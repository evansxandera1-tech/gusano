import random, math, wave, struct, subprocess, os, time, threading
from datetime import datetime
from collections import deque
from flask import Flask, Response

# ============ CONFIG ============
BASE_DIR = os.path.expanduser("~/gameplay_slither")
FRAMES_DIR = os.path.join(BASE_DIR, "frames")
LOG_PATH = os.path.join(BASE_DIR, "log.txt")

W, H = 1600, 900
HALF_W = W // 2
CELL = 30
COLS = HALF_W // CELL
ROWS = H // CELL

FPS = 60                        # fps de render/video (movimiento fluido)
LOGIC_FPS = 5                   # celdas por segundo que avanza el gusano (velocidad real de juego)
STEP_EVERY = FPS // LOGIC_FPS   # cada cuantos frames de render se avanza 1 celda de grilla

DURATION_MIN = 10
FRAMES_PER_VIDEO = DURATION_MIN * 60 * FPS
N_VIDEOS = 5

OUTLINE = (20, 15, 40)
FOOD_COLOR = (255, 40, 120)
FOOD_OUTLINE = (255, 255, 255)
CORNER_RADIUS = 4                # esquina minima: sigue siendo cuadradito, no bolita
FLASH_FRAMES = 18                # destello al comer (~0.3s a 60fps)
TRAIL_LEN = 4                    # cuadraditos fantasma detras de la cola (estela)

BORDER = 26                      # grosor del marco de ladrillos
BRICK_ROW = 13
MORTAR = (20, 12, 8)
VS_COLOR_A = (255, 106, 0)
VS_COLOR_B = (255, 207, 61)
VS_OUTLINE = (0, 229, 255)
BALL_RADIUS = 9

# ============ PALETAS CURADAS (10, fijas por video, sin repetir hasta agotar el pool) ============
PALETTES = [
    dict(bg=(18,24,38),  dot_bg=(28,36,54),  head=(64,196,255),  tail=(20,50,90)),
    dict(bg=(30,18,40),  dot_bg=(44,26,58),  head=(255,99,190),  tail=(90,30,70)),
    dict(bg=(14,30,22),  dot_bg=(22,44,32),  head=(110,255,140), tail=(30,90,45)),
    dict(bg=(38,20,14),  dot_bg=(54,30,20),  head=(255,140,60),  tail=(110,55,20)),
    dict(bg=(16,16,40),  dot_bg=(26,26,58),  head=(140,120,255), tail=(50,40,110)),
    dict(bg=(22,19,7),   dot_bg=(34,30,11),  head=(255,224,80),  tail=(150,130,30)),
    dict(bg=(10,32,32),  dot_bg=(18,46,46),  head=(60,255,220),  tail=(20,110,95)),
    dict(bg=(34,12,24),  dot_bg=(48,20,34),  head=(255,70,100),  tail=(110,25,45)),
    dict(bg=(20,20,20),  dot_bg=(32,32,32),  head=(255,255,255), tail=(90,90,90)),
    dict(bg=(12,26,40),  dot_bg=(20,38,56),  head=(255,170,60),  tail=(110,70,25)),
]
N_VARIANTS = len(PALETTES)
PAIR_OFFSET = N_VARIANTS // 2    # izquierda y derecha siempre a mitad de pool de distancia
WALL_OFFSET = 2                  # el marco de ladrillos usa una paleta distinta a ambos paneles

def get_run_number():
    rn = os.environ.get("GITHUB_RUN_NUMBER")
    if rn is not None:
        return int(rn)
    return int(time.time()) // 3600

def lerp_color(a, b, t):
    return tuple(int(a[i] + (b[i] - a[i]) * t) for i in range(3))

def mul_color(c, f):
    return tuple(max(0, min(255, int(ch * f))) for ch in c)

# ============ LOG ============
os.makedirs(BASE_DIR, exist_ok=True)
os.makedirs(FRAMES_DIR, exist_ok=True)

def log(msg):
    line = f"[{datetime.now().strftime('%H:%M:%S')}] {msg}"
    print(line, flush=True)
    with open(LOG_PATH, "a", encoding="utf-8") as f:
        f.write(line + "\n")

STATE = {
    "status": "iniciando",
    "current_video": 0,
    "total_videos": N_VIDEOS,
    "progress": 0,
    "done": False,
    "error": None,
    "completed": [],
}

# ============ FUENTE ============
def _load_font(size):
    from PIL import ImageFont
    candidates = [
        "/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf",
        "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf",
    ]
    for c in candidates:
        if os.path.exists(c):
            return ImageFont.truetype(c, size)
    return ImageFont.load_default()

# ============ JUEGO ============
class Game:
    def __init__(self, seed, vid):
        self.rng = random.Random(seed)
        self.total_cells = COLS * ROWS
        self.vid = vid
        self.palette = PALETTES[vid % N_VARIANTS]
        self.eat_events = []
        self.eat_flashes = []   # [(pos, frame_idx), ...]
        self.trail = deque(maxlen=TRAIL_LEN)
        self.birth_frame = 0
        self.reset(0)

    def reset(self, frame_idx=0):
        self.snake = [(COLS // 2, ROWS // 2)]
        self.prev_snake = list(self.snake)
        self.direction = (1, 0)
        self.foods = [self.rand_cell() for _ in range(8)]
        self.bg_img = self._make_bg()
        self.trail.clear()
        self.birth_frame = frame_idx

    def _make_bg(self):
        from PIL import Image, ImageDraw
        img = Image.new("RGB", (HALF_W, H), self.palette["bg"])
        draw = ImageDraw.Draw(img)
        for x in range(0, HALF_W, CELL):
            for y in range(0, H, CELL):
                draw.ellipse([x+CELL//2-1, y+CELL//2-1, x+CELL//2+1, y+CELL//2+1], fill=self.palette["dot_bg"])
        return img

    def rand_cell(self, margin=1):
        return (self.rng.randint(margin, COLS-1-margin), self.rng.randint(margin, ROWS-1-margin))

    def nearest_food(self, head):
        return min(self.foods, key=lambda f: (f[0]-head[0])**2 + (f[1]-head[1])**2)

    def _free_space(self, start, body):
        visited = {start}
        q = deque([start])
        while q:
            x, y = q.popleft()
            for dx, dy in ((1,0),(-1,0),(0,1),(0,-1)):
                nx, ny = x+dx, y+dy
                if 0 <= nx < COLS and 0 <= ny < ROWS and (nx, ny) not in body and (nx, ny) not in visited:
                    visited.add((nx, ny))
                    q.append((nx, ny))
        return len(visited)

    def bot_move(self, head):
        # regla universal: sobrevivir primero (maximo espacio libre), comer es solo el desempate
        body = set(self.snake[:-1])
        tail_free = set(self.snake[:1]) - {head}
        body_for_space = body - tail_free
        tx, ty = self.nearest_food(head)
        DIRS = [(1,0),(-1,0),(0,1),(0,-1)]
        valid = []
        for dx, dy in DIRS:
            nx, ny = head[0]+dx, head[1]+dy
            if 0 <= nx < COLS and 0 <= ny < ROWS and (nx, ny) not in body:
                valid.append((dx, dy))
        if not valid:
            return self.direction
        scored = []
        for d in valid:
            nx, ny = head[0]+d[0], head[1]+d[1]
            space = self._free_space((nx, ny), body_for_space)
            dist_food = (nx-tx)**2 + (ny-ty)**2
            scored.append((space, -dist_food, d))
        scored.sort(key=lambda s: (s[0], s[1]), reverse=True)
        return scored[0][2]

    def step(self, frame_idx):
        if frame_idx % STEP_EVERY != 0:
            return
        old_snake = list(self.snake)
        head = old_snake[-1]
        self.direction = self.bot_move(head)
        nx, ny = head[0]+self.direction[0], head[1]+self.direction[1]
        hit_wall = nx < 0 or nx >= COLS or ny < 0 or ny >= ROWS
        hit_self = (nx, ny) in old_snake[:-1]

        if hit_wall or hit_self:
            # unica forma de terminar la partida: choque real (callejon sin salida).
            # no hay tope artificial de % de tablero.
            self.reset(frame_idx)
            return

        new_head = (nx, ny)
        ate = new_head in self.foods
        if ate:
            self.snake = old_snake + [new_head]
            self.prev_snake = old_snake + [old_snake[-1]]
            self.foods.remove(new_head)
            self.foods.append(self.rand_cell())
            self.eat_events.append(frame_idx)
            self.eat_flashes.append((new_head, frame_idx))
        else:
            self.snake = old_snake[1:] + [new_head]
            self.prev_snake = old_snake
            self.trail.append(old_snake[0])

    def render(self, frame_idx):
        from PIL import Image, ImageDraw
        base = self.bg_img.convert("RGBA")
        overlay = Image.new("RGBA", (HALF_W, H), (0, 0, 0, 0))
        odraw = ImageDraw.Draw(overlay)
        draw = ImageDraw.Draw(base)
        pal = self.palette
        pad = 3
        sub_t = (frame_idx % STEP_EVERY) / STEP_EVERY

        for fx, fy in self.foods:
            x0, y0 = fx*CELL, fy*CELL
            draw.rectangle([x0+pad, y0+pad, x0+CELL-pad, y0+CELL-pad], fill=FOOD_COLOR, outline=FOOD_OUTLINE, width=2)

        for i, (tx, ty) in enumerate(self.trail):
            age = len(self.trail) - i
            alpha = max(0, int(90 * (1 - age / (TRAIL_LEN + 1))))
            if alpha <= 0:
                continue
            x0, y0 = tx*CELL, ty*CELL
            odraw.rounded_rectangle([x0+pad, y0+pad, x0+CELL-pad, y0+CELL-pad], radius=CORNER_RADIUS,
                                     fill=pal["head"] + (alpha,))

        n = len(self.snake)
        prev = self.prev_snake if len(self.prev_snake) == n else self.snake
        for i in range(n):
            cx = prev[i][0] + (self.snake[i][0]-prev[i][0]) * sub_t
            cy = prev[i][1] + (self.snake[i][1]-prev[i][1]) * sub_t
            x0, y0 = cx*CELL, cy*CELL
            t = i / max(1, n-1)
            color = lerp_color(pal["tail"], pal["head"], t)
            odraw.rounded_rectangle([x0+pad+3, y0+pad+4, x0+CELL-pad+3, y0+CELL-pad+4],
                                     radius=CORNER_RADIUS, fill=(0, 0, 0, 90))
            draw.rounded_rectangle([x0+pad, y0+pad, x0+CELL-pad, y0+CELL-pad],
                                    radius=CORNER_RADIUS, fill=color, outline=OUTLINE, width=3)
            if i == n-1:
                dx, dy = self.direction
                ex0 = x0 + CELL/2 + dx*6 - dy*7
                ey0 = y0 + CELL/2 + dy*6 - dx*7
                ex1 = x0 + CELL/2 + dx*6 + dy*7
                ey1 = y0 + CELL/2 + dy*6 + dx*7
                for ex, ey in [(ex0, ey0), (ex1, ey1)]:
                    draw.ellipse([ex-4, ey-4, ex+4, ey+4], fill=(255, 255, 255))
                    draw.ellipse([ex-2+dx*1.5, ey-2+dy*1.5, ex+2+dx*1.5, ey+2+dy*1.5], fill=(20, 15, 30))

        for pos, ef in self.eat_flashes:
            elapsed = frame_idx - ef
            if 0 <= elapsed < FLASH_FRAMES:
                p = elapsed / FLASH_FRAMES
                fx, fy = pos
                cx, cy = fx*CELL+CELL/2, fy*CELL+CELL/2
                r = 8 + p*26
                alpha = int(255*(1-p))
                odraw.ellipse([cx-r, cy-r, cx+r, cy+r], outline=(255, 255, 255, alpha), width=3)
        self.eat_flashes = [(pos, ef) for pos, ef in self.eat_flashes if frame_idx - ef < FLASH_FRAMES]

        return Image.alpha_composite(base, overlay).convert("RGB")


# ============ MARCO DE LADRILLOS (brilla/parpadea, color de la paleta del video) ============
def _brick_strip(draw, x, y, w, h, horizontal, brick_a, brick_b, frame_idx, phase_base):
    draw.rectangle([x, y, x+w, y+h], fill=MORTAR)
    row = BRICK_ROW
    i = 0
    if horizontal:
        bx = 0
        while bx < w:
            base = brick_a if i % 2 == 0 else brick_b
            f = 0.72 + 0.28 * math.sin(frame_idx/9 + phase_base + i*0.6)
            x1 = x + min(bx+row, w) - 2
            if x1 > x+bx+1:
                draw.rectangle([x+bx+1, y+1, x1, y+h-2], fill=mul_color(base, f))
            bx += row; i += 1
    else:
        by = 0
        while by < h:
            base = brick_a if i % 2 == 0 else brick_b
            f = 0.72 + 0.28 * math.sin(frame_idx/9 + phase_base + i*0.6)
            y1 = y + min(by+row, h) - 2
            if y1 > y+by+1:
                draw.rectangle([x+1, y+by+1, x+w-2, y1], fill=mul_color(base, f))
            by += row; i += 1

def draw_frame_border(draw, wall_idx, frame_idx):
    wp = PALETTES[wall_idx % N_VARIANTS]
    brick_a, brick_b = wp["head"], wp["tail"]
    _brick_strip(draw, 0, 0, W, BORDER, True, brick_a, brick_b, frame_idx, 0)
    _brick_strip(draw, 0, H-BORDER, W, BORDER, True, brick_a, brick_b, frame_idx, 2)
    _brick_strip(draw, 0, 0, BORDER, H, False, brick_a, brick_b, frame_idx, 4)
    _brick_strip(draw, W-BORDER, 0, BORDER, H, False, brick_a, brick_b, frame_idx, 6)
    _brick_strip(draw, HALF_W-BORDER//2, 0, BORDER, H, False, brick_a, brick_b, frame_idx, 8)


# ============ PELOTA QUE RECORRE SOLO EL MARCO ============
class BorderBall:
    def __init__(self, seed):
        self.rng = random.Random(seed)
        half = BORDER // 2
        self.track = [(half, half), (W-half, half), (W-half, H-half), (half, H-half), (half, half)]
        self.lens = [0]
        for i in range(1, len(self.track)):
            x0, y0 = self.track[i-1]; x1, y1 = self.track[i]
            self.lens.append(self.lens[-1] + math.hypot(x1-x0, y1-y0))
        self.total = self.lens[-1]
        self.dist = 0.0
        self.vel = 3.0
        self.next_change = 0

    def _pos(self, d):
        d = d % self.total
        for i in range(1, len(self.track)):
            if d <= self.lens[i]:
                seg = self.lens[i] - self.lens[i-1]
                tt = (d - self.lens[i-1]) / seg if seg > 0 else 0
                x0, y0 = self.track[i-1]; x1, y1 = self.track[i]
                return x0 + (x1-x0)*tt, y0 + (y1-y0)*tt
        return self.track[-1]

    def step_and_pos(self, frame_idx):
        if frame_idx > self.next_change:
            sign = 1 if self.rng.random() < 0.5 else -1
            self.vel = sign * (2.0 + self.rng.random()*3.0)
            self.next_change = frame_idx + self.rng.randint(70, 140)
        self.dist += self.vel
        return self._pos(self.dist)

def draw_ball(draw, pos):
    x, y = pos
    draw.ellipse([x-BALL_RADIUS, y-BALL_RADIUS, x+BALL_RADIUS, y+BALL_RADIUS], fill=(255, 255, 255))
    draw.arc([x-BALL_RADIUS+2, y-BALL_RADIUS+2, x+BALL_RADIUS-2, y+BALL_RADIUS-2], 20, 110, fill=(230, 168, 0), width=2)


# ============ VS + ESPIRAL SUTIL EN EL CENTRO ============
def draw_vs_and_spiral(draw, frame_idx, font_vs):
    cx, cy = W // 2, H // 2
    for i in range(70):
        ang = i * 2.4 + (frame_idx / 300.0) * 6.283
        rad = 6 + i * 5.2
        if rad > 260:
            continue
        x = cx + math.cos(ang) * rad
        y = cy + math.sin(ang) * rad * 0.6
        col = VS_COLOR_A if i % 2 == 0 else VS_OUTLINE
        a = 0.10 * (1 - rad/260)
        if a <= 0:
            continue
        draw.ellipse([x-3, y-3, x+3, y+3], fill=mul_color(col, 1))

    t = 0.5 + 0.5*math.sin(frame_idx/23.0)
    vs_color = lerp_color(VS_COLOR_A, VS_COLOR_B, t)
    draw.text((cx, cy), "VS", font=font_vs, fill=vs_color, stroke_width=5, stroke_fill=VS_OUTLINE, anchor="mm")


# ============ HUD (contador + barra + tiempo, compacto) ============
def draw_hud(draw, x0, y0, w, game, frame_idx, accent, font_big, font_small):
    count = len(game.snake)
    draw.text((x0, y0), str(count), font=font_big, fill=(255, 255, 255))
    elapsed_s = (frame_idx - game.birth_frame) / FPS
    mm, ss = int(elapsed_s // 60), int(elapsed_s % 60)
    timer_txt = f"{mm:02d}:{ss:02d}"
    pct = min(1.0, count / game.total_cells)
    bar_y = y0 + 26
    bar_w = w - 60
    draw.rectangle([x0, bar_y, x0+bar_w, bar_y+3], fill=(255, 255, 255))
    draw.rectangle([x0, bar_y, x0+int(bar_w*pct), bar_y+3], fill=accent)
    draw.text((x0+bar_w+8, bar_y-5), timer_txt, font=font_small, fill=(230, 230, 230))


# ============ SONIDO ============
def synth_beep(path, freq=880, duration=0.08, volume=0.35, samplerate=44100):
    n_samples = int(duration * samplerate)
    with wave.open(path, "w") as f:
        f.setnchannels(1); f.setsampwidth(2); f.setframerate(samplerate)
        for i in range(n_samples):
            t = i / samplerate
            fade = 1.0 - (i / n_samples)
            sample = volume * fade * math.sin(2 * math.pi * freq * t)
            f.writeframes(struct.pack("<h", int(sample * 32767)))

def build_audio_track(eat_events_all, total_frames, fps, out_wav):
    samplerate = 44100
    duration = total_frames / fps
    n_samples = int(duration * samplerate)
    track = [0] * n_samples
    beep_path = os.path.join(BASE_DIR, "_beep.wav")
    synth_beep(beep_path)
    with wave.open(beep_path, "r") as bf:
        beep_samples = bf.readframes(bf.getnframes())
        beep_vals = struct.unpack("<%dh" % (len(beep_samples)//2), beep_samples)
    for frame_idx in eat_events_all:
        start_sample = int((frame_idx / fps) * samplerate)
        for i, v in enumerate(beep_vals):
            pos = start_sample + i
            if pos < n_samples:
                track[pos] = max(-32768, min(32767, track[pos] + v))
    with wave.open(out_wav, "w") as f:
        f.setnchannels(1); f.setsampwidth(2); f.setframerate(samplerate)
        f.writeframes(b"".join(struct.pack("<h", v) for v in track))
    os.remove(beep_path)


# ============ PIPELINE: 1 video ============
def generar_un_video(video_num, left_vid, right_vid, wall_idx, run_number):
    from PIL import Image, ImageDraw

    output_path = os.path.join(BASE_DIR, f"gameplay_final_run{run_number}_{video_num}.mp4")
    audio_path = os.path.join(BASE_DIR, f"audio_run{run_number}_{video_num}.wav")
    for fn in os.listdir(FRAMES_DIR):
        os.remove(os.path.join(FRAMES_DIR, fn))

    log(f"--- Video {video_num}/{N_VIDEOS} | variante izq={left_vid} der={right_vid} marco={wall_idx} ---")

    game_left = Game(seed=random.randint(1, 9999), vid=left_vid)
    game_right = Game(seed=random.randint(1, 9999), vid=right_vid)
    ball = BorderBall(seed=random.randint(1, 9999))
    font_vs = _load_font(120)
    font_big = _load_font(28)
    font_small = _load_font(20)

    for i in range(FRAMES_PER_VIDEO):
        game_left.step(i)
        game_right.step(i)

        frame = Image.new("RGB", (W, H))
        frame.paste(game_left.render(i), (0, 0))
        frame.paste(game_right.render(i), (HALF_W, 0))

        draw = ImageDraw.Draw(frame)
        draw_frame_border(draw, wall_idx, i)
        draw_vs_and_spiral(draw, i, font_vs)
        draw_ball(draw, ball.step_and_pos(i))
        draw_hud(draw, BORDER+10, BORDER+8, HALF_W-BORDER*2-10, game_left, i, game_left.palette["head"], font_big, font_small)
        draw_hud(draw, HALF_W+BORDER+10, BORDER+8, HALF_W-BORDER*2-10, game_right, i, game_right.palette["head"], font_big, font_small)

        frame.save(os.path.join(FRAMES_DIR, f"frame_{i:05d}.png"))

        if i % 200 == 0:
            video_pct = i / FRAMES_PER_VIDEO
            STATE["progress"] = int(video_pct * 70)
            log(f"video {video_num}: frame {i}/{FRAMES_PER_VIDEO}")

    STATE["status"] = f"video {video_num}: generando audio"
    STATE["progress"] = 72
    all_eats = sorted(game_left.eat_events + game_right.eat_events)
    build_audio_track(all_eats, FRAMES_PER_VIDEO, FPS, audio_path)
    log(f"Audio listo ({len(all_eats)} sonidos).")

    STATE["status"] = f"video {video_num}: codificando (ffmpeg)"
    STATE["progress"] = 80
    cmd = [
        "ffmpeg", "-y",
        "-framerate", str(FPS),
        "-i", os.path.join(FRAMES_DIR, "frame_%05d.png"),
        "-i", audio_path,
        "-c:v", "libx264", "-crf", "29", "-preset", "slow",
        "-pix_fmt", "yuv420p",
        "-c:a", "aac", "-shortest",
        output_path
    ]
    result = subprocess.run(cmd, capture_output=True, text=True)
    if result.returncode != 0:
        raise RuntimeError(result.stderr[-2000:])

    os.remove(audio_path)
    for fn in os.listdir(FRAMES_DIR):
        os.remove(os.path.join(FRAMES_DIR, fn))

    log(f"Video {video_num} listo: {output_path}")
    video_size = os.path.getsize(output_path)

    try:
        subprocess.run(
            ["rclone", "copy", output_path, "gdrive:gameplay_slither", "--no-traverse"],
            check=True, capture_output=True, text=True
        )
        log(f"Video {video_num} subido a Drive")
        os.remove(output_path)
        log(f"Video {video_num} borrado localmente tras subir")
    except Exception as e:
        log(f"ERROR subiendo video {video_num} a Drive: {e}")

    STATE["completed"].append(f"gameplay_final_run{run_number}_{video_num}.mp4")
    return video_size


# ============ PIPELINE COMPLETO ============
def generar_todo():
    try:
        run_number = get_run_number()
        base_idx = (run_number - 1) * N_VIDEOS
        log(f"=== Run #{run_number} | {N_VIDEOS} videos de {DURATION_MIN} min ===")

        TARGET_BYTES = 2 * 1024**3
        v = 1
        total_bytes = 0
        while total_bytes < TARGET_BYTES:
            STATE["current_video"] = v
            STATE["status"] = f"video {v}: generando frames"
            global_idx = (base_idx + (v - 1)) % N_VARIANTS
            left_vid = global_idx
            right_vid = (global_idx + PAIR_OFFSET) % N_VARIANTS
            wall_idx = (global_idx + WALL_OFFSET) % N_VARIANTS

            video_size = generar_un_video(v, left_vid, right_vid, wall_idx, run_number)
            total_bytes += video_size
            log(f"Progreso tanda: {total_bytes/1024/1024:.0f} MB / 2048 MB")
            v += 1

        STATE["progress"] = 100
        STATE["status"] = "completo"
        STATE["done"] = True
        log("=== Proceso completo ===")
    except Exception as e:
        STATE["error"] = str(e)
        STATE["status"] = "error"
        log(f"ERROR: {e}")


# ============ INTERFAZ WEB ============
app = Flask(__name__)

@app.route("/")
def home():
    with open(LOG_PATH, encoding="utf-8") as f:
        log_lines = f.readlines()[-40:]
    log_html = "<br>".join(l.strip() for l in reversed(log_lines))
    links_html = "".join(
        f'<p><a href="/descargar/{n}" style="font-size:18px;">⬇️ Descargar video {n}</a></p>'
        for n in STATE["completed"]
    )
    return f"""
    <html><head><meta charset="utf-8"><title>Gameplay Slither v2.2</title></head>
    <body style="font-family:sans-serif; background:#111; color:#eee; padding:20px;">
    <h2>🐍 Generador de Gameplay (Slither grid) — v2.2</h2>
    <p><b>Estado:</b> {STATE['status']} — video {STATE['current_video']}/{STATE['total_videos']} — {STATE['progress']}%</p>
    {links_html}
    <h3>Log</h3>
    <div style="background:#000; padding:10px; border-radius:6px; max-height:400px; overflow-y:auto;">
    {log_html}
    </div>
    <script>setTimeout(()=>location.reload(), 4000);</script>
    </body></html>
    """

@app.route("/descargar/<nombre>")
def descargar(nombre):
    path = os.path.join(BASE_DIR, nombre)
    if not os.path.exists(path):
        return "Todavía no está listo.", 404
    with open(path, "rb") as f:
        data = f.read()
    return Response(data, mimetype="video/mp4",
                     headers={"Content-Disposition": f"attachment; filename={nombre}"})


if __name__ == "__main__":
    if os.environ.get("RUN_MODE") == "github":
        log("Modo GitHub Actions: generando sin interfaz web...")
        generar_todo()
    else:
        log("Servidor iniciado. Generación automática arrancando...")
        def generar_en_loop():
            while True:
                generar_todo()
                log("Esperando 3 horas para la proxima tanda...")
                time.sleep(3 * 60 * 60)
        threading.Thread(target=generar_en_loop, daemon=True).start()
        app.run(host="0.0.0.0", port=8080)
