import random, math, wave, struct, subprocess, os, time, threading, colorsys
from datetime import datetime
from flask import Flask, Response

# ============ CONFIG ============
BASE_DIR = os.path.expanduser("~/gameplay_slither")
FRAMES_DIR = os.path.join(BASE_DIR, "frames")
LOG_PATH = os.path.join(BASE_DIR, "log.txt")

W, H = 1920, 1080
HALF_W = W // 2
CELL = 30
COLS = HALF_W // CELL
ROWS = H // CELL
FPS = 20
DURATION_MIN = 10
FRAMES_PER_VIDEO = DURATION_MIN * 60 * FPS
N_VIDEOS = 5

DOT_BG = (55, 38, 95)
OUTLINE = (20, 15, 40)
FOOD_COLOR = (255, 40, 120)
FOOD_OUTLINE = (255, 255, 255)

THRESHOLDS = [0.90]

HUE_CYCLE_SECONDS = 20  # tiempo para completar una vuelta de color (transicion continua)
BG_REGEN_EVERY = 6      # cada cuantos frames se re-dibuja el fondo (perf)

# ============ SISTEMA DE 50 VARIANTES (golden angle, sin guardar estado) ============
N_VARIANTS = 50
GOLDEN = 0.6180339887498949  # conjugado áureo -> distribución de matices sin repetición en 50 pasos
PAIR_OFFSET = 25  # panel izquierdo y derecho siempre a mitad de rueda de distancia

def get_run_number():
    rn = os.environ.get("GITHUB_RUN_NUMBER")
    if rn is not None:
        return int(rn)
    # fallback si corre local/Termux sin GitHub Actions: varía cada hora
    return int(time.time()) // 3600

def variant_palette(vid, shift=0.0):
    hue = (vid * GOLDEN + shift) % 1.0
    def rgb(h, s, v):
        r, g, b = colorsys.hsv_to_rgb(h % 1.0, s, v)
        return (int(r*255), int(g*255), int(b*255))
    return {
        "bg":   rgb(hue, 0.55, 0.35),
        "body": rgb(hue + 0.50, 0.80, 0.95),
        "head": rgb(hue + 0.15, 0.85, 1.00),
    }

# ============ LOG ============
os.makedirs(BASE_DIR, exist_ok=True)
os.makedirs(FRAMES_DIR, exist_ok=True)

def log(msg):
    line = f"[{datetime.now().strftime('%H:%M:%S')}] {msg}"
    print(line)
    with open(LOG_PATH, "a", encoding="utf-8") as f:
        f.write(line + "\n")

STATE = {
    "status": "iniciando",
    "current_video": 0,
    "total_videos": N_VIDEOS,
    "progress": 0,
    "done": False,
    "error": None,
    "completed": [],  # lista de nombres de archivo ya listos
}

# ============ JUEGO ============
class Game:
    def __init__(self, seed, vid):
        self.rng = random.Random(seed)
        self.total_cells = COLS * ROWS
        self.threshold_idx = 0
        self.vid = vid
        self.palette = variant_palette(vid)
        self.last_color_period = 0
        self.eat_events = []
        self.reset()

    def reset(self):
        self.snake = [(COLS//2, ROWS//2)]
        self.direction = (1, 0)
        self.foods = [self.rand_cell() for _ in range(8)]
        self.bg_img = self._make_bg()

    def _make_bg(self):
        from PIL import Image, ImageDraw
        img = Image.new("RGB", (HALF_W, H), self.palette["bg"])
        draw = ImageDraw.Draw(img)
        for x in range(0, HALF_W, CELL):
            for y in range(0, H, CELL):
                draw.ellipse([x+CELL//2-1, y+CELL//2-1, x+CELL//2+1, y+CELL//2+1], fill=DOT_BG)
        return img

    def rand_cell(self, margin=1):
        return (self.rng.randint(margin, COLS-1-margin), self.rng.randint(margin, ROWS-1-margin))

    def nearest_food(self, head):
        return min(self.foods, key=lambda f: (f[0]-head[0])**2 + (f[1]-head[1])**2)

    def _free_space(self, start, body):
        from collections import deque
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

    def bot_move(self, head, mistake_chance=0.02):
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
        if self.rng.random() < mistake_chance and valid:
            return self.rng.choice(valid)
        if valid:
            min_space = len(self.snake) + 5
            safe = []
            for d in valid:
                nx, ny = head[0]+d[0], head[1]+d[1]
                if self._free_space((nx, ny), body_for_space) >= min_space:
                    safe.append(d)
            if safe:
                def score(d):
                    nx, ny = head[0]+d[0], head[1]+d[1]
                    return (nx-tx)**2 + (ny-ty)**2
                return min(safe, key=score)
            return max(valid, key=lambda d: self._free_space((head[0]+d[0], head[1]+d[1]), body_for_space))
        return self.direction

    def step(self, frame_idx):
        shift = (frame_idx % (FPS * HUE_CYCLE_SECONDS)) / (FPS * HUE_CYCLE_SECONDS)
        self.palette = variant_palette(self.vid, shift)
        if frame_idx % BG_REGEN_EVERY == 0:
            self.bg_img = self._make_bg()
        target_fill = THRESHOLDS[self.threshold_idx] * self.total_cells
        head = self.snake[-1]
        self.direction = self.bot_move(head)
        nx, ny = head[0]+self.direction[0], head[1]+self.direction[1]
        hit_wall = nx < 0 or nx >= COLS or ny < 0 or ny >= ROWS
        hit_self = (nx, ny) in self.snake[:-1]
        reached_threshold = len(self.snake) >= target_fill

        if hit_wall or hit_self or reached_threshold:
            self.threshold_idx = (self.threshold_idx + 1) % len(THRESHOLDS)
            self.reset()
            return

        new_head = (nx, ny)
        ate = new_head in self.foods
        self.snake.append(new_head)
        if ate:
            self.foods.remove(new_head)
            self.foods.append(self.rand_cell())
            self.eat_events.append(frame_idx)
        else:
            self.snake.pop(0)

    def render(self):
        from PIL import Image, ImageDraw
        img = self.bg_img.copy()
        draw = ImageDraw.Draw(img)
        pal = self.palette
        pad = 3
        for fx, fy in self.foods:
            x0, y0 = fx*CELL, fy*CELL
            draw.rectangle([x0+pad, y0+pad, x0+CELL-pad, y0+CELL-pad], fill=FOOD_COLOR, outline=FOOD_OUTLINE, width=2)
        n = len(self.snake)
        for i, (sx, sy) in enumerate(self.snake):
            x0, y0 = sx*CELL, sy*CELL
            is_head = (i == n-1)
            color = pal["head"] if is_head else pal["body"]
            draw.rectangle([x0+pad, y0+pad, x0+CELL-pad, y0+CELL-pad], fill=color, outline=OUTLINE, width=3)
            ix0, iy0 = x0+pad+4, y0+pad+4
            ix1, iy1 = x0+CELL//2, y0+CELL//2
            draw.rectangle([ix0, iy0, ix1, iy1], fill=tuple(min(255,c+40) for c in color))
        if n > 0:
            hx, hy = self.snake[-1]
            hx0, hy0 = hx*CELL, hy*CELL
            for ex, ey in [(hx0+CELL-9, hy0+8), (hx0+CELL-9, hy0+CELL-12)]:
                draw.rectangle([ex-4, ey-4, ex+4, ey+4], fill=(20,15,30))
                draw.rectangle([ex-2, ey-2, ex+2, ey+2], fill=(255,255,255))
        return img

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
def generar_un_video(video_num, left_vid, right_vid, run_number):
    from PIL import Image
    output_path = os.path.join(BASE_DIR, f"gameplay_final_run{run_number}_{video_num}.mp4")
    audio_path = os.path.join(BASE_DIR, f"audio_run{run_number}_{video_num}.wav")

    for fn in os.listdir(FRAMES_DIR):
        os.remove(os.path.join(FRAMES_DIR, fn))

    log(f"--- Video {video_num}/{N_VIDEOS} | variante izq={left_vid} der={right_vid} ---")
    game_left = Game(seed=random.randint(1,9999), vid=left_vid)
    game_right = Game(seed=random.randint(1,9999), vid=right_vid)

    for i in range(FRAMES_PER_VIDEO):
        game_left.step(i)
        game_right.step(i)
        frame = Image.new("RGB", (W, H))
        frame.paste(game_left.render(), (0, 0))
        frame.paste(game_right.render(), (HALF_W, 0))
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
        "-c:v", "libx264", "-crf", "27", "-preset", "medium",
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

# ============ PIPELINE COMPLETO ============
def generar_todo():
    try:
        run_number = get_run_number()
        base_idx = (run_number - 1) * N_VIDEOS
        log(f"=== Run #{run_number} | {N_VIDEOS} videos de {DURATION_MIN} min ===")

        for v in range(1, N_VIDEOS + 1):
            STATE["current_video"] = v
            STATE["status"] = f"video {v}: generando frames"
            global_idx = (base_idx + (v - 1)) % N_VARIANTS
            left_vid = global_idx
            right_vid = (global_idx + PAIR_OFFSET) % N_VARIANTS
            generar_un_video(v, left_vid, right_vid, run_number)

        STATE["progress"] = 100
        STATE["status"] = "completo"
        STATE["done"] = True
        log("=== Proceso completo: 5 videos listos ===")

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
    <html><head><meta charset="utf-8"><title>Gameplay Slither v1.7</title></head>
    <body style="font-family:sans-serif; background:#111; color:#eee; padding:20px;">
    <h2>🐍 Generador de Gameplay (Slither grid) — v1.7</h2>
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
        # Modo headless para GitHub Actions: solo genera, sin levantar servidor web
        log("Modo GitHub Actions: generando sin interfaz web...")
        generar_todo()
    else:
        log("Servidor iniciado. Generación automática arrancando...")
        threading.Thread(target=generar_todo, daemon=True).start()
        app.run(host="0.0.0.0", port=8080)
