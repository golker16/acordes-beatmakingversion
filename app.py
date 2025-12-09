import os, sys, threading, logging, traceback, random, re, subprocess
from pathlib import Path
from dataclasses import dataclass
from typing import List, Dict, Tuple, Optional
from datetime import datetime

import yaml
from mido import Message, MidiFile, MidiTrack, MetaMessage, bpm2tempo

# --- asegurar backend rtmidi en el ejecutable (PyInstaller hidden import) ---
try:
    import mido  # noqa: F401
    import mido.backends.rtmidi  # noqa: F401
except Exception:
    pass

from PySide6 import QtCore, QtWidgets
from PySide6.QtWidgets import (
    QApplication, QMainWindow, QWidget, QVBoxLayout, QHBoxLayout,
    QLabel, QPushButton, QComboBox, QProgressBar, QPlainTextEdit, QFileDialog,
    QGroupBox, QGridLayout, QTabWidget, QSpinBox
)
import qdarkstyle


# =========================
# Config general
# =========================
APP_NAME = "MelodiaLoop"
PPQ = 480
BPM_DEFAULT = 110
NOTE_VELOCITY = 90
LOOP_BARS = 4  # 4 compases, 1 acorde por compás

# ---------------- Rutas robustas para PyInstaller ----------------
def resource_base() -> Path:
    if hasattr(sys, "_MEIPASS"):
        return Path(sys._MEIPASS)
    if getattr(sys, "frozen", False):
        return Path(sys.executable).parent
    return Path(__file__).parent

def resource_path(rel: str) -> Path:
    return resource_base() / rel

GROOVES_DIR = resource_path("grooves")
OUTPUT_DIR = Path("output"); OUTPUT_DIR.mkdir(exist_ok=True)
PREVIEW_DIR = OUTPUT_DIR / "previews"; PREVIEW_DIR.mkdir(parents=True, exist_ok=True)

# ---------------- Logging ----------------
logger = logging.getLogger(APP_NAME)
logger.setLevel(logging.INFO)
fh = logging.FileHandler(OUTPUT_DIR / "app.log", encoding="utf-8")
fh.setFormatter(logging.Formatter("%(asctime)s [%(levelname)s] %(message)s"))
logger.addHandler(fh)


# =========================
# Armónica / simbología
# =========================
class RomanError(Exception):
    pass

ROMAN_TO_DEG = {
    "I":1, "II":2, "III":3, "IV":4, "V":5, "VI":6, "VII":7,
    "i":1, "ii":2, "iii":3, "iv":4, "v":5, "vi":6, "vii":7,
}

NOTE_PC = {"C":0,"C#":1,"D":2,"D#":3,"E":4,"F":5,"F#":6,"G":7,"G#":8,"A":9,"A#":10,"B":11}
MAJOR_PCS     = [0,2,4,5,7,9,11]
NATMIN_PCS    = [0,2,3,5,7,8,10]
HARMONIC_PCS  = [0,2,3,5,7,8,11]

SNAP_POLICY = "strict"

REST_SET = {"—", "-", "NC"}
def is_rest_symbol(s: str) -> bool:
    return s.strip() in REST_SET

def allowed_scale_pcs(tonic: str, mode: str) -> set:
    tonic_pc = NOTE_PC[tonic]
    mode = mode.lower()
    if mode in ("major", "ionian", "mayor"):
        pcs = MAJOR_PCS
    elif mode in ("minor_harmonic", "harmonic_minor"):
        pcs = HARMONIC_PCS
    else:
        pcs = NATMIN_PCS
    return {(tonic_pc + x) % 12 for x in pcs}

def snap_note_to_pcs_same_octave(midi_note: int, allowed_pcs: set) -> int:
    base_oct = midi_note // 12
    pc = midi_note % 12
    if pc in allowed_pcs:
        return midi_note
    for d in range(1, 6):
        up = pc + d
        down = pc - d
        if 0 <= up <= 11 and up in allowed_pcs:
            return base_oct * 12 + up
        if 0 <= down <= 11 and down in allowed_pcs:
            return base_oct * 12 + down
    return midi_note

def snap_list_to_pcs(notes: List[int], allowed_pcs: set):
    snapped, changed = [], 0
    for n in notes:
        base_oct = n // 12; pc = n % 12
        if pc in allowed_pcs:
            snapped.append(n); continue
        best = None
        for d in range(1, 6):
            up = pc + d; dn = pc - d
            if 0 <= up <= 11 and up in allowed_pcs:
                best = base_oct*12 + up; break
            if 0 <= dn <= 11 and dn in allowed_pcs:
                best = base_oct*12 + dn; break
        if best is None:
            best = n
        if best != n:
            changed += 1
        snapped.append(best)
    return snapped, changed

def tonic_midi(tonic: str, octave: int) -> int:
    return NOTE_PC[tonic] + 12 * (octave + 1)

def degree_root_midi(tonic: str, mode: str, roman_core: str, accidental: str, octave: int) -> int:
    if roman_core not in ROMAN_TO_DEG:
        raise RomanError(f"Grado romano desconocido: {roman_core}")
    deg = ROMAN_TO_DEG[roman_core] - 1
    mode = mode.lower()
    if mode in ("major", "ionian", "mayor"):
        pcs = MAJOR_PCS
    elif mode in ("minor_harmonic", "harmonic_minor"):
        pcs = HARMONIC_PCS
    else:
        pcs = NATMIN_PCS
    base = tonic_midi(tonic, octave)
    pitch = base + pcs[deg]
    if accidental == "b":
        pitch -= 1
    elif accidental == "#":
        pitch += 1
    return pitch

def chord_intervals(roman_core: str, quality: Optional[str]) -> List[int]:
    is_upper = roman_core[0].isupper()
    triad = [0,4,7] if is_upper else [0,3,7]
    seventh = 11 if is_upper else 10
    if not quality:
        return triad
    q = quality.lower()
    if q in ["maj","maj7","maj9"]:
        return triad + [11]
    if q in ["7","13","9","11"]:
        return [0,4,7,10]
    if q in ["m","min","m7"]:
        return [0,3,7,10]
    if q in ["m6","min6"]:
        return [0,3,7,9]
    if q in ["dim","°","dim7"]:
        return [0,3,6]
    if q in ["ø7","m7b5","halfdim"]:
        return [0,3,6,10]
    return triad + [seventh]

def parse_symbol(symbol: str) -> Dict:
    s = symbol.strip()
    if is_rest_symbol(s):
        return {"rest": True}
    bass_inv = None
    if "/" in s:
        s, after = s.split("/", 1)
        bass_inv = after.strip()

    accidental = ""
    if s.startswith(("b","#")):
        accidental, s = s[0], s[1:]

    core, suffix = "", ""
    for ch in s:
        if ch in "IViv":
            core += ch
        else:
            suffix += ch

    if not core or core not in ROMAN_TO_DEG:
        raise RomanError(f"Simbología no soportada: {symbol}")

    quality = suffix if suffix else None
    return {"rest": False, "accidental": accidental, "core": core, "quality": quality, "bass_inv": bass_inv}

def build_symbol(accidental: str, core: str, quality: Optional[str], bass_inv: Optional[str]) -> str:
    s = ""
    if accidental:
        s += accidental
    s += core
    if quality:
        s += quality
    if bass_inv:
        s += f"/{bass_inv}"
    return s

def normalize_symbol_for_mode(symbol: str, mode: str) -> Tuple[str, bool, str]:
    """
    Traducciones suaves para evitar cosas "raras" según modo.
    """
    try:
        tok = parse_symbol(symbol)
        if tok.get("rest"):
            return symbol, False, ""

        acc, core, q, inv = tok["accidental"], tok["core"], tok["quality"], tok["bass_inv"]
        changed = False
        detail = ""
        m = mode.lower()

        if m in ("major", "ionian", "mayor"):
            if acc == "" and core == "v":
                core = "V"
                if q and q.lower() == "m7":
                    q = "7"
                changed, detail = True, "v→V"
            if acc == "" and core in ("VII", "vii"):
                core = "vii"
                if not q or q.lower() not in ("°", "dim", "dim7", "ø7"):
                    q = "°"
                changed, detail = True, "VII/vii→vii°"
        elif m in ("minor_natural", "aeolian"):
            if acc == "" and core == "V":
                core = "v"
                if q and q.lower() == "7":
                    q = "m7"
                changed, detail = True, "V→v"
            if acc == "" and core in ("vii",):
                if q and q.lower() in ("°", "dim", "dim7", "ø7"):
                    q = None
                core = "VII"
                changed, detail = True, "vii°→VII"
        else:  # minor_harmonic
            if acc == "" and core == "v":
                core = "V"
                if q and q.lower() == "m7":
                    q = "7"
                changed, detail = True, "v→V"
            if acc == "" and core in ("VII", "vii"):
                core = "vii"
                if not q or q.lower() not in ("°", "dim", "dim7", "ø7"):
                    q = "°"
                changed, detail = True, "VII/vii→vii°"

        new_symbol = build_symbol(acc, core, q, inv)
        return new_symbol, changed, detail
    except Exception:
        return symbol, False, ""


# =========================
# MIDI helpers
# =========================
@dataclass
class MidiEvent:
    t: int
    kind: str   # 'on'/'off'
    note: int
    vel: int
    channel: int = 0

def write_track(events: List[MidiEvent]) -> MidiTrack:
    events = sorted(events, key=lambda e: (e.t, 0 if e.kind == "on" else 1))
    tr = MidiTrack()
    last_t = 0
    for ev in events:
        delta = ev.t - last_t
        if ev.kind == "on":
            tr.append(Message("note_on", note=int(ev.note), velocity=int(ev.vel), channel=int(ev.channel), time=delta))
        else:
            tr.append(Message("note_off", note=int(ev.note), velocity=0, channel=int(ev.channel), time=delta))
        last_t = ev.t
    return tr


# =========================
# GROOVE: lectura y proyección
# =========================
@dataclass
class GrooveNote:
    bar: int           # 1..8
    phi_on: float      # 0..1
    phi_off: float     # 0..1
    pitch: int
    vel: int

def track_to_abs_events(track) -> List[Tuple[int, object]]:
    t = 0
    out = []
    for msg in track:
        t += msg.time
        out.append((t, msg))
    return out

def collect_notes_all_tracks(mid: MidiFile) -> List[Tuple[int,int,int,int]]:
    notes = []
    for tr in mid.tracks:
        on: Dict[Tuple[int,int], List[Tuple[int,int]]] = {}
        for t, msg in track_to_abs_events(tr):
            if msg.is_meta:
                continue
            ch = getattr(msg, "channel", None)
            if ch is None:
                continue
            if msg.type == "note_on" and msg.velocity > 0:
                key = (msg.note, ch)
                on.setdefault(key, []).append((t, msg.velocity))
            elif msg.type in ("note_off", "note_on") and getattr(msg, "velocity", 0) == 0:
                key = (msg.note, ch)
                if key in on and on[key]:
                    s, v = on[key].pop(0)
                    if t > s:
                        notes.append((s, t, msg.note, v))
    return notes

def read_first_timesig(mid: MidiFile) -> Tuple[int,int]:
    for tr in mid.tracks:
        for msg in tr:
            if isinstance(msg, MetaMessage) and msg.type == "time_signature":
                return msg.numerator, msg.denominator
    return 4,4

def load_groove_notes(groove_mid_path: Path) -> Tuple[List[GrooveNote], int]:
    mid = MidiFile(groove_mid_path)
    ppq = mid.ticks_per_beat
    num, den = read_first_timesig(mid)
    if num != 4 or den != 4:
        logger.warning(f"Groove TS {num}/{den} (se asume 4/4 para fases).")
    bar_ticks = int(ppq * 4 * (num/den))
    notes_raw = collect_notes_all_tracks(mid)
    if not notes_raw:
        raise ValueError("Groove vacío (no hay notas).")

    out: List[GrooveNote] = []
    for s, e, p, v in notes_raw:
        bar = (s // bar_ticks) + 1
        if bar < 1 or bar > 8:  # solo primeras 8 barras
            continue
        bar_start = (bar - 1) * bar_ticks
        phi_on  = (s - bar_start) / bar_ticks
        phi_off = (e - bar_start) / bar_ticks
        phi_on = max(0.0, min(0.999, float(phi_on)))
        phi_off = max(phi_on + 1e-4, min(0.999, float(phi_off)))
        out.append(GrooveNote(bar=bar, phi_on=phi_on, phi_off=phi_off, pitch=p, vel=v))
    return out, bar_ticks

def sidecar_for(groove_mid_path: Path) -> dict:
    yml = groove_mid_path.with_suffix(".yml")
    if not yml.exists():
        yml2 = groove_mid_path.with_suffix(".yaml")
        if yml2.exists():
            yml = yml2
        else:
            raise FileNotFoundError(f"Falta sidecar YAML: {yml.name}")
    data = yaml.safe_load(yml.read_text(encoding="utf-8"))
    if "key" not in data or "mode" not in data or "bars" not in data or len(data["bars"]) != 8:
        raise ValueError(f"YAML inválido {yml.name}: se esperan key, mode, bars[8].")
    return data

def triad_pcs_from_roman(key: str, mode: str, roman_str: str) -> Tuple[int, List[int]]:
    if is_rest_symbol(roman_str):
        root_pc = NOTE_PC[key]
        return root_pc, [root_pc, (root_pc+4)%12, (root_pc+7)%12]

    tok = parse_symbol(roman_str)
    deg_idx = ROMAN_TO_DEG[tok["core"]] - 1
    key_pc = NOTE_PC[key]

    m = mode.lower()
    if m in ("major","ionian","mayor"):
        pcs_mode = MAJOR_PCS
    elif m in ("minor_harmonic","harmonic_minor"):
        pcs_mode = HARMONIC_PCS
    else:
        pcs_mode = NATMIN_PCS

    root_pc = (key_pc + pcs_mode[deg_idx]) % 12
    if tok["quality"] and tok["quality"] in ("°","dim","dim7"):
        triad = [root_pc, (root_pc+3)%12, (root_pc+6)%12]
    else:
        if tok["core"][0].isupper():
            triad = [root_pc, (root_pc+4)%12, (root_pc+7)%12]
        else:
            triad = [root_pc, (root_pc+3)%12, (root_pc+7)%12]
    return root_pc, triad

def nearest_chord_tone_index(note_pc: int, triad_pcs: List[int]) -> int:
    best_i, best_d = 0, 12
    for i, pc in enumerate(triad_pcs[:3]):
        d = min((note_pc - pc) % 12, (pc - note_pc) % 12)
        if d < best_d:
            best_d = d
            best_i = i
    return best_i

def symbol_for_slot(symbol_bar: str, phi_on: float) -> str:
    parts = [s.strip() for s in symbol_bar.split("|") if s.strip()]
    if len(parts) == 2:
        return parts[0] if phi_on < 0.5 else parts[1]
    return parts[0] if parts else "NC"

def target_triad_midi(tonic: str, mode: str, symbol: str, octave: int = 5) -> Optional[List[int]]:
    if is_rest_symbol(symbol):
        return None
    tok = parse_symbol(symbol)
    root = degree_root_midi(tonic, mode, tok["core"], tok["accidental"], octave=octave)
    ints = chord_intervals(tok["core"], tok["quality"])
    return [root + ints[0], root + ints[1], root + ints[2]]

@dataclass
class LayerResult:
    events: List[MidiEvent]
    snaps: int

def map_groove_to_layer_range(
    groove_notes: List[GrooveNote],
    sidecar: dict,
    bars_symbols: List[str],
    tonic_target: str,
    mode_target: str,
    bar_ticks_out: int,
    allowed_pcs_out: set,
    channel: int,
    bar_start: int,
    bar_end: int,
    relative_to_region: bool = False,
) -> LayerResult:
    events: List[MidiEvent] = []
    snap_changes = 0

    key_src  = sidecar["key"]
    mode_src = sidecar["mode"]
    bars_src = sidecar["bars"]  # 8 strings

    for bar_idx in range(bar_start, bar_end + 1):
        bar_start_t = (bar_idx - bar_start) * bar_ticks_out if relative_to_region else (bar_idx - 1) * bar_ticks_out
        symbol_target_bar = bars_symbols[bar_idx - 1]

        rel = (bar_idx - bar_start) % 8
        gbar_idx = rel + 1
        symbol_src_bar = bars_src[gbar_idx - 1]

        gnotes = [gn for gn in groove_notes if gn.bar == gbar_idx]
        for gn in gnotes:
            src_sym = symbol_for_slot(symbol_src_bar, gn.phi_on)
            if is_rest_symbol(src_sym):
                continue
            _, triad_src_pcs = triad_pcs_from_roman(key_src, mode_src, src_sym)
            idx = nearest_chord_tone_index(gn.pitch % 12, triad_src_pcs)

            tgt_sym = symbol_for_slot(symbol_target_bar, gn.phi_on)
            if is_rest_symbol(tgt_sym):
                continue
            triad_tgt_midi = target_triad_midi(tonic_target, mode_target, tgt_sym, octave=5)
            if not triad_tgt_midi:
                continue

            # Inversiones en bajo (canal 1)
            try:
                tok_tgt = parse_symbol(tgt_sym)
                if channel == 1:
                    if tok_tgt.get("bass_inv") == "3":
                        idx = 1
                    elif tok_tgt.get("bass_inv") == "5":
                        idx = 2
            except Exception:
                pass

            target_pc = (triad_tgt_midi[idx]) % 12
            orig_oct = gn.pitch // 12
            new_note = orig_oct * 12 + target_pc

            if SNAP_POLICY == "strict":
                snapped = snap_note_to_pcs_same_octave(new_note, allowed_pcs_out)
                if snapped != new_note:
                    snap_changes += 1
                new_note = snapped

            onset = bar_start_t + int(gn.phi_on * bar_ticks_out)
            offset = bar_start_t + int(gn.phi_off * bar_ticks_out)
            dur = max(1, offset - onset)
            events.append(MidiEvent(onset, "on", new_note, NOTE_VELOCITY, channel=channel))
            events.append(MidiEvent(onset + dur, "off", new_note, 0, channel=channel))

    return LayerResult(events=events, snaps=snap_changes)


# =========================
# Guía "escala" (4 romanos)
# =========================
def apply_scale_guide_to_first_note(
    events: List[MidiEvent],
    guide_symbols: List[str],
    tonic: str,
    mode: str,
    allowed_pcs: set,
    bar_ticks: int,
    channel: int,
) -> List[MidiEvent]:
    """
    Ajusta la primera nota (note_on) de cada compás hacia el acorde guía de ese compás.
    También ajusta el note_off correspondiente (simple: el primer off luego del on).
    """
    if not events or not guide_symbols:
        return events

    ev = [MidiEvent(e.t, e.kind, e.note, e.vel, e.channel) for e in events]  # copia
    total_bars = len(guide_symbols)

    # index por tiempo
    ev_sorted_idx = sorted(range(len(ev)), key=lambda i: (ev[i].t, 0 if ev[i].kind == "on" else 1))

    for bar_i in range(total_bars):
        gsym = (guide_symbols[bar_i] or "").strip()
        if not gsym or is_rest_symbol(gsym):
            continue

        # triada guía
        try:
            triad = target_triad_midi(tonic, mode, gsym, octave=5)
        except Exception:
            triad = None
        if not triad:
            continue
        triad_pcs = [n % 12 for n in triad[:3]]

        bar_start = bar_i * bar_ticks
        bar_end = (bar_i + 1) * bar_ticks

        # encontrar primer note_on en ese compás y canal
        on_idx = None
        for i in ev_sorted_idx:
            if ev[i].channel != channel:
                continue
            if ev[i].kind != "on":
                continue
            if bar_start <= ev[i].t < bar_end:
                on_idx = i
                break

        if on_idx is None:
            continue

        old_note = ev[on_idx].note
        old_pc = old_note % 12
        old_oct = old_note // 12

        # mapear a chord tone guía más cercano
        best_pc = triad_pcs[nearest_chord_tone_index(old_pc, triad_pcs)]
        new_note = old_oct * 12 + best_pc

        if SNAP_POLICY == "strict":
            new_note = snap_note_to_pcs_same_octave(new_note, allowed_pcs)

        new_note = max(0, min(127, int(new_note)))
        if new_note == old_note:
            continue

        # cambiar on
        ev[on_idx].note = new_note

        # cambiar el primer off correspondiente después del on (misma nota vieja)
        off_idx = None
        for j in ev_sorted_idx:
            if j == on_idx:
                continue
            if ev[j].channel != channel:
                continue
            if ev[j].kind != "off":
                continue
            if ev[j].t <= ev[on_idx].t:
                continue
            if ev[j].note == old_note:
                off_idx = j
                break
        if off_idx is not None:
            ev[off_idx].note = new_note

    return ev


# =========================
# Selección archivos grooves
# =========================
def list_top_level_mids(folder: Path) -> List[Path]:
    if not folder or not folder.exists():
        return []
    out = []
    for p in folder.iterdir():
        if p.is_file() and p.suffix.lower() == ".mid":
            out.append(p)
    return sorted(out)

def list_bass_mids(folder: Path) -> List[Path]:
    if not folder or not folder.exists():
        return []
    bass_dir = folder / "bass"
    if not bass_dir.exists():
        return []
    out = []
    for p in bass_dir.iterdir():
        if p.is_file() and p.suffix.lower() == ".mid":
            out.append(p)
    return sorted(out)


# =========================
# Player via RtMidi
# =========================
class MidiPlayer(QtCore.QObject):
    playing_changed = QtCore.Signal(bool)

    def __init__(self):
        super().__init__()
        self._thread = None
        self._stop_flag = threading.Event()

    def _pick_output_port(self):
        import mido
        try:
            mido.set_backend('mido.backends.rtmidi')
        except Exception as e:
            logger.warning(f"No se pudo activar backend rtmidi: {e}")
        ports = mido.get_output_names()
        logger.info(f"Puertos MIDI disponibles: {ports}")
        if not ports:
            logger.error("No hay puertos MIDI de salida.")
            return None
        for p in ports:
            if "Microsoft GS Wavetable Synth" in p:
                return p
        for p in ports:
            if "MIDI" in p or "Mapper" in p:
                return p
        return ports[0]

    def start(self, midi_path: str):
        self.stop()
        self._stop_flag.clear()

        def run():
            import mido
            try:
                mido.set_backend('mido.backends.rtmidi')
                port_name = self._pick_output_port()
                if not port_name:
                    self.playing_changed.emit(False)
                    return
                logger.info(f"Usando puerto MIDI: {port_name}")
                mf = mido.MidiFile(midi_path)
                self.playing_changed.emit(True)
                with mido.open_output(port_name) as out:
                    for msg in mf.play():
                        if self._stop_flag.is_set():
                            break
                        if not msg.is_meta:
                            out.send(msg)
            except Exception as e:
                logger.error(f"Error en reproducción MIDI: {type(e).__name__}: {e}")
            finally:
                self.playing_changed.emit(False)

        self._thread = threading.Thread(target=run, daemon=True)
        self._thread.start()

    def stop(self):
        if self._thread and self._thread.is_alive():
            self._stop_flag.set()
            self._thread.join(timeout=1.0)
        self._thread = None
        self.playing_changed.emit(False)


# =========================
# UI helpers
# =========================
class NoWheelComboBox(QComboBox):
    def wheelEvent(self, event):
        event.ignore()

def reveal_in_file_manager(path: Path):
    try:
        if sys.platform.startswith("win"):
            subprocess.Popen(["explorer", "/select,", str(path)])
        elif sys.platform == "darwin":
            subprocess.Popen(["open", "-R", str(path)])
        else:
            subprocess.Popen(["xdg-open", str(path.parent)])
    except Exception as e:
        logger.warning(f"No se pudo abrir carpeta: {e}")


# =========================
# Ventana principal (Loop)
# =========================
class MainWindow(QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle(APP_NAME)
        self.resize(1180, 720)

        # Estado
        self.current_preview_path: Optional[str] = None
        self.player = MidiPlayer()
        self.player.playing_changed.connect(self._on_playing)

        # ---- Top bar: tonalidad / modo / bpm + acciones
        self.cmb_key = QComboBox()
        self.cmb_key.addItems(["C","C#","D","D#","E","F","F#","G","G#","A","A#","B"])
        self.cmb_key.setCurrentText("C")

        self.cmb_mode = QComboBox()
        self.cmb_mode.addItems(["major", "minor_natural", "minor_harmonic"])
        self.cmb_mode.setCurrentText("major")

        self.spn_bpm = QSpinBox()
        self.spn_bpm.setRange(40, 220)
        self.spn_bpm.setValue(BPM_DEFAULT)

        self.btn_reload = QPushButton("🔄")
        self.btn_reload.setToolTip("Recargar grooves")
        self.btn_random = QPushButton("🎲")
        self.btn_random.setToolTip("Randomizar grooves")
        self.btn_generate = QPushButton("⚡")
        self.btn_generate.setToolTip("Generar preview (4 compases)")
        self.btn_play = QPushButton("▶️")
        self.btn_play.setToolTip("Play preview")
        self.btn_stop = QPushButton("⏹️")
        self.btn_stop.setToolTip("Stop")
        self.btn_export = QPushButton("💾")
        self.btn_export.setToolTip("Exportar MIDI (genera si hace falta)")

        for b in (self.btn_reload, self.btn_random, self.btn_generate, self.btn_play, self.btn_stop, self.btn_export):
            b.setFixedWidth(38)

        top = QHBoxLayout()
        top.addWidget(QLabel("Tónica:")); top.addWidget(self.cmb_key)
        top.addWidget(QLabel("Modo:"));   top.addWidget(self.cmb_mode)
        top.addWidget(QLabel("BPM:"));    top.addWidget(self.spn_bpm)
        top.addStretch(1)
        top.addWidget(self.btn_reload)
        top.addWidget(self.btn_random)
        top.addWidget(self.btn_generate)
        top.addWidget(self.btn_play)
        top.addWidget(self.btn_stop)
        top.addWidget(self.btn_export)

        self.progress = QProgressBar()
        self.progress.setValue(0)

        # ---- Panel: progresión + escala guía
        self.grp_prog = QGroupBox("Progresión (4 compases · 1 acorde por compás)")
        prog_grid = QGridLayout(self.grp_prog)

        self.chord_boxes: List[QComboBox] = []
        self.scale_boxes: List[QComboBox] = []

        chord_options = [
            "I","ii","iii","IV","V","vi","vii°",
            "i","III","iv","v","VI","VII",
            "bII","bIII","bVI","bVII",
            "V7","i7","IVmaj7","ii7","vi7",
            "NC","—"
        ]

        for i in range(LOOP_BARS):
            lab = QLabel(f"Bar {i+1}")
            cb = NoWheelComboBox()
            cb.setEditable(True)
            cb.addItems(chord_options)
            cb.setCurrentText(["I","V","vi","IV"][i] if i < 4 else "I")
            self.chord_boxes.append(cb)

            prog_grid.addWidget(lab, 0, i)
            prog_grid.addWidget(cb, 1, i)

        self.grp_scale = QGroupBox("Guía (escala) 4 romanos (opcional · afecta la primera nota de cada compás)")
        scale_grid = QGridLayout(self.grp_scale)

        for i in range(LOOP_BARS):
            lab = QLabel(f"Bar {i+1}")
            cb = NoWheelComboBox()
            cb.setEditable(True)
            cb.addItems(["NC","—","I","ii","iii","IV","V","vi","vii°","i","III","iv","v","VI","VII"])
            cb.setCurrentText("NC")
            self.scale_boxes.append(cb)
            scale_grid.addWidget(lab, 0, i)
            scale_grid.addWidget(cb, 1, i)

        # ---- Panel: grooves por capa
        self.grp_grooves = QGroupBox("Grooves")
        ggrid = QGridLayout(self.grp_grooves)

        def make_groove_row(row: int, title: str) -> Tuple[QComboBox, QPushButton]:
            lab = QLabel(title)
            cb = NoWheelComboBox()
            cb.setSizeAdjustPolicy(QComboBox.AdjustToContents)
            btn = QPushButton("🎲")
            btn.setFixedWidth(36)
            btn.setToolTip("Elegir groove aleatorio")
            ggrid.addWidget(lab, row, 0)
            ggrid.addWidget(cb, row, 1, 1, 3)
            ggrid.addWidget(btn, row, 4)
            return cb, btn

        self.cb_m1, self.btn_m1_rand = make_groove_row(0, "Melody 1")
        self.cb_m2, self.btn_m2_rand = make_groove_row(1, "Melody 2")
        self.cb_m3, self.btn_m3_rand = make_groove_row(2, "Melody 3")
        self.cb_ba, self.btn_ba_rand = make_groove_row(3, "Bass")

        # ---- Logs
        self.log = QPlainTextEdit()
        self.log.setReadOnly(True)

        # ---- Layout principal (Proyecto)
        main = QWidget()
        v = QVBoxLayout(main)
        v.addLayout(top)
        v.addWidget(self.progress)

        v.addWidget(self.grp_prog)
        v.addWidget(self.grp_scale)
        v.addWidget(self.grp_grooves)

        # TABS
        self.tabs = QTabWidget()
        self.tabs.addTab(main, "Proyecto")
        self.tabs.addTab(self.log, "Logs")

        container = QWidget()
        container_layout = QVBoxLayout(container)
        container_layout.addWidget(self.tabs)
        self.setCentralWidget(container)

        # ---- Hooks
        self.btn_reload.clicked.connect(self.reload_grooves)
        self.btn_random.clicked.connect(self.randomize_all_grooves)
        self.btn_generate.clicked.connect(self.on_generate_preview)
        self.btn_play.clicked.connect(self.on_play)
        self.btn_stop.clicked.connect(self.on_stop)
        self.btn_export.clicked.connect(self.on_export)

        self.btn_m1_rand.clicked.connect(lambda: self.randomize_combo(self.cb_m1))
        self.btn_m2_rand.clicked.connect(lambda: self.randomize_combo(self.cb_m2))
        self.btn_m3_rand.clicked.connect(lambda: self.randomize_combo(self.cb_m3))
        self.btn_ba_rand.clicked.connect(lambda: self.randomize_combo(self.cb_ba))

        self.reload_grooves()
        self.log_info(f"Base recursos: {resource_base()}")
        self.log_info("Estructura esperada: grooves/*.mid (+ .yml) y grooves/bass/*.mid (+ .yml)")
        self.log_info("Loop: 4 compases (1 acorde por compás).")

    # ---- logs & ui helpers
    def log_info(self, msg): logger.info(msg); self.log.appendPlainText(f"[INFO] {msg}")
    def log_warn(self, msg): logger.warning(msg); self.log.appendPlainText(f"[WARN] {msg}")
    def log_err(self, msg):  logger.error(msg); self.log.appendPlainText(f"[ERROR] {msg}")

    def _on_playing(self, playing: bool):
        self.btn_play.setEnabled(not playing)
        self.btn_stop.setEnabled(playing)

    def randomize_combo(self, cb: QComboBox):
        n = cb.count()
        if n <= 0:
            return
        cb.setCurrentIndex(random.randrange(n))

    def reload_grooves(self):
        self.progress.setValue(0)
        try:
            if not GROOVES_DIR.exists():
                self.log_warn(f"No existe carpeta: {GROOVES_DIR}")
                # limpiar combos
                for cb in (self.cb_m1, self.cb_m2, self.cb_m3, self.cb_ba):
                    cb.clear()
                    cb.addItem("(sin grooves)", "")
                return

            mel = list_top_level_mids(GROOVES_DIR)
            bass = list_bass_mids(GROOVES_DIR)

            def fill(cb: QComboBox, items: List[Path], empty_label: str):
                cb.clear()
                if not items:
                    cb.addItem(empty_label, "")
                    return
                for p in items:
                    cb.addItem(p.name, str(p))

            fill(self.cb_m1, mel, "(sin melody grooves)")
            fill(self.cb_m2, mel, "(sin melody grooves)")
            fill(self.cb_m3, mel, "(sin melody grooves)")
            fill(self.cb_ba, bass, "(sin bass grooves)")

            self.progress.setValue(100)
            self.log_info(f"Grooves melody: {len(mel)} | bass: {len(bass)}")
        except Exception as e:
            self.log_err(f"Error recargando grooves: {e}")
            traceback.print_exc()
        finally:
            self.progress.setValue(0)

    def randomize_all_grooves(self):
        self.randomize_combo(self.cb_m1)
        self.randomize_combo(self.cb_m2)
        self.randomize_combo(self.cb_m3)
        self.randomize_combo(self.cb_ba)

    def _current_paths(self) -> Tuple[Optional[Path], Optional[Path], Optional[Path], Optional[Path]]:
        def p_of(cb: QComboBox) -> Optional[Path]:
            data = cb.currentData()
            return Path(data) if data else None
        return p_of(self.cb_m1), p_of(self.cb_m2), p_of(self.cb_m3), p_of(self.cb_ba)

    def _get_bars_symbols(self) -> List[str]:
        tonic = self.cmb_key.currentText()
        mode = self.cmb_mode.currentText()
        out = []
        for i, cb in enumerate(self.chord_boxes):
            raw = (cb.currentText() or "NC").strip()
            sym, changed, detail = normalize_symbol_for_mode(raw, mode)
            if changed:
                self.log_info(f"Bar {i+1}: '{raw}' → '{sym}' [{detail}]")
            out.append(sym)
        return out

    def _get_scale_guide(self) -> List[str]:
        mode = self.cmb_mode.currentText()
        out = []
        for i, cb in enumerate(self.scale_boxes):
            raw = (cb.currentText() or "NC").strip()
            sym, changed, detail = normalize_symbol_for_mode(raw, mode)
            if changed:
                self.log_info(f"Guía Bar {i+1}: '{raw}' → '{sym}' [{detail}]")
            out.append(sym)
        return out

    def _render_loop_midi(self) -> str:
        """
        Genera un MIDI preview del loop de 4 compases.
        """
        tonic = self.cmb_key.currentText()
        mode = self.cmb_mode.currentText()
        bpm = int(self.spn_bpm.value())

        bars_symbols = self._get_bars_symbols()
        guide_symbols = self._get_scale_guide()

        m1, m2, m3, ba = self._current_paths()

        allowed = allowed_scale_pcs(tonic, mode)
        bar_ticks = 4 * PPQ
        total_ticks = LOOP_BARS * bar_ticks

        mid = MidiFile(ticks_per_beat=PPQ)
        tempo_track = MidiTrack()
        tempo_track.append(MetaMessage("set_tempo", tempo=bpm2tempo(bpm), time=0))
        tempo_track.append(MetaMessage("time_signature", numerator=4, denominator=4, time=0))
        mid.tracks.append(tempo_track)

        # ---- Chords (triadas en canal 0)
        chords_events: List[MidiEvent] = []
        for bar_idx in range(1, LOOP_BARS + 1):
            symbol = bars_symbols[bar_idx - 1]
            start_t = (bar_idx - 1) * bar_ticks
            if is_rest_symbol(symbol):
                continue
            try:
                tok = parse_symbol(symbol)
                if tok.get("rest"):
                    continue
                r4 = degree_root_midi(tonic, mode, tok["core"], tok["accidental"], octave=4)
                iv = chord_intervals(tok["core"], tok["quality"])
                chord_midis = [r4 + iv[0], r4 + iv[1], r4 + iv[2]]

                inv = tok.get("bass_inv")
                if inv == "3":
                    chord_midis = [chord_midis[1], chord_midis[0], chord_midis[2]]
                elif inv == "5":
                    chord_midis = [chord_midis[2], chord_midis[0], chord_midis[1]]

                chord_midis, _ = snap_list_to_pcs(chord_midis, allowed)
                dur = int(bar_ticks * 0.95)
                for n in chord_midis:
                    chords_events.append(MidiEvent(start_t, "on", n, NOTE_VELOCITY, channel=0))
                for n in reversed(chord_midis):
                    chords_events.append(MidiEvent(start_t + dur, "off", n, 0, channel=0))
            except Exception as e:
                self.log_warn(f"Bar {bar_idx}: acorde omitido '{symbol}': {e}")

        # ---- Grooves proyectados (4 compases)
        def project_layer(path_mid: Optional[Path], channel: int) -> List[MidiEvent]:
            if not path_mid:
                return []
            side = sidecar_for(path_mid)
            gnotes, _ = load_groove_notes(path_mid)
            res = map_groove_to_layer_range(
                gnotes, side, bars_symbols, tonic, mode,
                bar_ticks, allowed, channel,
                bar_start=1, bar_end=LOOP_BARS,
                relative_to_region=True,
            )
            return res.events

        ev_m1 = project_layer(m1, 2)
        ev_m2 = project_layer(m2, 3)
        ev_m3 = project_layer(m3, 4)
        ev_ba = project_layer(ba, 1)

        # ---- aplicar guía (opcional) a la primera nota por compás (melodías)
        if guide_symbols and any((s.strip() not in ("", "NC", "—", "-") for s in guide_symbols)):
            ev_m1 = apply_scale_guide_to_first_note(ev_m1, guide_symbols, tonic, mode, allowed, bar_ticks, channel=2)
            ev_m2 = apply_scale_guide_to_first_note(ev_m2, guide_symbols, tonic, mode, allowed, bar_ticks, channel=3)
            ev_m3 = apply_scale_guide_to_first_note(ev_m3, guide_symbols, tonic, mode, allowed, bar_ticks, channel=4)

        # ---- Tracks
        tr_ch = write_track(chords_events)
        tr_ch.insert(0, MetaMessage("track_name", name="Chords", time=0))
        tr_ch.insert(0, Message("program_change", program=0, channel=0, time=0))
        mid.tracks.append(tr_ch)

        if ev_ba:
            tr_ba = write_track(ev_ba)
            tr_ba.insert(0, MetaMessage("track_name", name="Bass", time=0))
            tr_ba.insert(0, Message("program_change", program=33, channel=1, time=0))
            mid.tracks.append(tr_ba)

        if ev_m1:
            tr_m1 = write_track(ev_m1)
            tr_m1.insert(0, MetaMessage("track_name", name="Melody1", time=0))
            tr_m1.insert(0, Message("program_change", program=80, channel=2, time=0))
            mid.tracks.append(tr_m1)

        if ev_m2:
            tr_m2 = write_track(ev_m2)
            tr_m2.insert(0, MetaMessage("track_name", name="Melody2", time=0))
            tr_m2.insert(0, Message("program_change", program=81, channel=3, time=0))
            mid.tracks.append(tr_m2)

        if ev_m3:
            tr_m3 = write_track(ev_m3)
            tr_m3.insert(0, MetaMessage("track_name", name="Melody3", time=0))
            tr_m3.insert(0, Message("program_change", program=82, channel=4, time=0))
            mid.tracks.append(tr_m3)

        ts = datetime.now().strftime("%Y%m%d-%H%M%S")
        fname = f"loop_{tonic}_{mode}_{bpm}bpm_{ts}.mid".replace(" ", "_")
        out_path = PREVIEW_DIR / fname
        mid.save(out_path)
        self.current_preview_path = str(out_path)

        self.log_info(f"Preview generado: {out_path}")
        return str(out_path)

    # ---- acciones
    def on_generate_preview(self):
        self.progress.setValue(0)
        try:
            self.progress.setValue(15)
            p = self._render_loop_midi()
            self.progress.setValue(100)
            return p
        except Exception as e:
            self.log_err(f"Generación preview falló: {e}")
            traceback.print_exc()
            return None
        finally:
            self.progress.setValue(0)

    def on_play(self):
        try:
            if not self.current_preview_path or not Path(self.current_preview_path).exists():
                self.on_generate_preview()
            if self.current_preview_path:
                self.player.start(self.current_preview_path)
        except Exception as e:
            self.log_err(f"Play falló: {e}")

    def on_stop(self):
        self.player.stop()

    def on_export(self):
        try:
            if not self.current_preview_path or not Path(self.current_preview_path).exists():
                self.on_generate_preview()
            if not self.current_preview_path:
                self.log_warn("No hay preview para exportar.")
                return

            src = Path(self.current_preview_path)
            dest, _ = QFileDialog.getSaveFileName(self, "Exportar MIDI", str(src.name), "MIDI (*.mid)")
            if not dest:
                reveal_in_file_manager(src)
                return

            import shutil
            shutil.copy(str(src), dest)
            self.log_info(f"Exportado a: {dest}")
            reveal_in_file_manager(Path(dest))
        except Exception as e:
            self.log_err(f"Export falló: {e}")
            traceback.print_exc()


def main():
    app = QApplication(sys.argv)
    app.setStyleSheet(qdarkstyle.load_stylesheet(qt_api='pyside6'))
    w = MainWindow()
    w.show()
    sys.exit(app.exec())

if __name__ == "__main__":
    main()
