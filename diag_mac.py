# -*- coding: utf-8 -*-
"""맥 러너 진단 — 렉·검은 줄 제보를 숫자로 가른다 (CI 전용).

    python3 diag_mac.py <parts_폴더>

실기기가 없으므로 GitHub Actions 맥 러너에서 실제 Mascot 을 띄워 잰다:
  1) 생성(첫 창까지) 시간 — '켜지지도 않는다' 제보의 후보
  2) 프레임(_tick_body) 시간 분포 + _safe 구역별 누적 시간 — 렉의 범인
  3) NSWindow 를 주기적으로 열거해 **자라는 창**을 색출 — '까만 두 줄이
     계속 커진다' 제보의 정체 (창인가, 캔버스 안 그림인가)
  4) 소품을 만두·고양이로 강제해 각각 잰다 (최근에 넣은 모션이 범인인지)
  5) 끝나면 .error.log 와 맥 로그를 통째로 쏟는다

지뢰 51: '안 보인다'류는 화면만 보고 못 가른다 — 숫자를 남긴다.
"""
import os
import sys
import time

sys.stdout.reconfigure(encoding="utf-8", errors="replace")
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
CHAR = sys.argv[1] if len(sys.argv) > 1 else "parts_saga"

t_imp0 = time.time()
import mascot as M                                    # noqa: E402
print("[진단] import mascot: %.2fs" % (time.time() - t_imp0), flush=True)

M.Mascot._room_tick = lambda self, now: None          # 서버는 안 건드린다


# ── _safe 구역별 시간 + 프레임 시간 계측 ────────────────────────────
acc = {}
frames = []
orig_safe = M.Mascot._safe


def safe_timed(self, name, fn, *a, **k):
    t0 = time.perf_counter()
    try:
        return orig_safe(self, name, fn, *a, **k)
    finally:
        dt = time.perf_counter() - t0
        s = acc.setdefault(name, [0.0, 0, 0.0])
        s[0] += dt
        s[1] += 1
        s[2] = max(s[2], dt)


orig_body = M.Mascot._tick_body


def body_timed(self):
    t0 = time.perf_counter()
    try:
        return orig_body(self)
    finally:
        frames.append(time.perf_counter() - t0)


M.Mascot._safe = safe_timed
M.Mascot._tick_body = body_timed


def dump_stats(tag):
    if frames:
        fs = sorted(frames)
        n = len(fs)
        print("[진단:%s] 프레임 %d개 · 중앙 %.1fms · 상위90%% %.1fms · 최대 %.1fms"
              % (tag, n, fs[n // 2] * 1000, fs[int(n * 0.9)] * 1000,
                 fs[-1] * 1000), flush=True)
    top = sorted(acc.items(), key=lambda kv: -kv[1][0])[:14]
    for name, (tot, cnt, mx) in top:
        print("   %-18s 합 %7.1fms · %5d번 · 최대 %6.1fms"
              % (name, tot * 1000, cnt, mx * 1000), flush=True)
    frames.clear()
    acc.clear()


def dump_windows(tag, prev):
    """NSWindow 열거 — 자라는 창을 색출한다."""
    try:
        from AppKit import NSApplication
        wins = NSApplication.sharedApplication().windows()
        cur = {}
        for w in wins:
            try:
                f = w.frame()
                key = "%s#%d" % (w.className(), w.windowNumber())
                cur[key] = (int(f.size.width), int(f.size.height),
                            int(f.origin.x), int(f.origin.y),
                            bool(w.isVisible()))
            except Exception:
                pass
        for key, v in sorted(cur.items()):
            old = prev.get(key)
            grow = ""
            if old and (v[0] > old[0] or v[1] > old[1]):
                grow = "  ← 커졌다! %sx%s → %sx%s" % (old[0], old[1], v[0], v[1])
            if old != v or grow:
                print("[창:%s] %-28s %4dx%-4d at(%d,%d) 보임=%s%s"
                      % (tag, key, v[0], v[1], v[2], v[3], v[4], grow),
                      flush=True)
        return cur
    except Exception as e:
        print("[창] 열거 실패 %r" % e, flush=True)
        return prev


def run_phase(m, tag, secs, prev_wins):
    t_end = time.time() + secs
    last_win = time.time()
    while time.time() < t_end:
        try:
            m.root.update()
        except Exception as e:
            print("[진단:%s] update 예외 %r" % (tag, e), flush=True)
            break
        time.sleep(0.01)
        if time.time() - last_win > 3.0:
            last_win = time.time()
            prev_wins = dump_windows(tag, prev_wins)
    dump_stats(tag)
    return prev_wins


print("[진단] Mascot 생성 시작 (%s)" % CHAR, flush=True)
t0 = time.time()
try:
    m = M.Mascot(char_dir=CHAR)
except SystemExit as e:
    print("[진단] SystemExit %r — 중복 방지?" % e, flush=True)
    raise
print("[진단] 생성까지 %.2fs · 매끈=%s" % (time.time() - t0,
                                       getattr(m, "_smooth_on", "?")),
      flush=True)
m.root.update()
m.can_talk = True

wins = dump_windows("시작", {})
wins = run_phase(m, "기본소품", 18, wins)

for want in ("만두", "고양이"):
    pick = next((k for k, v in m._prop_layout.items()
                 if isinstance(v, dict) and v.get("gname") == want), None)
    print("[진단] 소품 강제: %s = %s" % (want, pick), flush=True)
    if pick:
        try:
            m._pick_prop = (lambda p=pick: p)
            t1 = time.time()
            m._load_parts()
            print("[진단] %s 파츠 로드 %.2fs" % (want, time.time() - t1),
                  flush=True)
        except Exception as e:
            print("[진단] %s 로드 실패 %r" % (want, e), flush=True)
    wins = run_phase(m, want, 18, wins)

# ── 매끈 레이어 채움 검증 — GPU 확대(contentsScale=1)가 창을 꽉
# 채우는가. 예전 '절반 크기' 사고(contentsScale=2 + 1배 그림)의 재발을
# 픽셀로 잡는다: 창 세로 82% 지점(책상)이 불투명해야 한다.
try:
    ck = getattr(m, "_mac_ck", None)
    W9 = m.root.winfo_width()
    H9 = m.root.winfo_height()
    if ck is not None:
        pts = [(W9 // 2, int(H9 * 0.82)), (W9 // 2, int(H9 * 0.55)),
               (W9 // 2, 2)]
        got = ck.probe(W9, pts)
        print("[채움] 창 %dx%d 중앙 82%%/55%%/위끝 ARGB = %s" % (W9, H9, got),
              flush=True)
        if got and len(got) >= 2:
            a_desk = (got[0][0] if isinstance(got[0], (list, tuple)) else 0)
            print("[채움] 책상 자리 알파=%s → %s" % (
                a_desk, "채워짐(정상)" if a_desk and a_desk > 30
                else "!! 비었다 — 절반 크기 재발 의심"), flush=True)
except Exception as e:
    print("[채움] 검증 실패 %r" % e, flush=True)

# ── 색상키 실검증 (검은 줄 — 지워지는지 합성 결과를 직접 읽는다) ──
try:
    m._safe("mac_verify", m._mac_verify)
except Exception as e:
    print("[진단] mac_verify 실패 %r" % e, flush=True)
try:
    m.root.update()
except Exception:
    pass

print("[진단] 종료 — 기록을 쏟는다", flush=True)
try:
    m.close()
except Exception:
    pass
for name in (".error.log", ".macwindow.log", ".yt_err.txt"):
    p = os.path.join(HERE, CHAR, name)
    if os.path.exists(p):
        print("── %s ──" % name, flush=True)
        try:
            body = open(p, encoding="utf-8", errors="replace").read()
            print(body[-4000:], flush=True)
        except Exception as e:
            print("읽기 실패 %r" % e, flush=True)
print("[진단] 끝", flush=True)
