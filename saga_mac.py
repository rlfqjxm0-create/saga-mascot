"""사가 마스코트 — macOS 앱 진입점 (.app 패키징용).

윈도우판(gippo_app.py)과 같은 구조지만 맥 경로 규칙을 따른다:
  설정·타이머 기록  ~/Library/Application Support/SagaMascot/
  자동 업데이트 파일 ~/Library/Application Support/SagaMascot/live/

GitHub의 version.json을 확인해 바뀐 파일만 임시 폴더에 모두 받은 뒤,
전부 성공했을 때만 live로 바꾼다(중간에 끊겨도 섞이지 않게).

맥 주의사항:
- 타자·펜 반응은 시스템 설정 > 개인정보 보호 및 보안 > 손쉬운 사용에서
  이 앱을 허용해야 동작한다 (권한이 없으면 조용히 반응만 안 함).
- 서명하지 않은 앱이라 첫 실행은 우클릭 > 열기로 열어야 한다.
"""
import hashlib
import json
import os
import shutil
import ssl
import sys
import time
import urllib.parse
import urllib.request

REPO = "rlfqjxm0-create/saga-mascot"   # 공개 배포 전용 레포
BRANCH = "main"
TIMEOUT = 20
RETRY = 3

BUNDLE = sys._MEIPASS if getattr(sys, "frozen", False) \
    else os.path.dirname(os.path.abspath(__file__))
APPDIR = os.path.expanduser("~/Library/Application Support/SagaMascot")
LIVE = os.path.join(APPDIR, "live")


def _ssl_ctx():
    """HTTPS 인증서 검증용 컨텍스트.

    앱에 들어간 OpenSSL은 빌드 머신(Homebrew) 기준 인증서 경로를 보는데,
    그 경로는 친구 맥에 없다. 그러면 인증서 검증이 실패해 업데이트가 조용히
    끊긴다. 그래서 certifi의 인증서 묶음을 명시적으로 쓴다.
    """
    try:
        import certifi
        return ssl.create_default_context(cafile=certifi.where())
    except Exception:
        try:
            return ssl.create_default_context()
        except Exception:
            return None


def _log(msg):
    """업데이트 실패 이유를 남긴다 — 안 남기면 왜 안 됐는지 알 길이 없다."""
    try:
        os.makedirs(APPDIR, exist_ok=True)
        with open(os.path.join(APPDIR, ".update.log"), "a", encoding="utf-8") as fp:
            stamp = time.strftime("%Y-%m-%d %H:%M:%S")
            fp.write(stamp + " " + str(msg) + os.linesep)
    except Exception:
        pass


def _fetch(path):
    """레포 파일의 원본 바이트 — raw.githubusercontent CDN."""
    quoted = urllib.parse.quote(path, safe="/")
    url = f"https://raw.githubusercontent.com/{REPO}/{BRANCH}/{quoted}"
    req = urllib.request.Request(url, headers={"User-Agent": "SagaMascot-updater"})
    for i in range(RETRY):
        try:
            with urllib.request.urlopen(req, timeout=TIMEOUT,
                                        context=_ssl_ctx()) as r:
                return r.read()
        except Exception:
            if i == RETRY - 1:
                raise
            time.sleep(1.0)


def _sha256(data):
    return hashlib.sha256(data).hexdigest()


def _local_bytes(rel, want):
    """live 또는 번들에 이미 같은 내용이 있으면 그 바이트를 돌려준다."""
    for base in (LIVE, BUNDLE):
        p = os.path.join(base, rel)
        if os.path.exists(p):
            with open(p, "rb") as fp:
                data = fp.read()
            if _sha256(data) == want:
                return data
    return None


def check_update():
    """전부 임시 폴더에 받아 놓고, 완전히 성공했을 때만 live로 바꾼다."""
    manifest = json.loads(_fetch("version.json").decode("utf-8"))
    cur = 0
    try:
        with open(os.path.join(LIVE, "version.json"), encoding="utf-8") as fp:
            cur = json.load(fp).get("version", 0)
    except Exception:
        pass
    if manifest.get("version", 0) <= cur:
        return
    first = cur == 0        # 설치 후 첫 실행 — 알릴 '변경'이 없다

    stage = os.path.join(APPDIR, "live.tmp")
    shutil.rmtree(stage, ignore_errors=True)
    for rel, want in manifest.get("files", {}).items():
        data = _local_bytes(rel, want)
        if data is None:
            data = _fetch(rel)
            if _sha256(data) != want:
                raise ValueError(f"해시 불일치: {rel}")
        dst = os.path.join(stage, rel)
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        with open(dst, "wb") as fp:
            fp.write(data)
    with open(os.path.join(stage, "version.json"), "w", encoding="utf-8") as fp:
        json.dump(manifest, fp)

    old = os.path.join(APPDIR, "live.old")           # 여기까지 왔으면 전부 성공
    shutil.rmtree(old, ignore_errors=True)
    try:
        if os.path.exists(LIVE):
            os.rename(LIVE, old)
        os.rename(stage, LIVE)
    except Exception:
        if os.path.exists(old) and not os.path.exists(LIVE):
            os.rename(old, LIVE)
        for root, _dirs, names in os.walk(stage):
            for name in names:
                src = os.path.join(root, name)
                dst = os.path.join(LIVE, os.path.relpath(src, stage))
                os.makedirs(os.path.dirname(dst), exist_ok=True)
                shutil.copy2(src, dst)
        shutil.rmtree(stage, ignore_errors=True)
    shutil.rmtree(old, ignore_errors=True)
    return manifest if not first else None           # 갱신된 경우만(+안내)


def _mark_updated(notes=None):
    """캐릭터가 시작할 때 말풍선으로 알리도록 신호를 남긴다.

    받은 새 코드는 바로 아래에서 읽어 실행하므로 재시작이 필요 없다.
    """
    try:
        items = [str(s).strip() for s in (notes or []) if str(s).strip()]
        with open(os.path.join(APPDIR, ".updated"), "w", encoding="utf-8") as fp:
            json.dump({"restart": False, "notes": items[:6]}, fp,
                      ensure_ascii=False)
    except Exception:
        pass


def main():
    os.makedirs(APPDIR, exist_ok=True)
    if os.environ.get("MASCOT_NO_UPDATE") != "1":
        try:
            man = check_update()
            if man:
                _mark_updated(man.get("notes"))
        except Exception as e:
            # 오프라인이면 그냥 넘어가되, 이유는 남긴다
            _log(f"업데이트 실패: {type(e).__name__}: {e}")

    live_mascot = os.path.join(LIVE, "mascot.py")
    live_parts = os.path.join(LIVE, "parts_saga")
    use_live = os.path.exists(live_mascot) \
        and os.path.exists(os.path.join(live_parts, "config.json"))

    if use_live:
        import importlib.util
        spec = importlib.util.spec_from_file_location("mascot", live_mascot)
        mascot = importlib.util.module_from_spec(spec)
        sys.modules["mascot"] = mascot
        spec.loader.exec_module(mascot)
        char_dir = live_parts
    else:
        import mascot
        char_dir = os.path.join(BUNDLE, "parts_saga")

    mascot.Mascot(char_dir=char_dir, state_dir=APPDIR).run()


if __name__ == "__main__":
    main()
