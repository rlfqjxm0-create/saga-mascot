# saga-mascot

saga 마스코트의 **자동 업데이트 페이로드**입니다. 사람이 읽을 것은 없습니다.

앱이 켜질 때 `version.json`의 SHA-256을 대조해 바뀐 파일만 내려받습니다.

`.gitattributes`의 `* -text`는 지우면 안 됩니다. git이 줄바꿈을 바꾸면 받은
바이트가 달라져 해시가 영원히 어긋나고, 그 파일에서 업데이트가 멈춥니다.

원본은 [ena-workspace](https://github.com/rlfqjxm0-create/ena-workspace)의
`ena-mascot/`에 있고, `make_manifest.py`가 이 레포로 밀어 넣습니다.
