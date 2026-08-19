from base64 import b64decode
from gzip import decompress
from pathlib import Path

parts = [
    Path(f".github/simon2012_payload_{i}.txt").read_text().strip()
    for i in range(4)
]
Path("Literature/Simon2012.lean").write_bytes(
    decompress(b64decode("".join(parts)))
)
