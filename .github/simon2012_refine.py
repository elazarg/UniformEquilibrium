from base64 import b64decode
from gzip import decompress
from hashlib import sha256
from pathlib import Path

names = ["0", "1", "2a", "2b", "3"]
parts = [
    Path(f".github/simon2012_payload_{name}.txt").read_text().strip()
    for name in names
]
for name, part in zip(names, parts):
    print(name, len(part), sha256(part.encode()).hexdigest())
joined = "".join(parts)
print("joined", len(joined), sha256(joined.encode()).hexdigest())
raw = decompress(b64decode(joined))
print("source", len(raw), sha256(raw).hexdigest())
Path("Literature/Simon2012.lean").write_bytes(raw)
