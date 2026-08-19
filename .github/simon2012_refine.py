from base64 import b64decode
from gzip import decompress
from hashlib import sha256
from pathlib import Path
from subprocess import run

parts = [
    Path(f".github/simon2012_patch_{i}.txt").read_text().strip()
    for i in range(8)
]
joined = "".join(parts)
patch = decompress(b64decode(joined))
assert sha256(joined.encode()).hexdigest() == (
    "9d9c384a0daa93b15436dbd38c1c83dbe297a06f7e4df36df4e3ea40af81e7c5"
)
assert sha256(patch).hexdigest() == (
    "a3d04766babbfda6136f50dbbb11e48d825e85a369dce4710c05a3368f279d46"
)
run(["git", "apply", "--check", "-"], input=patch, check=True)
run(["git", "apply", "-"], input=patch, check=True)
