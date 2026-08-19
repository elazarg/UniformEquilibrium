from pathlib import Path

text = Path("Literature/Fink1964.lean").read_text(encoding="utf-8")
for name in ["property_a_continuous", "theorem_1", "phi_isClosed"]:
    block = text.split(f"theorem {name}", 1)[1].split("theorem ", 1)[0]
    if "sorry" in block:
        raise RuntimeError(f"{name} is still sorry-backed")
