from pathlib import Path

text = Path("Literature/Fink1964.lean").read_text(encoding="utf-8")
required = [
    "open scoped NNReal Topology",
    "fun p => stdSimplex.mix t ht0 ht1 (y p) (z p)",
    "def extendAction (P : Game ι)",
    "Declarations whose proofs are\nstill `sorry`-backed remain visibly so",
]
missing = [anchor for anchor in required if anchor not in text]
if missing:
    raise RuntimeError(f"missing honest Fink audit repair: {missing}")
