from pathlib import Path

text = Path("Literature/Fink1964.lean").read_text(encoding="utf-8")
required = [
    "open scoped NNReal Topology",
    "fun p => stdSimplex.mix t ht0 ht1 (y p) (z p)",
    "letI : ∀ i, Fintype (P.Act s i) := fun i => inferInstance",
    "def extendAction (P : Game ι)",
    "(a : P.Act s i) : P.AmbientAct i := by\n  classical",
    "those conclusions remain\n`sorry`-backed rather than checked",
]
missing = [anchor for anchor in required if anchor not in text]
if missing:
    raise RuntimeError(f"missing repaired Fink anchors: {missing}")
