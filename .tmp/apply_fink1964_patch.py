from pathlib import Path

text = Path("Literature/Fink1964.lean").read_text(encoding="utf-8")
required = [
    "unfold f\n  simp_rw [P.fCoord_eq_sum]",
    "change\n          |-P.fCoord",
    "abbrev CostEntry",
    "theorem abs_cost_le_costBound",
]
missing = [anchor for anchor in required if anchor not in text]
if missing:
    raise RuntimeError(f"missing current Fink elaboration repair: {missing}")
