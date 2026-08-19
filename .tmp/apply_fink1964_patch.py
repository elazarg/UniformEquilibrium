from pathlib import Path

text = Path("Literature/Fink1964.lean").read_text(encoding="utf-8")
required = [
    "theorem fCoord_eq_sum",
    "simp_rw [P.fCoord_eq_sum]",
    "def stateCostBound",
    "mul_lt_mul_of_pos_left huv zero_lt_one",
]
missing = [anchor for anchor in required if anchor not in text]
if missing:
    raise RuntimeError(f"missing Fink elaboration repair: {missing}")
