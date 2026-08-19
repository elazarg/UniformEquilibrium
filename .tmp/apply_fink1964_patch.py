from pathlib import Path

text = Path("Literature/Fink1964.lean").read_text(encoding="utf-8")
proved = [
    "property_a_continuous", "property_b", "property_c",
    "contractingWith_valueOperator", "lemma_1", "T_le_fCoord",
    "exists_pure_fCoord_eq_T", "theorem_1", "corollary_1",
    "corollary_2", "phi_nonempty", "phi_segment", "phi_isClosed",
]
missing = [name for name in proved
           if f"theorem {name}" not in text or
              text.split(f"theorem {name}", 1)[1].split("theorem ", 1)[0].count("sorry")]
if missing:
    raise RuntimeError(f"proof patch missing or still sorry-backed: {missing}")
