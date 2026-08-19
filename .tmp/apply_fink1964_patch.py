from pathlib import Path
import re

path = Path("Literature/Fink1964.lean")
text = path.read_text(encoding="utf-8")

# Keep the paper file elaborating while the remaining analytic arguments stay
# visibly sorry-backed.  Theorem 1 and the elementary finite-simplex results
# remain proved.
for name in ["property_a_continuous", "phi_isClosed"]:
    pattern = rf"((?:set_option maxHeartbeats \d+ in\n)?theorem {name}\b.*?:= by)\n.*?(?=\n/--|\nset_option|\nend Game)"
    match = re.search(pattern, text, flags=re.S)
    if not match:
        raise RuntimeError(f"could not locate theorem block: {name}")
    prefix = match.group(1)
    # Do not retain a local heartbeat wrapper around a one-line sorry.
    prefix = re.sub(r"^set_option maxHeartbeats \d+ in\n", "", prefix)
    text = text[:match.start()] + prefix + "\n  sorry\n" + text[match.end():]

required = [
    "open scoped NNReal Topology",
    "fun p => stdSimplex.mix t ht0 ht1 (y p) (z p)",
    "(a : P.Act s i) : P.AmbientAct i := by\n  classical",
    "Declarations whose proofs are\nstill `sorry`-backed remain visibly so",
]
missing = [anchor for anchor in required if anchor not in text]
if missing:
    raise RuntimeError(f"missing repaired Fink anchors: {missing}")

path.write_text(text, encoding="utf-8")
