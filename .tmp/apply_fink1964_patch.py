from pathlib import Path
import re

path = Path("Literature/Fink1964.lean")
text = path.read_text(encoding="utf-8")

# Keep the audit honest and elaborating while the remaining analytic proofs
# are worked on.  These declarations are intentionally visible as sorry-backed.
for name in ["property_a_continuous", "theorem_1", "phi_isClosed"]:
    pattern = rf"(theorem {name}\b.*?:= by)\n.*?(?=\n/--|\nend Game)"
    match = re.search(pattern, text, flags=re.S)
    if not match:
        raise RuntimeError(f"could not locate theorem block: {name}")
    text = text[:match.start()] + match.group(1) + "\n  sorry\n" + text[match.end():]

# These unused helper bounds were the source of dependent Fintype synthesis
# failures.  Lemma 2 and Theorem 2 state the paper claims without requiring
# a separately exported bound definition.
start_marker = "/-- A finite index for one entry of the paper's cost table. -/"
end_marker = "/-- **Lemma 2.**"
if start_marker in text:
    start = text.index(start_marker)
    end = text.index(end_marker, start)
    text = text[:start] + text[end:]

reward_start = "/-- A finite bound on the production reward table."
reward_end = "/-- Marginalization of independent contingent plans"
if reward_start in text:
    start = text.index(reward_start)
    end = text.index(reward_end, start)
    text = text[:start] + text[end:]

text = text.replace(
    "simp [actionPMF_apply_toReal, stdSimplexEquiv_symm_apply,\n    ofVector_toReal]",
    "simp [actionPMF_apply_toReal, stdSimplexEquiv_symm_apply]",
    1,
)

old_status = """The marginalization lemmas below identify the required transfer back to the
literal state-dependent action sets.  The final reward/cost bridge and Theorem 2
are stated explicitly; until their proofs are discharged, those conclusions remain
`sorry`-backed rather than checked."""
new_status = """The file records every numbered statement.  Declarations whose proofs are
still `sorry`-backed remain visibly so; the surrounding prose does not describe
them as checked.  In particular, the final reward/cost bridge and Theorem 2 are
not yet discharged."""
if old_status in text:
    text = text.replace(old_status, new_status, 1)

path.write_text(text, encoding="utf-8")
