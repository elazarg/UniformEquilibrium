from pathlib import Path

path = Path("Literature/Fink1964.lean")
text = path.read_text(encoding="utf-8")
old = """/-- Extend one local action to a complete contingent plan using fixed actions
at every other state. -/
open Classical in
def extendAction (P : Game ι) (s : P.State) (i : ι)
    (a : P.Act s i) : P.AmbientAct i :=
  fun t => if h : t = s then h.symm ▸ a else Classical.choice (P.act_nonempty t i)
"""
new = """/-- Extend one local action to a complete contingent plan using fixed actions
at every other state. -/
def extendAction (P : Game ι) (s : P.State) (i : ι)
    (a : P.Act s i) : P.AmbientAct i := by
  classical
  exact fun t =>
    if h : t = s then h.symm ▸ a else Classical.choice (P.act_nonempty t i)
"""
if old in text:
    text = text.replace(old, new, 1)
elif new not in text:
    raise RuntimeError("extendAction repair anchor not found")
path.write_text(text, encoding="utf-8")
