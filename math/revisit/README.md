# Formalization Revisit Queue

This directory retains export packets that contain useful mathematics but are
not suitable for the active formalization queue as written.

A packet belongs here when at least one of the following holds:

- a stated claim is false or needs corrected hypotheses;
- the useful conjecture-facing content is already proved in Lean, while a
  remaining claim is not worth prioritizing;
- a substantial checked subset exists, but the packet cannot honestly move to
  `formalized/`; or
- completing it requires new infrastructure whose value should be reassessed
  before implementation.

Every packet should begin by stating what is checked, what prevents promotion,
and what would justify revisiting it. The containing directory is its lifecycle
status; do not repeat that status in a packet header. Move a repaired and fully
accepted target back to `exports/`; move it to `formalized/` once its useful
stated content is checked in Lean.
