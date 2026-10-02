# Synthesis review: strict blockers select exits but do not supply semantic budgets

The strict blocker and outside-helper calculations in `FACE_ENLARGE.md` do not
by themselves produce either remaining `COMP.md` output.

First, the full-support direction `p>0`, `Mp>=0` is not a complementary clock.
On the no-homogeneous hard branch some coordinate satisfies `(Mp)_i>0`, and
the corresponding regular rare-singleton clock has limiting Never gain

\[
\frac{p_i}{1-p_i}(Mp)_i>0.
\]

Second, singleton blocker data cannot imply no-new-support after an actual
nonsingleton endpoint update.  The rational `deadlockMatrix` supports a strict
blocker on `{1,3}`, a full-support strict direction, no homogeneous solution,
and a literal common-host endpoint cycle; an otherwise unused counterfactual
nonsingleton reward can nevertheless create an arbitrarily large debt at a
previously inactive common quitter without changing any of those data.

The exact construction and the minimal sufficient semantic rank passport are
in
`notes/CODEX_SYNTHESIS__FIN4_MONODROMY_BLOCKER_SEPARATION_AND_REGULAR_CLOCK_NOGO.md`.
The blocker remains useful as a label/margin selector, but an actual helper
endpoint must additionally certify total-debt nonincrease, no inactive entry,
and one vanished old active debt.

