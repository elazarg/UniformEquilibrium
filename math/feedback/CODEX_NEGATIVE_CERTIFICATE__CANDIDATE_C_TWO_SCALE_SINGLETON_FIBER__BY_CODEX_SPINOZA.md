# Audit of the Candidate-C two-scale singleton fibre

Identity: `CODEX_SPINOZA`  
Date: 2026-09-03  
Verdict: **PASS as exact ordinary mathematics**, with the note's existing
qualification that the one-sided approximate-active mesh wrapper is not yet a
named Lean theorem.

## Claim audited

The note fixes the four Candidate-C singleton rows and leaves all 44
nonsingleton reward coordinates arbitrary.  It claims that the fixed vector

\[
b=(1,-1/2,0,-1/4)=r(\{1\})
\]

is a uniform-equilibrium payoff, via a two-block singleton cycle with total
hazards \(\delta\) and \(1/2\), followed by equal-survival mesh subdivision.

## Exact data and coarse algebra

The singleton rows agree with `CANDIDATE_C_ROWS` in
`experiments/codex_riemann_inert_perturbation_search.py`:

\[
r(\{0\})=(1,-3/4,0,1/2),\quad
r(\{1\})=(1,-1/2,0,-1/4),
\]

\[
r(\{2\})=(0,1,-1,0),\quad
r(\{3\})=(1/4,1/2,1/4,-1/4).
\]

There are \(15\cdot4=60\) table coordinates and the four singleton rows fix
16 of them, so the asserted affine fibre dimension is exactly 44.  For an
arbitrary point of this fibre,

\[
M=\max_{S\ne\varnothing,i}|r_i(S)|
\]

is a valid finite reward bound and \(D=2M\) bounds every collision-minus-solo
difference.  Here automatically \(M\ge1\).

Solving

\[
x=\delta A+(1-\delta)y,\qquad y=\tfrac12b+\tfrac12x
\]

gives, with \(d=1+\delta\),

\[
x=\frac{2\delta A+(1-\delta)b}{d},\qquad
y=\frac{b+\delta A}{d}.
\]

The four displayed coordinate formulae in the note are correct.  In
particular

\[
\|y-b\|_\infty=\frac{3\delta}{4d},
\]

and the largest deficit below an own singleton reward at either endpoint is
player 1's deficit at \(x\), namely

\[
\eta_\delta=\frac{\delta}{2d}.
\]

All mesh interpolants lie coordinatewise between their coarse endpoints, so
the same \(\eta_\delta\) bound holds at every microphase.

## Bellman and unrestricted-deviation check

At a microphase owned by \(j\), with micro-hazard \(h\), a passive player
\(i\)'s immediate-Quit value is

\[
(1-h)r_i(\{i\})+h r_i(\{i,j\}).
\]

Since the current value is at least \(r_i(\{i\})-\eta_\delta\), its excess is
at most \(\eta_\delta+2Mh\).  The active owner's immediate-Quit value is its
singleton value and has excess at most \(\eta_\delta\), so the same common
bound applies.

Prescribed Continue is exact for every passive player.  It is exact for owner
0 because that owner's coordinate is constantly one.  In owner 1's block the
singleton value \(-1/2\) lies strictly above both coarse endpoint values; the
arc identity therefore makes the next-phase Continue value weakly below the
current value.  This is exactly the one-sided inequality needed after adding
the common constant supersolution error.  Thus

\[
e(\delta,m)=\eta_\delta+2M\max\{h_m(\delta),h_m(1/2)\}
\]

is a valid global Snell supersolution error.  Equality in the checked
`quittingCyclicHazardTerminalValue_le_add_of_quitError_exactContinue` is used
only to derive this Continue branch inequality, so replacing equality for
owner 1 by the directly verified favourable inequality is sound.

The deleted-player continuation products over a whole cycle are exactly

\[
1/2\quad(i=0),\qquad 1-\delta\quad(i=1),\qquad
(1-\delta)/2\quad(i=2,3),
\]

all strictly below one for \(0<\delta<1\).  Consequently the residual term in
the Snell iteration vanishes for every complete behavioral replacement.  The
argument includes Never and every arbitrarily late or randomized stopping
law; it is not a bounded-controller calculation.

## Quantifiers and fixed target

For fixed \(\delta\), both mesh hazards tend to zero as \(m\to\infty\).
Given an accuracy, choose \(\delta>0\) first so that both
\(\eta_\delta\) and \(\|y-b\|_\infty\) are small, then choose \(m\) depending
on that \(\delta\), the accuracy, and the fibre point's bound \(M\).  A
diagonal sequence therefore has terminal error tending to zero and terminal
payoff tending to the **single fixed target** \(b\).  The named theorem
`quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto` (or its
all-errors approximate-target form) then supplies the correct uniform-horizon
quantifiers: after the profile is selected for the requested error, one
horizon threshold works for all later horizons.

The increasingly slow contraction as \(\delta\downarrow0\) only enlarges
that selected profile's horizon threshold; it does not interchange the
uniform-equilibrium quantifiers.

## Scope and export relevance

The result genuinely excludes Candidate C and its whole 44-dimensional
nonsingleton fibre from the counterexample search.  It does not classify
nearby singleton matrices, prove completeness of two-scale cycles, or address
the full Fin4 conjecture.

It is suitable for export as a **special-class Fin4 uniform-payoff theorem**
after the approximate-active cyclic supersolution wrapper is formalized (or
the existing proof is generalized from Continue equality to Continue
inequality) and independently Lean-checked.  Until then, the present note is
correct ordinary mathematics but should not carry an `L` seal.

## Sources checked

- `notes/CODEX_NEGATIVE_CERTIFICATE__CANDIDATE_C_TWO_SCALE_SINGLETON_FIBER.md`;
- `notes/CODEX_RIEMANN__PERSISTENT_PAIR_CHAMBER_NO_GO.md`;
- `experiments/codex_riemann_inert_perturbation_search.py`;
- `quittingSingletonArcCycleRoot`,
  `quittingSingletonArcCycleValue`, and
  `quittingSingletonArcCycle_phase_certificate` in
  `UniformEquilibrium/Quitting/Cycles/SingletonArcCycle.lean`;
- `quittingCyclicHazardTerminalValue_le_add_of_quitError_exactContinue` and
  `isεAsymptoticNash_quittingCyclicBehaviorProfile_of_quitError_exactContinue`
  in `UniformEquilibrium/Quitting/Cycles/CyclicSupersolution.lean`; and
- `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto` in
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
