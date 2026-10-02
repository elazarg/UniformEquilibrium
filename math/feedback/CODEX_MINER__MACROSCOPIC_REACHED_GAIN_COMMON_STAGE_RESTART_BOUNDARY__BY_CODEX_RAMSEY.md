# Independent review of `MACROSCOPIC_REACHED_GAIN_COMMON_STAGE_RESTART_BOUNDARY`

**Reviewer:** `CODEX_RAMSEY`  
**Verdict:** **PASS in the repaired internal scope; no export recommendation.**

## Claim checked

The note iterates the gain arm of
`causalCollision_tailEscape_or_quantitativeNearMinimumTransfer` at one fixed
reached date.  The repaired statement returns, at every fixed depth, a
common-tail debt excursion, an actual endpoint debt excursion, a reached
singleton atom, or a literal chain of profitable stage-pure endpoint
restarts.  In the last arm finite marked-root recurrence gives a closed
endpoint-improvement word.  The note claims only that every selected root
fails support Nash against the one fixed suffix payoff; it does not claim
that freely chosen rotated phase values cannot support a projective lasso.

## 1. Literal restart and common suffix: PASS

The target in the checked gain theorem is literally

```text
Function.update profile who
  (quittingStagePureEndpointBehaviorDeviation
    reward profile who stage action).
```

It is therefore an actual behavioral profile and can be passed verbatim as
the next source.  The defining live-hazard identity changes only `who` at the
marked date and resumes the old live root word at `stage+1`.  Induction over
the restarts consequently preserves every live root off the marked date and
preserves the complete suffix root word.  In a quitting game the only
nonterminal history is the live all-Continue history, so equality of this
suffix word gives equality of both the prescribed terminal payoff and every
unrestricted unilateral cap of the suffix.  Thus the common terminal-semantic
suffix pair asserted in (3.1) is legitimate, not merely equality of a
normal-form proxy.  `quittingLiveMass_stagePureEndpoint_eq` also gives exact
preservation of the probability of reaching the marked date.

## 2. Squared routed mass and gain constants: PASS

At step `k`, the old stage atom lower bound `beta_k` implies live mass at
least `beta_k`.  The gain theorem separately returns routed *root* mass at
least `beta_k`; multiplying it by the unchanged live mass gives actual
target-stage mass at least

```text
beta_k^2 = alpha^(2^(k+1)) = beta_(k+1).
```

Since the initial atom mass satisfies `0 < alpha <= 1`, the sequence
`beta_k` is nonincreasing.  The checked inequality

```text
beta_k^2 * D_* / 2 <= card(I) * gain_k
```

therefore yields exactly

```text
gain_k >= beta_(k+1) * D_* / (2 card(I)),
```

and, through depth `K`, the common lower bound `c_K`.  The tail-escape lower
bound similarly dominates `e_K=beta_K*D_*/2`.  The mover-debt identity is a
literal conclusion of the checked transfer theorem.  A direct check at
`alpha=1/2` gives the intended sequence `1/2,1/4,1/16,...`; there is no
missing additional reach factor.

The repaired singleton stopping arm is necessary and sufficient for the
induction's typing.  A Continue update can erase one member of a two-player
collision, leaving a positive-mass singleton; nonemptiness survives, but the
next collision invocation's strict `1 < card` hypothesis does not.  The
current Theorem 4.1 and Corollary 5.1 now stop exactly there.

## 3. Finite recurrence: PASS

After any number of updates, each marked-date marginal is one of its initial
value, pure Continue, or pure Quit.  Hence there are at most `3^N` marked
root states.  A collision-preserving chain with `3^N` edges has `3^N+1`
source profiles, so two marked roots coincide.  The common off-date live
word then makes the whole live word, terminal law, prescribed payoff, cap
vector, and semantic pair coincide.  The intervening segment is nonempty and
every literal source-to-target endpoint repair retains the fixed positive
gain bound.

This is a closed best-response word, not a Nash--Bellman cycle.  Gains belong
to potentially different movers, so their positivity is fully compatible
with return of the entire payoff/debt vector.

## 4. Fixed-tail support defect: PASS

For a selected edge, exact gain factorization is

```text
gain = liveMass * coordinateNashDefect(reward,T.1,root,who).
```

Because `0 < liveMass <= 1`, the coordinate defect is at least the gain and
hence at least `c`.  The checked opposite-action lemma gives positive root
probability on the losing action.  In a binary mixture the coordinate defect
is that losing probability times the absolute endpoint gap; the gap is
therefore at least the defect.  The appropriate support inequality fails for
every `delta<c`, in either best-Continue or best-Quit orientation.

The qualification in the repaired note is exact: this failure is only at
the fixed common continuation `T.1`.  A
`QuittingFiniteSignedProjectiveLasso` tests each phase root against its own
rotated phase value.  Nothing here excludes other phase values that repair
support while satisfying a signed Bellman seam; the construction simply
does not produce them.

## 5. AGKRS separation and status

The producer-level hypothesis separation is correct.  The collision restart
uses `D_*>0`, equivalent to failure of a uniform-equilibrium payoff.  The
actual cofinal AGKRS source is extracted from approximate-equilibrium
existence, which already has a checked uniform-payoff consequence.  Thus the
two actual producers cannot be combined on one reward table.  This says
nothing contradictory about arbitrary bare inhabitants of their erased data
structures.

I found no additional consumer in the named sources.  The result is useful
as an internal, source-native finite-restart boundary: it removes the profile
provenance ambiguity and identifies the remaining failure as simultaneous
Nashification/phase-value production.  It does not yield S.1/S.2/S.3, a
charged semantic return, a well-founded rank decrease, or a positive-minimum
counterexample, so it does not meet the export significance gate.

## Sources checked

- `TerminalSemanticCausalCollisionMinimumTransfer.lean`;
- `TerminalSemanticPlateauLocalizedOtherDefect.lean`;
- `TerminalSemanticCausalCollisionAtomicOrientation.lean`;
- `TerminalSemanticPlateauDefectStratification.lean`;
- `SupportEnlargementAlternative.lean`;
- `SignedProjectiveLasso.lean`; and
- `PrioritizedPreemptionSeedBoundary.lean`.

The review is independent of the earlier Euler audit.  Comparing afterward,
the repaired singleton arm and fixed-tail-only anti-lasso scope are exactly
the two points that audit had required.
