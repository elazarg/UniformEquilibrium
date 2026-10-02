# Two-clock conditioned cross-share rigidity

## Status

This is a self-contained **conditional ordinary-mathematics theorem** extracted
from the audit of `HARD_RESIDUE.md`.  It is not exported and is not claimed to
be checked in Lean.

The theorem corrects the proposed diffuse two-clock argument.  Ordinary
convergence to a boundary is not an error estimate relative to the vanishing
remaining-absorption mass, so the earlier block-normalization proof does not
work.  The correct invariant is the complete future terminal law conditioned
on absorption.  With cross-singleton mass aligned to dates at which the other
player is active, that law forces the corresponding normalized solo entry to
vanish.

No current source theorem is known to produce all of the conditioned-mesh and
aligned-cross-share hypotheses below.  The result therefore excludes a
supplied tail architecture; it does not consume a current Fin4 atlas node.

## Setting

Let `I` be finite, let

\[
r:\{S\subseteq I:S\ne\varnothing\}\longrightarrow\mathbb R^I
\]

be a quitting reward table, and suppose

\[
|r_i(S)|\le M
\]

for all players and nonempty coalitions.  Let `x_t` be a sequence of product
roots and `v_t` a sequence of continuation values satisfying the exact
Bellman recursion

\[
v_t=F_{x_t}(v_{t+1})
\]

and the exact endpoint-Nash conditions at every date.  Let `b` be a boundary
value such that, coordinatewise,

\[
v_t\longrightarrow b.
\tag{1}
\]

Write

\[
\alpha_t=1-\prod_{i\in I}x_{t,i}(C)
\]

for the raw one-stage absorption probability, and

\[
A_t=1-\prod_{u\ge t}(1-\alpha_u)
\]

for the eventual absorption probability from date `t`.  Assume `A_t>0` for
every date under consideration.  Define the conditioned one-stage mesh

\[
w_t=\frac{\alpha_t}{A_t}.
\tag{2}
\]

For a nonempty coalition `S`, write

\[
\Pi_t(S)=
\Pr(\text{terminal coalition is }S\mid
     \text{eventual absorption from }t).
\tag{3}
\]

Finally, for distinct players `p,q`, use the project's normalization

\[
M_{p,q}
=\operatorname{normalizedSoloMatrix}(r)_{p,q}
=r_p(\{q\})-r_p(\{p\}).
\tag{4}
\]

## Theorem

Assume:

1. `w_t -> 0`;
2. after some finite date, only the two distinct players `p,q` can Quit;
3. the boundary is pinned at their singleton rewards,

   \[
   b_p=r_p(\{p\}),\qquad b_q=r_q(\{q\});
   \tag{5}
   \]

4. there are dates `s_n -> infinity` and `eta_q>0` such that `p` has positive
   Quit probability at `s_n` and

   \[
   \Pi_{s_n}(\{q\})\ge\eta_q;
   \tag{6}
   \]

5. there are dates `t_n -> infinity` and `eta_p>0` such that `q` has positive
   Quit probability at `t_n` and

   \[
   \Pi_{t_n}(\{p\})\ge\eta_p.
   \tag{7}
   \]

Then

\[
\boxed{M_{p,q}=0\quad\text{and}\quad M_{q,p}=0.}
\tag{8}
\]

More precisely, at every sufficiently late `p`-active date `s` with
`Pi_s({q}) >= eta_q`,

\[
\boxed{
\eta_q|M_{p,q}|
\le
2M\bigl(w_s+\Pi_s(\{p,q\})\bigr)
\le
4M\sup_{u\ge s}w_u.}
\tag{9}
\]

The symmetric estimate holds for `M_{q,p}`.

## Proof

Let `vhat_s` be the boundary-corrected terminal value of the tail beginning at
`s`, conditioned on eventual absorption.  Assumption (1) is needed here: the
checked phantom-boundary identity identifies `vhat_s` with the actual future
terminal payoff divided by `A_s` only under `v_t -> b`.

At a `p`-active date, exact endpoint Nash and the pinning equality (5) give
the conditioned active-support estimate

\[
|\widehat v_s(p)-r_p(\{p\})|\le2M w_s.
\tag{10}
\]

After the finite support cutoff, the only possible terminal coalitions are
`{p}`, `{q}`, and `{p,q}`.  Therefore the conditioned terminal-law identity
gives

\[
\widehat v_s(p)-r_p(\{p\})
=\Pi_s(\{q\})M_{p,q}
+\Pi_s(\{p,q\})
  \bigl(r_p(\{p,q\})-r_p(\{p\})\bigr).
\tag{11}
\]

It remains to control collision.  At a two-clock root, write `a,b` for the
two Quit probabilities and

\[
\alpha=a+b-ab.
\]

The collision mass is `ab`, and

\[
ab\le\alpha^2,
\qquad
\frac{ab}{\alpha}\le\alpha
\tag{12}
\]

whenever `alpha>0`.  The future conditioned collision share is an average of
these stagewise collision fractions, weighted by the conditional absorption
date.  Hence

\[
\Pi_s(\{p,q\})
\le\sup_{u\ge s}\alpha_u
\le\sup_{u\ge s}w_u,
\tag{13}
\]

where the last inequality uses `A_u<=1`, and therefore `alpha_u<=w_u`.

Taking absolute values in (11), using (10), the reward bound, and
`Pi_s({q})>=eta_q`, yields the first inequality in (9).  Since
`w_s<=sup_{u>=s}w_u`, (13) gives the second.  Convergence `w_t->0` implies its
tail supremum tends to zero.  Apply (9) along `s_n` to obtain `M_{p,q}=0`.
The symmetric argument along `t_n` proves `M_{q,p}=0`.

The argument permits arbitrarily fragmented or alternating singleton mass.
It does not require a long solo window or a fixed-length block.

## Fin4 hard-principal contradiction

For a two-element nonprojective principal in the checked Fin4 full-support
hard residual, the two reciprocal normalized solo entries are strictly
negative:

\[
M_{p,q}<0,
\qquad
M_{q,p}<0.
\tag{14}
\]

This is the data stored by `FinFourHardCardTwoCrossing`, produced by
`FinFourQuantitativeFullSupportHardResidual.cardTwoCrossing` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/
FullSupportHardPrincipalDispatch.lean`.

Equations (8) and (14) are incompatible.  Thus a card-two hard principal
cannot support a tail satisfying all the hypotheses of the theorem.

This conclusion is conditional.  The checked hard-principal theorem supplies
the static signs (14), not the exact two-clock tail or the aligned conditioned
shares (6)--(7).

## Necessary hypotheses and falsifiers

### Boundary convergence is necessary

The vector `b` cannot be introduced only through the two equalities (5).  If
`v_t -> b` is omitted, it is unrelated to the Bellman path and the conditioned
terminal-value identity cannot be invoked.

Ordinary convergence also cannot support the discarded block proof: if
`A_s -> 0`, a block carrying a fixed fraction of the remaining absorption can
have mass of order `A_s`.  The estimate `v_s-b -> 0` does not imply
`v_s-b=o(A_s)`.

### Aligned cross-share is necessary

If only `p` ever absorbs, the chronology never reads the coordinate
`r_p({q})`.  That coordinate, and hence `M_{p,q}`, can be changed arbitrarily
without changing the path.  A positive `q`-singleton share specifically at
starts where `p` is active is essential.  An unaligned statement that both
players appear somewhere in the tail is insufficient.

### Eventual pair support is necessary for individual vanishing

With a third persistent singleton, (11) contains another first-order solo
term.  The account then yields a linear relation among several normalized
solo entries, not `M_{p,q}=0` individually.

### Diffuseness is necessary

If conditioned collision retains a positive share, the pair-reward term in
(11) can cancel a nonzero solo entry.  The bound (13), and thus the conclusion,
can fail.

### Failure of conditioned diffuseness is not fixed unconditional charge

Take raw absorption of order `2^{-t}`.  Remaining absorption is of the same
order, so `w_t` can stay bounded away from zero while every unconditional
late-stage mass tends to zero.  A source reach floor is additionally needed
before failure of `w_t -> 0` can feed an unconditional charge consumer.

### Vanishing cross-share is not debt-support descent

Conditional occupation mass and positive semantic debt support are different
objects.  No current theorem turns `Pi_s({q})->0` into disappearance of `q`
from the debt support.  Such an implication would require new cap control.

## Source correspondence and missing adapter

The theorem uses existing checked semantic ingredients:

* `quittingTailConditionedValue_eq_terminalValue_div` and
  `abs_quittingTailConditionedValue_sub_singleton_le_weight` in
  `UniformEquilibrium/Quitting/Cycles/PhantomBoundaryConditioning.lean`;
* `quittingRootSequenceSingletonMass` and the terminal-mass identities in
  `UniformEquilibrium/Quitting/AbsorptionPath/
  NormalizedFiniteWindowOccupation.lean`;
* `quittingRootSequenceCollisionMass` and collision concentration identities
  in `UniformEquilibrium/Quitting/AbsorptionPath/
  CollisionConcentration.lean`;
* `normalizedSoloMatrix_eq_soloReward_sub` in
  `UniformEquilibrium/Quitting/Classification/
  PreemptionGateDictionary.lean`; and
* the card-two signs in `FullSupportHardPrincipalDispatch.lean` cited above.

The missing producer is exact and substantial.  No current source adapter is
known to take a Fin4 hard-residual/minimum source and construct one infinite
exact Nash--Bellman tail satisfying all of:

1. eventual support on the selected pair;
2. coordinatewise convergence to a boundary pinned at both singleton rewards;
3. positive eventual absorption and vanishing conditioned mesh; and
4. the two active-start cross-share lower bounds (6)--(7).

Without that adapter, the theorem does not yield terminal approximants, a
uniform-equilibrium payoff, a charged return, or a well-founded regeneration.

## Lean-facing theorem shapes

The local statements should be separated from the source adapter:

```text
twoClock_conditionedCollisionShare_le_tailSup_mesh

conditionedCrossSingletonShare_mul_abs_normalizedSoloMatrix_le

normalizedSoloMatrix_pair_eq_zero_of_twoClockDiffuse_crossShares
```

The final theorem must carry `value -> boundary` explicitly and must quantify
the `p`-active/`q`-share and `q`-active/`p`-share sequences separately.  A
single field saying that both singleton shares occur infinitely often is too
weak.

## Exact next question

Can a card-two Fin4 hard-residual minimum source be converted, without
changing the source table or losing unrestricted-cap provenance, into either:

1. an exact two-clock tail satisfying the four missing adapter properties;
2. terminal approximants or a charged admissible return; or
3. a regenerated source with a strict renewable finite rank?

The theorem above closes the first output once its exact tail is supplied.  It
does not produce that tail.
