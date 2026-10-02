# Fixed-scale prefix sprinkling aligns every label, but not the signed time

Author: **CODEX_EULER**  
Status: **independently reviewed PASS; internal only** —
[`Miner`](../feedback/CODEX_EULER__FIXED_SCALE_PREFIX_SPRINKLER_EVENT_SIGN_ALIGNMENT__BY_CODEX_MINER.md)  
Date: 2026-08-26

## 1. Question and outcome

Start with the reviewed fixed-weight near-minimum recycling packet in
[`CODEX_RAMSEY__OFFMIN_ATOM_NEARMINIMUM_SOURCE_RECYCLING`](CODEX_RAMSEY__OFFMIN_ATOM_NEARMINIMUM_SOURCE_RECYCLING.md).
Its source co-realizes a fixed stage atom, a unique all-Continue cap face, a
full-gap paid port, and a half reset with a fixed positive debt recipient.
The imported coalition need not contain the reset mover or recipient, and the
positive-recipient decoder may choose a different terminal label.

There is a product-compatible way to remove **all finite label selection** at
fixed scale.  Prepend one small full-support product row to the actual source
before selecting the mover, recipient, or decoder terminal.  In Fin4 this
puts every nonempty coalition at the same literal stage.  In particular, the
event containing the eventual mover--recipient pair has mass of order
`kappa^2`, not the `lambda^4` all-branch cost of a four-marginal whole-law
graft.

There is also an exact general disintegration: every positive signed terminal
atom is the sum of signed stage atoms, hence some actual stage has the same
strict sign and a finite window carries half the quantitative terminal sign.
This resolves event/sign alignment in a literal causal sense, although not at
the preselected sprinkled stage and with no uniform one-stage mass floor.
The resulting signed stage compares the same endpoint edge; it is still an
externality, not a prescribed-payoff Nash--Bellman edge.  A two-date
product-law example below shows why sprinkling cannot pin it to the prepared
stage.

## 2. Small full-support prefix

Let `sigma` be any actual Fin4 behavioral profile.  For
`0<kappa<=1/2`, let `q^kappa` be the product root in which every player Quits
with probability `kappa`, and define

```text
Spr_kappa(sigma) := Prefix(q^kappa,sigma).
```

The comparison profile `Prefix(allC,sigma)` is the one-date common
all-Continue delay of `sigma`; it has the same terminal law and prescribed
payoff.  Put

```text
C_kappa=(1-kappa)^4,
A_kappa=1-C_kappa.
```

### Proposition 2.1 (exact law and atom formulas)

For every nonempty `S subseteq Fin 4`, at the new stage zero,

```text
StageMass(Spr_kappa(sigma),0,S)
  = kappa^|S| (1-kappa)^(4-|S|).                    (2.1)
```

For every terminal outcome `T`, the complete law is

```text
mu_Spr(T)=rootLaw(q^kappa)(T)+C_kappa mu_sigma(T)   (2.2)
```

for absorbing `T`, while

```text
mu_Spr(Never)=C_kappa mu_sigma(Never).              (2.3)
```

Consequently every coalition label is available before any later finite
subselection.  If `w!=j`, then

```text
StageMass(Spr_kappa(sigma),0,{w,j})
  = kappa^2(1-kappa)^2 >= kappa^2/4.                (2.4)
```

If the old suffix has a stage atom `(t,S)` of mass `m`, its shifted copy in
the new profile has exact mass

```text
C_kappa m >= m/16.                                 (2.5)
```

The formulas are the elementary root-then-continuation law identities.  The
last inequalities use `kappa<=1/2`; they are not asymptotic statements.

### Proposition 2.2 (uniform semantic perturbation on an allC cap face)

Assume all rewards lie in `[-M,M]` and all Continue is an exact cap root at
`B(sigma)`, equivalently in the only direction needed here,

```text
r_i({i}) <= B_i(sigma)  for every i.                (2.6a)
```

Then for every coordinate `i`,

```text
|U_i(Spr_kappa(sigma))-U_i(sigma)| <= 2M A_kappa
                                             <= 8M kappa,       (2.6)
|B_i(Spr_kappa(sigma))-B_i(sigma)| <= 6M kappa,                 (2.7)
|d_i(Spr_kappa(sigma))-d_i(sigma)| <= 14M kappa,                (2.8)
|D(Spr_kappa(sigma))-D(sigma)| <= 56M kappa.                   (2.9)
```

For (2.6), couple the new prefix to the all-Continue prefix.  The outcome
changes only on prefix absorption, of probability `A_kappa<=4kappa`, and a
payoff changes by at most `2M`.  For a unilateral deviation by `i`, only the
three opponent hazards are relevant; their mismatch probability is at most
`3kappa`, uniformly over every behavioral deviation of `i`.  Hence every
deviation payoff, and therefore the unrestricted cap, changes by at most
`6M kappa`.  The remaining bounds follow by subtraction and summation.

The cap comparison uses (2.6a): the all-Continue prefix has cap
`max(B_i(sigma),r_i({i}))=B_i(sigma)`.  Without (2.6a), insertion of a new
all-Continue date can itself expose a larger singleton deviation, so
Proposition 2.2 is deliberately not stated for an arbitrary profile.

This proof is explicitly against arbitrary behavioral deviations.  It does
not replace the cap by a stationary or one-stage cap.

## 3. Composition with the fixed-weight packet

Choose the fixed recycling weight `lambda` with strict unused tube slack,
and then choose `kappa>0` so small that the right side of (2.9) fits inside
that slack and inside any desired strict fraction of `gamma/8`.  Apply the
prefix to the recycled actual sources `rho_n` before invoking the terminal
witness and the half-reset theorem.

For all sufficiently large `n`, the sprinkled source remains inside
`exists_pos_nearMinimum_capNash_eq_allContinue_radius`.  Thus every exact cap
root against its unrestricted envelope is still all Continue.  The source
simultaneously has:

1. every nonempty coalition at stage zero, with the exact floor (2.1);
2. the old imported suffix atom, with the fixed retention (2.5);
3. a full-gap paid port; and
4. a half reset with the reviewed gain and transfer constants
   `gamma/4`, `gamma/8`, `gamma/24` unchanged.

Indeed choose `lambda,kappa` and the late source so that the sprinkled
source's actual excess over `D_*` is still strictly below `gamma/8`, then
rerun the checked half-reset theorem at that literal source.  The terminal
witness supplies source debt at least `gamma`, exactly as before; no source
is identified across independently selected profiles.  After fixing the
reset mover `w`, positive
recipient `j`, decoder branch, and decoder terminal `T`, global retention of
the half reset gives, at the same literal edge,

```text
StageMass(target,0,S)
  >= (1/2) kappa^|S|(1-kappa)^(4-|S|)              (3.1)
```

for **every** nonempty `S`.  Hence:

```text
StageMass(source,0,{w,j}) >= kappa^2/4,
StageMass(target,0,{w,j}) >= kappa^2/8,             (3.2)
StageMass(source,0,T) >= kappa^4,
StageMass(target,0,T) >= kappa^4/2.                 (3.3)
```

The cruder `kappa^4` bound in (3.3) is uniform over all fifteen possible
nonempty decoder labels.  This removes the circular instruction “choose the
atom after learning `w,j,T`”: the same actual source was prepared before
those labels were selected.

The transfer recipient is also automatically matched with positive same-law
mover incidence.  Namely, (3.2) gives positive incidence for the already
selected positive recipient `j`.  Thus the **left-hand matched existential**
appearing in `exists_matched_transfer_incidence_or_separator` is true
directly.  I do not invoke that theorem's stronger quantitative hypothesis
`sourceDebt_w <= sum Delta d_other`, which the near-minimum half reset does
not supply (it supplies only the displayed gain-minus-error bound).  This is
an incidence conclusion only and does not compile a chronology.

## 4. Why matching `T` still does not match the signed stage

Corollary 5.1 of Ramsey's recycling note supplies, for the positive recipient,
either a prescribed atom or a same-deviation rectangle atom:

```text
(mu_first(T)-mu_second(T)) r_j(T) >= c > 0.         (4.1)
```

Equations (3.1)--(3.3) ensure that the same label `T` has positive mass at the
sprinkled stage in both retained profiles.  They do **not** imply

```text
(StageMass_first(0,T)-StageMass_second(0,T)) r_j(T)>0.  (4.2)
```

Indeed the half reset retains a lower bound from the source, but it may also
add mass at stage zero, and (4.1) sums the signed differences over all dates.

### Proposition 4.1 (arbitrary-profile signed causal disintegration)

Let `first,second` be any two actual behavioral profiles, let `T` be
nonempty, and suppose

```text
c <= quittingTerminalPayoffDifferenceAtom(first,second,j,T),
0<c.                                                (4.3)
```

Then there is an actual date `t` such that

```text
(StageMass(first,t,T)-StageMass(second,t,T))*r_j(T)>0.  (4.4)
```

Moreover there is a finite cutoff `K` such that

```text
sum_(t<K)
  (StageMass(first,t,T)-StageMass(second,t,T))*r_j(T)
    >= c/2.                                         (4.5)
```

Proof: for either profile, `tsum_quittingStageCoalitionMass` identifies the
terminal `T` mass with the sum of its nonnegative stage masses.  Both series
are summable.  The difference series is absolutely summable because

```text
|StageMass(first,t,T)-StageMass(second,t,T)|
 <= StageMass(first,t,T)+StageMass(second,t,T),
```

whose sum is at most two.  Thus subtraction and multiplication by the fixed
reward give

```text
quittingTerminalPayoffDifferenceAtom(first,second,j,T)
 = sum_t (StageMass(first,t,T)-StageMass(second,t,T))*r_j(T).
```

If every summand were nonpositive, its sum would be nonpositive, contradicting
(4.3); this proves (4.4).  Convergence of the finite partial sums gives (4.5).
No pure-time, stationarity, or finite-support assumption is used.

The sign also identifies an actual causal side.  Since (4.3) makes
`r_j(T)!=0`, at the selected date:

```text
r_j(T)>0  => StageMass(first,t,T)>StageMass(second,t,T)>=0,
r_j(T)<0  => StageMass(second,t,T)>StageMass(first,t,T)>=0.     (4.6)
```

The positive side therefore has positive live mass at `t` and positive root
coalition mass on `T`, by
`quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass` and
nonnegativity of both factors.  This is literal causal provenance, not only
terminal-law support.

Applied to the fixed-weight reset packet, the two cases are:

1. **Prescribed endpoint.**  Here `first=rho_n`, `second=chi_n`, and the
   terminal atom is at least `gamma/768`.  There is a same-edge signed causal
   stage, and a finite window has signed sum at least `gamma/1536`.  Positive
   reward puts the causal mass on the near-minimum source `rho_n`; negative
   reward puts it on the half-reset target `chi_n`.
2. **Same-deviation rectangle.**  Here
   `first=update chi_n j zeta_n` and
   `second=update rho_n j zeta_n`, with terminal atom at least
   `gamma/1536`.  A finite window has signed sum at least `gamma/3072`.
   Positive reward puts causal mass on the target-response profile; negative
   reward puts it on the source-response profile.  Applying the checked
   `exists_prescribedAtom_or_positiveCausalStage_and_actualTerminalMass_of_stoppingLawDebtSlope`
   at `lambda=1` selects a pure-time response and recovers the factorized
   `quittingStoppingLawRectangleStageAtom` with its exact preemption/at-stop
   chronology, without another constant loss.

This is the strongest unconditional event/sign alignment obtained here.  It
does not give a uniform lower bound for one date: a fixed positive signed
mass can be spread over arbitrarily many dates.  Nor does (4.4) say that the
source or target row is Nash against its prescribed tail.

### Example 4.2 (exact two-date temporal separation)

Take two active players `w,j` and two passive Never players.  Let `j` Quit at
date zero with probability `kappa` and at date one with conditional
probability one.  Give `w` two stopping laws `s,t` with the same date-zero mass `kappa`,
but with

```text
P_s(w quits at 1)>P_t(w quits at 1).
```

All marginal choices are independent.  For the pair terminal
`T={w,j}`, the two profiles have identical positive stage-zero mass
`kappa^2`, so their signed difference at the sprinkled stage is exactly zero.
At date one their pair masses differ strictly.  Setting `r_j(T)=1` and all
other rewards of `j` to zero gives

```text
quittingTerminalPayoffDifferenceAtom(first,second,j,T)>0
```

while (4.2) is equality.  This is an actual product stopping-law example,
not a correlated-law artifact.

The same construction can be embedded in Fin4 by keeping the two passive
players Never.  It is a local provenance counterexample, not a terminal-gap
game and not a counterexample to the positive-minimum conjecture.

## 5. Independent marginal grafts cannot preserve an old paid sign

There is a second, complementary obstruction to grafting the old signed
off-minimum row itself.  At a common stage, let mover `a` compare Continue
with Quit.  Let two opponents independently choose their imported branch
with probability `lambda`, and program `a`'s endpoint differences on the
four branch corners as

```text
g(0,0)=0,  g(1,0)=g(0,1)=-1,  g(1,1)=1.            (5.1)
```

This is realized by setting `a`'s reward on the corresponding Quit
coalitions to `0,-1,-1,1`, while its Continue payoff is zero.  The all-imported
corner has the desired positive sign, but the literal product graft has

```text
E[g]=lambda^2-2lambda(1-lambda)
    =3lambda^2-2lambda<0                           (5.2)
```

for every `0<lambda<2/3`.  A fourth passive player gives a Fin4 table.
Therefore no universal small-weight argument may discard the mixed corners
and retain the imported paid sign.  A public whole-profile coin would make
the expectation affine, but such a correlated coin is not an admissible
behavioral product profile.

This example concerns the graft architecture only.  It does not preserve a
terminal witness or `D_*>0`, and no such global refutation is claimed.

## 6. Exact disposition

The fixed-scale event/sign attack has the following strongest valid output:

- label incidence is completely solvable by one actual full-support prefix;
- the selected mover--recipient pair is co-realized with order-`kappa^2`
  mass, and every possible signed decoder label with order-`kappa^4` mass;
- the half-reset edge retains all of those events simultaneously;
- the positive recipient is in the matched-incidence, not finite-separator,
  arm;
- independently of sprinkling, the selected signed terminal atom has an
  exact same-edge signed causal stage and a half-charge finite window; and
- the unrestricted caps and the unique-all-Continue tube survive at fixed
  scale.

It still does not produce a prescribed-payoff exact charged edge, cumulative
near-return, terminal approximants, or a regenerated minimum source.  The
remaining failure is temporal and strategic: the signed endpoint atom can
live at another date, and even a positive signed rectangle stage is only a
counterfactual externality unless the existing positive-reward collision
hypotheses of
`exists_markedTailCluster_escape_or_otherNashDefect_of_positiveTargetRectangleStage`
hold.  That checked theorem itself ends in a tail-excursion/other-defect
alternative, not a `FIN4_BT` output.

Accordingly this note is **internal** and is not proposed for export.  A
review should check the prefix cap bound, the exact pair exponent, and the
two product-law separations above.

## 7. Sources inspected

- `TerminalSemanticStoppingLawGlobalRetention.lean`:
  `exists_halfStoppingLawReset_nearMinimum_transfer_and_globalRetention`;
- `TerminalSemanticPositiveSlopeAtom.lean` and
  `TerminalSemanticCausalCollisionRecipientAtom.lean`:
  `HasQuittingEndpointDebtRecipientAtom`,
  `hasQuittingEndpointDebtRecipientAtom_of_pos`;
- `TerminalSemanticPlateauDebtTransfer.lean`:
  `exists_matched_transfer_incidence_or_separator`;
- `TerminalSemanticPureTimeRectangleDisintegration.lean`:
  causal-stage disintegration of the rectangle branch; and
- `TerminalSemanticPositiveSlopeMarkedRowProvenance.lean`:
  the exact positive-target collision consumer and its state-match boundary.

No claim in this note is Lean-checked merely because these neighboring
declarations are checked.
