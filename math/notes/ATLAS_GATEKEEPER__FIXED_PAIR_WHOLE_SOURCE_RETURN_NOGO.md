# Fixed-pair whole-source return: a prefix-independent join-wall no-go

Author: `ATLAS_GATEKEEPER`

## Status

This is an exact no-go for a broad natural repair class at the collision
whole-source-return seam.

A literal pure pair at the marked row cannot in general be made near-minimal
by changing its pre-mark prefix, delaying it, cap-prefixing it, or changing
its unreachable tail.  If one spectator has a nonnegative membership wall at
that pair, its unrestricted behavioral debt is at least the wall times the
unconditional pair mass.  The estimate is independent of every pre-mark root
and every continuation.

An exact Fin4 table below attains the bound.  It also has a diffuse sequence
converging to a zero-debt joint semantic/law minimum with singleton law mass
one.  The same literal owner-completion operation used by clock compression
gives a sure singleton row, a best-endpoint update gives a sure pair row of
mass one with zero marked owner defect, and a literal minimum-return tail may
be attached.  Nevertheless every such pair source has debt two.  Because its
minimum is zero, this example does not instantiate the positive-minimum
`FinFourMinimumAtomProducer` type.

The regression has global minimum zero, so it does not refute a producer
which uses the hypothesis (D_*>0) essentially.  It does prove that no repair
based only on moving the fixed pure pair deeper, changing its past, or
installing a minimum tail can establish whole-source return.  A valid
positive-minimum proof must either change the marked root/label, prove a
compensating sign relation that excludes the wall, or consume the wall by a
separate semantic theorem.

## 1. Prefix-independent join-wall theorem

Let (I) be finite, let (j,o,i) be distinct players, and let (t) be a date of
an arbitrary behavioral profile (rho).  Assume that the actual live root at
(t) makes (j) and (o) Quit surely.  Put

\[
 m:=\Pr_\rho(\text{the terminal coalition at date }t\text{ is }\{j,o\}).
 \tag{1}
\]

Assume that for some (c\ge0), every possible background containing the two
sure quitters has a nonnegative (i)-join gain, with gain at least (c) on the
literal pair background:

\[
 r_i(A\cup\{i\})-r_i(A)\ge0
 \quad
 \bigl(\{j,o\}\subseteq A\subseteq I\setminus\{i\}\bigr),
 \tag{2}
\]

\[
 r_i(\{j,o,i\})-r_i(\{j,o\})\ge c.
 \tag{3}
\]

Then

\[
 \boxed{d_i(\rho)\ge c m,\qquad D(\rho)\ge c m.}
 \tag{4}
\]

### Proof

Let (i) use the behavioral deviation which copies its prescribed strategy at
every earlier date and Quits surely at date (t).  Its behavior after (t) is
irrelevant.  Couple this deviation with prescribed play.

Every outcome absorbed before (t) is unchanged.  On reaching (t), outcomes
where (i) already Quits are unchanged.  If (i) prescribed Continue, the old
quitter coalition is some

\[
 \{j,o\}\subseteq A\subseteq I\setminus\{i\},
\]

and the deviated coalition is (A\cup\{i\}).  Equation (2) makes every such
payoff change nonnegative.  On the subevent where (A=\{j,o\}), whose
unconditional probability is exactly (m), equation (3) makes the change at
least (c).  Thus this one literal behavioral deviation gains at least (cm).
The unrestricted cap dominates its payoff, proving the first inequality in
(4); nonnegativity of all semantic debts proves the second.

Nothing in the argument assumes stationarity, finite support, a particular
tail, or Nash behavior before the marked date.  It permits arbitrary
behavioral strategies at every earlier date and arbitrary actions of all
spectators at the marked root.

### Positive-minimum consequence

Let (D_*) be the global semantic-debt minimum.  Every family of actual
profiles satisfying the same wall with

\[
 \inf_n m_n\ge\lambda>0
\]

obeys

\[
 \liminf_nD(\rho_n)\ge c\lambda.
 \tag{5}
\]

Consequently, whenever

\[
 c\lambda>D_*,
 \tag{6}
\]

no modification of the pre-mark chronology or the post-mark tail which
retains that pure pair and mass floor can satisfy the missing whole-source
return

\[
 D(\rho_n)\longrightarrow D_*.
\]

This is a genuine obstruction, not a failure of a particular Lipschitz
estimate.  It is witnessed by one actual unrestricted behavioral deviation
at every profile.

## 2. Sharp Fin4 regression

Let the players be

\[
 j=0,\qquad o=1,\qquad i=2,\qquad h=3.
\]

Define a reward table bounded by one as follows.  Players (j) and (h) always
receive zero.  Player (o) receives

\[
 r_o(S)=\mathbf 1_{\{j,o\}\subseteq S}.
 \tag{7}
\]

Player (i) receives

\[
 r_i(S)=
 \begin{cases}
 1,&\{j,o,i\}\subseteq S,\\
 -1,&\text{otherwise}.
 \end{cases}
 \tag{8}
\]

Thus (i)'s membership gain is exactly two when both (j) and (o) are already
in the quitting coalition, and zero on every other background.  Equations
(2)--(3) hold with (c=2), and the estimate (4) is sharp.

### Diffuse singleton minimum sequence

For (N\ge1), let (\sigma_N) prescribe that (j) chooses uniformly among dates
(0,\ldots,N-1), while (o,i,h) play Never.  Prescribed play terminates at the
singleton (\{j\}) with probability one, and

\[
 U(\sigma_N)=(0,0,-1,0).
 \tag{9}
\]

The only positive debt is (o)'s.  Quitting at a fixed date ties (j) with
probability at most (1/N), while every other outcome gives (o) zero.  Hence

\[
 B_o(\sigma_N)=\frac1N,
 \qquad
 D(\sigma_N)=\frac1N.
 \tag{10}
\]

Player (i) receives (-1) from every finite deviation against an opponent
profile in which (o) Never Quits; Never also receives (-1), because (j)
stops almost surely.  Thus (B_i(\sigma_N)=-1) and (d_i(\sigma_N)=0).

The semantic/law pairs converge to a carrier point (X_*) with

\[
 U(X_*)=B(X_*)=(0,0,-1,0),
 \qquad
 \mu_*(\{j\})=1,
 \qquad
 D(X_*)=0.
 \tag{11}
\]

The global minimum is indeed zero: the all-Never profile has zero payoff and
zero debt (player (i) can choose Never rather than take its negative solo
reward).

### Literal owner compression and the pair target

Choose any finite marked date (t).  Copy an arbitrary finite pre-mark word,
make (j) Quit surely at (t), and attach (\sigma_N) after the row's
all-Continue outcome.  Let (\beta_N) be this singleton profile.  Its marked
singleton has mass one if the pre-word is all Continue, and its literal tail
semantic pair is (\operatorname{Sem}(\sigma_N)).

At the marked singleton, (o)'s unique better endpoint is Quit: it changes its
payoff from zero to one.  Make that one-date update and call the result
(\rho_N).  Then

\[
 \Pr_{\rho_N}(\{j,o\}\text{ at }t)=1,
 \tag{12}
\]

the marked coordinate defect of (o) is zero, and the literal post-row tail is
still (\sigma_N), hence converges to (X_*).

But (i)'s prescribed payoff is (-1), while Quitting at (t) produces the
triple (\{j,o,i\}) and payoff (1).  Therefore

\[
 d_i(\rho_N)=2,
 \qquad
 D(\rho_N)=2.
 \tag{13}
\]

This remains true after arbitrary changes before (t) which retain pair mass
one; more generally (4) gives (D\ge2m) at retained pair mass (m).  It also
remains true for every attached tail, because the two sure quitters make the
tail unreachable even after a unilateral deviation by (i).

Thus the exact packet passport

\[
 \boxed{
 \begin{array}{l}
 \text{fixed pure pair mass},\\
 \text{zero marked defect for the routed owner},\\
 \text{literal tail returning to the selected minimum},\\
 \text{arbitrarily deep or arbitrary pre-mark prefix}
 \end{array}}
 \tag{14}
\]

does not imply whole-source return.  The cross-coordinate cap leakage can
attain the full reward oscillation times the retained pair mass.

## 3. Relation to the reviewed Quit packet

The owner-clock minimum-return Quit packet has precisely the geometric shape
used in the theorem: the singleton owner (j) and packet owner (o) Quit surely
at the marked row, and it retains a fixed pair atom.  Hence every table-level
join wall of the form (2)--(3) applies to its literal sources without any
additional provenance theorem.

The current packet hypotheses do not exclude such a wall or bound its charge
by (D_*).  They also provide no negative membership gain on another marked
background which would cancel (4).  Therefore the following broad repair
principle is false:

> A fixed pure pair packet with a minimum-return tail can always be made
> near-minimal by inserting, deleting, or changing finitely many roots before
> the marked row while retaining its pair mass.

The theorem covers arbitrary finite or infinite pre-mark behavior, not just a
particular graft.  What it does **not** exclude is a repair which changes the
marked pure-pair geometry, routes the atom to a different terminal, or uses
the full positive-minimum hard residual to prove a compensating sign identity.

## 4. Formalization handoff

The generic theorem can be stated using:

- the literal one-date pure-Quit update for (i);
- `quittingTerminalPayoff_stagePureEndpointDeviation_sub_eq_liveMass_mul`;
- the product-root absorbing contribution expanded over coalitions; and
- the definition of unrestricted terminal debt as the cap minus prescribed
  payoff.

A convenient first declaration is:

```lean
theorem terminalDebt_ge_stagePairMass_mul_of_joinWall
    (hjo : root j = PMF.pure true ∧ root o = PMF.pure true)
    (hwall : ∀ A, {j,o} ⊆ A → i ∉ A →
      c ≤ reward ⟨insert i A, ...⟩ i - reward ⟨A, ...⟩ i)
    (hc : 0 ≤ c) :
    c * quittingStageCoalitionMass reward profile stage pair ≤
      quittingTerminalDeviationDebt reward profile i
```

For the weaker hypotheses (2)--(3), expand the root expectation and separate
the literal pair term from the other nonnegative terms.

The concrete Fin4 regression should then define the table (7)--(8), the
uniform deadline profiles, and the pure-pair profiles, and prove (10)--(13)
by the existing pure-time best-response and sure-exit reductions.

## Declarations inspected

- `FinFourOwnerCompressedSingletonEndpoint` and its literal profile, tail,
  stage-mass, and own-cap identities in
  `Research/Quitting/FinFourProducerAtlas/MinimumSingletonClockCompression.lean`;
- `QuittingStageAtomConcentratedPacketAdapter`,
  `.targetTail_eq_sourceTail`, `.sourceStageMass_le_targetStageMass`, and
  `.ownerMarkedDefect_eq_zero` in
  `Research/Quitting/PositiveStageAtomConcentratedPacket.lean`;
- `quittingTerminalPayoff_stagePureEndpointDeviation_sub_eq_liveMass_mul` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauLocalizedOtherDefect.lean`;
- `quittingTerminalSemanticDebt_stageBestEndpoint_eq_sub_gain` and the routed
  stage-mass identities in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLiveWeightedCollisionTransfer.lean`;
- the exact phase-switch deviation split in
  `UniformEquilibrium/Quitting/Boundary/Repair/CollisionRepairCharacterization.lean`;
- `QuittingConcentratedCollisionMinimumResidual` in
  `Research/Quitting/ConcentratedSingleton/StrategicDispatch.lean`; and
- the checked three-role source-return hypothesis in
  `Research/Quitting/ConcentratedCollisionFourRoleMonodromy.lean`.

## Nonclaims

- The regression has (D_*=0); it is not a quitting-game counterexample.
- The theorem does not prove that the reviewed positive-minimum packet always
  has a join wall satisfying (6).
- It does not consume a positive join wall when (c\lambda\le D_*).
- It does not rule out a genuinely source-dependent repair which changes the
  marked root or proves cap cancellation from hard-residual data.
- It does rule out tail replacement, delay, and arbitrary pre-mark damping as
  universal repairs of a fixed pure pair passport.
