# Independent review of the positive-Never unique-all-Continue actualizer boundary

Reviewer: **CODEX_RAMSEY**  
Source: [`CODEX_MINER__POSITIVE_NEVER_UNIQUE_ALLCONTINUE_ACTUALIZER_BOUNDARY.md`](../notes/CODEX_MINER__POSITIVE_NEVER_UNIQUE_ALLCONTINUE_ACTUALIZER_BOUNDARY.md)  
Verdict: **REVISE to PASS after the fixed-half restoration repair**  
Disposition: **internal only**.  After repair, this is a valid
stronger-premise no-go for the proposed finite-clock actualization consumer.
It does not produce a `FIN4_BT_QUESTION` output.

## Claims checked

The input is an off-minimum joint semantic/law carrier point `(y,lambda)`
with

```text
D(y)>D_*>0,   q=lambda(Never)>0,
```

whose exact cap-root correspondence against `y.2` is the singleton
`{allContinue}`.  The note claims:

1. source-matched finite-clock actual profiles converge jointly to
   `(y,lambda)`;
2. if every singleton inequality is strict, all exact cap roots at all
   sufficiently late actualizers are all Continue, so every compatible paid
   cap chronology is literally inert;
3. a late release of the positive-Never mass gives a fixed actual debt
   descent or a source-matched three-label recipient transfer; and
4. the descent can be mixed back with the source to restore positive Never,
   but the passport shrinks too quickly to give a maintained rank or
   cumulative-charge consumer.

The first three items pass.  Item 4 has the correct qualitative conclusion
but uses an unnecessarily weak estimate and makes a false statement about
the best guaranteed renewal scale.

## Independent check

### 1. Law-matched finite-clock actualizers

Joint-carrier membership gives actual profiles `rho_n` with

```text
(Sem(rho_n),Law(rho_n)) -> (y,lambda).
```

Apply common-quantile compression to `rho_n` at a diagonal level tending to
infinity.  The checked two-sided payoff transport in
`Research/Quitting/EscapeAwareQuantileClockHierarchy.lean` gives uniform
convergence of both prescribed payoffs and unrestricted behavioral caps.
Thus `Sem(sigma_n)->y`.

The law assertion also passes.  Each marginal Never atom is preserved
exactly by `quittingQuantileClockCompressedLaws_none`, so the joint Never
coordinate is preserved relative to `rho_n`.  Off the common bad-cell event,
the quotient preserves the earliest finite coalition exactly; the product
bad-cell mass is bounded uniformly by the pair-collision budget in
`EscapeAwareQuantileClockCollision.lean`, which tends to zero.  There are
only finitely many terminal outcome coordinates, hence

```text
Law(sigma_n)->lambda,   Law(sigma_n)(Never)->q.
```

This is genuinely stronger than semantic finite-clock density and remains
source matched to the supplied joint point.  It still does not attain the
limit point.

### 2. Strict singleton slack and literal inertness

All Continue is exact at `y.2`, so

```text
kappa=min_i (y.2_i-r_i({i})) >= 0.
```

If `kappa>0`, apply
`exists_open_linearAbsorptionDefect_of_compact_strictAllContinue` from
`UniformEquilibrium/Quitting/Root/StrictAllContinueBasinLinearAbsorptionDefect.lean`
to the singleton compact set `{y.2}`, with any `0<delta<=kappa`.  Compactness,
strict singleton separation, and uniqueness of the exact root are exactly
the theorem's hypotheses.  It yields an open neighborhood `N` and `c>0`
such that

```text
c*Absorption(root) <= RootNashDefect(V,root)
```

for every `V in N` and every product root.  Since the actualizer cap vectors
eventually lie in `N`, every exact root has zero absorption and is literally
all Continue.

The induction through a compatible paid cap lift is valid: an exact
all-Continue prefix fixes the terminal semantic pair by the singleton/cap
inequalities and fixes the terminal **outcome law** by its affine prefix
formula.  The next root therefore faces the same cap vector and is again all
Continue.  This proves zero absorption, zero charge, and zero cap
displacement at every finite stage for any exact-root selection, not merely
for the maintained selector.

Since `D(Sem(sigma_n))->D(y)>D_*`, these sources are uniformly separated
from both the minimum fiber and the terminal-approximate-Nash region.  For
Fin4, terminal exploitability at most `epsilon_n` would give total debt at
most `4 epsilon_n`, contradicting `D_*>0`.  Thus finite-clock actualization
does not consume the strict branch; it literalizes its inertness.

### 3. Exact late release and constants

The witness supplies a fixed owner `a` with

```text
s_a=r_a({a})>=Gamma.
```

Choose `K_n` after every finite atom of `sigma_n` and move only `a`'s
remaining Never mass to `K_n`.  Every path except the old joint-Never path
has the same terminal outcome; the old joint-Never path becomes singleton
`{a}`.  Since `a`'s cap depends only on its opponents,

```text
g_n=U_a(tau_n)-U_a(sigma_n)=s_a q_n,
d_a(tau_n)-d_a(sigma_n)=-g_n.
```

Writing `T_n` for the sum of the other three debt changes gives the exact
identity

```text
D(tau_n)-D(sigma_n)=-g_n+T_n.
```

The split at `-g_n/2` is exhaustive.  In the descent arm it gives
`Gamma*q/4`; otherwise `T_n>Gamma*q/4`, and a fixed one of three opponents
gets more than `Gamma*q/12` after subselection.  The reviewed finite-support
decoder loses factors two and four, giving the displayed `Gamma*q/24` and
`Gamma*q/48` atoms.  All inequalities and strict/equality conventions are
correct.

Corollary 4.2 is also correct.  Global minimality gives

```text
T_n >= g_n-(D(sigma_n)-D_*),
```

whose right side tends to `H=s_a*q-(D(y)-D_*)`.  If `H>0`, eventual `H/2`
and the three-recipient pigeonhole yield `H/6`, followed by `H/12` or
`H/24` in the two decoder arms.  This is a real same-source quantitative
narrowing, but the decoded row is still not a Nash--Bellman edge.

### 4. Mandatory repair: fixed half-mixture restoration

Proposition 5.1 proves a true weak statement, but its subsequent claim that
the only guaranteed restoration weight is `O(q)` and that the next Never
mass can therefore be `O(q^2)` is false under the already checked stopping-law
mixture theorem.

Let `upsilon_n` mix only player `a`'s source law in `sigma_n` and late-capped
law in `tau_n`, with **source weight `theta=1/2`**.  The checked declaration

```text
quittingTerminalSemanticDebt_stoppingLawMixture_le
```

in
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawDebtConvexity.lean`
is coordinatewise and applies to unrestricted behavioral caps.  Summing it
gives

```text
D(upsilon_n)
  <= (1/2)D(sigma_n)+(1/2)D(tau_n)
  <= D(sigma_n)-Gamma*q/8
```

eventually in the descent arm.  At the same time the literal product event
gives

```text
Law(upsilon_n)(Never)=(1/2)q_n -> q/2>0.
```

Thus the note should replace (5.2)--(5.4) and their proof with the stronger,
simpler fixed-half statement.  No reward-Lipschitz loss or assumption `M>0`
is needed.  The endpoint ordering in the mixture convention should be stated
so that the source coefficient is exactly `1/2`.

This repair does **not** turn the result into a conjecture consumer.  Under
repetition the certified masses may now shrink geometrically,

```text
q_{t+1}=q_t/2,
```

and the guaranteed drops are proportional to `q_t`; their sum is still
finite.  More importantly, after each restoration neither the cap-ray
proportionality, the unique-root/strict-slack hypothesis, nor the original
rectangle labels are preserved.  Therefore no iteration of the *same full
source-produced problem* and no natural-valued rank follows.  The precise
nonclaim should be geometric/Zeno loss, not an asserted quadratic loss.

### 5. Tight and graft boundaries

When `kappa=0`, uniqueness at the point does not yield the open linear basin.
Indeed a tight player can support small nearby absorbing roots unless further
cross-row signs exclude them.  The strict/tight split is exact.

The note should phrase its all-nonproper conclusion at the level actually
proved: eventually every actualizer marginal Never probability is bounded
below by (say) `q/2`, because their product tends to `q>0`.  A complete
marginal-law limit is not selected in Section 2; if one is later selected in
the stopping-law compactification, its Never coordinates inherit that lower
bound.

The repaired 6AL audit is accurate.  The late-capped endpoint supplies a
sure finite clock after the cutoff, hence can supply the endpoint-deleted
reach field.  It does not supply 6AJ--6AK's two near-killed **source** labels:
positive joint Never gives a fixed positive all-source-Never event after
deleting either one of those labels.  The graft remains unavailable for this
source-side reason.

## Conjecture-facing disposition

After the half-mixture repair, the note proves a useful stronger-premise
no-go:

```text
off-min positive-Never unique-allC point + strict singleton slack
  -> law-matched finite-clock actual sources
  -> every exact cap chronology literally inert
  -> no terminal approximants and no cap return from this actualization.
```

The late release adds a genuine actual descent-or-three-label transfer, and
the descent can be restored to positive Never with a fixed half-mixture.  But
the operation leaves the invariant cap ray, does not preserve the full
rectangle/tangent input, and gives neither a uniform nonvanishing charge nor
a well-founded regenerated rank.  The singleton-tight arm is also open.

## Verdict

**REVISE to PASS.**  Sections 2--4 and the strict-basin no-go pass.  The
current source has replaced Proposition 5.1's `O(q)` source weight and
quadratic-passport discussion by the exact half-release fork, explicitly
cited coordinatewise debt convexity, and narrowed the marginal-law limit
wording as required.  The result genuinely rules out finite-clock
actualization as a consumer in the strict branch, but it does not meet a
`FIN4_BT_QUESTION` output.

## Delta verification of the repair

The repaired Proposition 5.1 now states the literal half release itself:

```text
Never(upsilon_n)=q_n/2,
U_a(upsilon_n)-U_a(sigma_n)=s_a q_n/2.
```

Repeating Theorem 4.1's accounting with this partial target yields either
debt descent `Gamma*q/8`, or one of three recipients gains more than
`Gamma*q/24`, followed by the decoder scales `Gamma*q/48` and
`Gamma*q/96`.  These constants are correct.  In the full-target descent arm,
the displayed application of
`quittingTerminalSemanticDebt_stoppingLawMixture_le` independently recovers
the same `Gamma*q/8` descent.  The text now claims only geometric decay and
finite total certified descent, and expressly denies preservation of the
ray, unique-root basin, rectangle, or early label.  Section 6 selects a
compact marginal-law subsequence before speaking about limiting clocks.
All requested repairs are therefore present; no objection remains in the
stated internal scope.
