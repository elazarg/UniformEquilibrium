# Review of conditioned atom-clock reprojection by `CODEX_NOETHER`

Reviewed note:
[`CODEX_CEDAR__CONDITIONED_ATOM_CLOCK_REPROJECTION.md`](../notes/CODEX_CEDAR__CONDITIONED_ATOM_CLOCK_REPROJECTION.md),
revised Propositions 1--2.

## Verdict

**VALID ordinary mathematics.**  The nonsemantic-candidate revision removes
the original circularity.  Proposition 1's prescribed/cap Lipschitz laws hold
for arbitrary ambient pairs, including max-branch switches.  Proposition 2
uses only exact within-block candidate recursion, summable seam prices, the
checked arbitrary-pair secant, literal two-label clocks, and the stated
boundedness/nonnegativity assumptions.  I found no hidden carrier-membership,
endpoint-Nash, or actual-small-debt premise.

This is a conditional certificate adapter, not an actual-data producer.  The
unproved conjecture-facing step is exactly the simultaneous production of
bounded nonnegative artificial Bellman blocks, summable payoff/cap seams, a
small first artificial debt, and two persistent labels from the atom/reset
geometry.

I did not run Lean and claim no `L`, `A`, or `C` seal.

## 1. One-row pair dependence

Write an arbitrary pair as `X=(u,b)`, where `b` is the envelope coordinate,
not the debt.  The first coordinate of
`quittingTerminalSemanticPrefix reward q X` is the root successor payoff.
Only the all-Continue event reads `u_i`, so for two pairs

```text
|F_q(X).1_i-F_q(Y).1_i|=J(q)|u_i-u'_i|.
```

The envelope coordinate has the exact form

```text
max(Q_i(q), C_i(q)+O_i(q)b_i).
```

The Quit branch is continuation-independent; after player `i` Continues,
only the all-opponents-Continue event reads `b_i`.  Since `O_i(q)>=0`, the
map `z |-> max(Q,C+O_i z)` is `O_i`-Lipschitz even when the active max branch
switches.  Subtracting the prescribed coordinate gives

```text
|debt(F_q(X))_i-debt(F_q(Y))_i|
 <=J(q)|u_i-u'_i|+O_i(q)|b_i-b'_i|.
```

Thus the coarser seam prices `A_i` and `A_i+B_i` are valid, including the
all-Continue root where the cap mismatch can pass with coefficient one.  No
semantic-carrier or Nash property of `X,Y` was used.

## 2. Seam orientation

At the last row of block `k`, exact donated recursion gives

```text
X_(k,N_k-1)=F_q(X_(k,N_k)).
```

The concatenated candidate successor at that same row is instead
`X_(k+1,0)`.  Therefore the actual candidate defects are exactly

```text
prescribedDefect
 =F_q(X_(k,N_k)).1-F_q(X_(k+1,0)).1,

directDebtDefect
 =debt(F_q(X_(k,N_k)))-debt(F_q(X_(k+1,0))).
```

This is the orientation bounded by Proposition 1.  At internal rows the two
successors coincide and both defects vanish.  An interval beginning or ending
inside a block merely selects a subset of the seam indices; it never repeats
a seam.

## 3. Generated secants need no candidate realization

For a global row and player, apply
`exists_quittingTerminalSemanticPrefix_secant`
(`UniformEquilibrium/Quitting/Debt/Dynamic/ChronologicalDebtShadowing.lean`)
with

```text
first  = artificial candidate successor pair,
second = literal semantic pair of the actual next suffix.
```

The actual current semantic pair is the prefix of `second` by the displayed
root.  The theorem therefore reads

```text
actual current cap-candidate-prefix cap
 =secant*(actual next cap-candidate next cap),
```

which is precisely `secant_generated`.  Its statement quantifies over
arbitrary `QuittingTerminalSemanticPair`s and gives
`0<=secant<=opponentContinue`; there is no carrier-membership premise.  The
revised artificial initial pair is therefore legitimate.

## 4. Every certificate field

The first seam series gives, for every player, start, and finite length,

```text
|sum prescribedDefect|<=sum_selected_seams A<=eta.
```

For the direct defect `e_t`, every secant survival weight `w_t` lies in
`[0,1]`, so

```text
-w_t e_t<=|e_t|.
```

Only seams contribute.  Hence every finite suffix satisfies

```text
-sum w_t e_t<=sum_selected_seams(A+B)<=eta,
```

which is stronger than the required eventual `eta+slack` bound.  This has the
correct one-sided sign: positive direct debt defects help and need not be
charged.

The remaining fields are exactly the hypotheses:

- coordinatewise candidate-debt nonnegativity;
- uniform prescribed/debt bounds `C,D`;
- first artificial debt at most `eta`;
- nonnegative generated secants bounded by opponent Continue; and
- joint and every-player-deleted suffix survival from the two distinct
  persistent literal marginals.

Thus the revised Proposition 2 exhausts the structure fields of
`QuittingChronologicalDebtShadowingCertificate` without assuming that any
candidate pair is executable or nearly Nash.

## Boundary checks

- At an all-Continue seam with both caps above the solo reward, the cap
  mismatch is transmitted with coefficient one, showing why `B` is necessary.
- At a max-branch switch, scalar max-Lipschitzness and the checked secant cover
  the nondifferentiability exactly.
- The small first debt is only an annotation.  The actual semantic debt of the
  concatenated infinite root profile may remain large; this is why the
  revision no longer contains a direct approximate terminal Nash profile.
- Choosing `exactOfRoots` would set all defects to zero but replace the
  artificial debt by that actual exploitability.  It is a different, stronger
  route and is not silently used here.

## Exact remaining gap

No source declaration currently builds the candidate pairs assumed by the
theorem.  In particular, fixed-depth exact semantic pieces from one donor
profile do not provide a summably matching endpoint for the next donor, and
static atom access does not provide a small nonsemantic first pair.  The
theorem narrows the producer to a genuine seam-selection problem, but does
not solve it.
