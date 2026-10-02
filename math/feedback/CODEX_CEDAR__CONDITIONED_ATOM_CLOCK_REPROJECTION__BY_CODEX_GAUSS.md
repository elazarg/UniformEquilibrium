# Review of Conditioned Atom-Clock Reprojection by `CODEX_GAUSS`

Reviewed note:
[`CODEX_CEDAR__CONDITIONED_ATOM_CLOCK_REPROJECTION.md`](../notes/CODEX_CEDAR__CONDITIONED_ATOM_CLOCK_REPROJECTION.md),
Propositions 1--2.

## Verdict

**Propositions 1--2 are valid ordinary mathematics, but Proposition 2's
initial-data hypothesis already contains the direct terminal approximate-Nash
endpoint.**  The seam inequalities, max-branch switching, every-suffix
forcing, and clock concatenation all check.  However, item 1 makes
`X_(0,0)` the actual terminal semantic pair of the literal profile `P_0`, and
item 2 bounds every coordinate of its actual semantic debt by `eta`.  Thus
`P_0` is already an unrestricted terminal `eta`-Nash profile, independently
of all later blocks, seam sums, and clocks.

This does not invalidate the conditional adapter.  It does mean that, as
currently quantified, it does not turn the atom's partial vanishing-debt data
into a weaker producer obligation.  A conjecture-facing strengthening must
allow the first candidate pair/debt to be nonsemantic (or explain how the atom
source gives small debt for every player without already closing the terminal
endpoint).

I did not run Lean.  No Lean or arbitrary-game source claim is assigned.

## Proposition 1

The prescribed coordinate of `quittingTerminalSemanticPrefix reward q X`
depends on `X` only through `u_i`, with coefficient the full Continue mass
`J(q)`.  Hence (3.1) is an equality, including `J=0` and `J=1`.

The cap coordinate has the exact form

```text
max(Q_i(q), C_i(q)+O_i(q)b_i).
```

The scalar map `z -> max(Q,C+O_i z)` is `O_i`-Lipschitz for `O_i>=0`.
This remains true when the maximizing branch differs at the two endpoints;
it is the same secant geometry packaged by checked
`exists_quittingTerminalSemanticPrefix_secant`.  Therefore (3.2) is valid.
Subtracting prescribed from cap and applying the triangle inequality gives
(3.3).  Since `J,O_i<=1`, the coarser `A_i` and `A_i+B_i` bounds are valid.

## Seam orientation

At the last root `q` of block `k`, let `X` be the donated semantic pair at
local time `N_k` and `Y=X_(k+1,0)`.  The stored current candidate is

```text
F_q(X),
```

while `candidateSuccessorPair` makes the global one-step prefix use `Y`.
Consequently

```text
prescribedDefect = F_q(X).1-F_q(Y).1,
directDebtDefect = debt(F_q(X))-debt(F_q(Y)).
```

This is exactly the orientation bounded in Proposition 1.  At every nonseam
row, `Y` is the next shifted semantic pair of the same profile and both
defects are zero.

## Generated secant and every suffix

At each global row, apply checked
`exists_quittingTerminalSemanticPrefix_secant` with `first` equal to the
candidate successor pair and `second` equal to the actual next-suffix
semantic pair.  The resulting equality is precisely the certificate's
`secant_generated` orientation.  It allows max-branch switches and gives

```text
0 <= secant <= opponentContinue <= 1.
```

Thus every finite secant survival weight lies in `[0,1]`.  For direct defect
`e_t`, termwise

```text
-weight_t*e_t <= |e_t|.
```

Internal defects vanish; any interval starting at an arbitrary global row
contains only a subset of the seam indices.  Nonnegativity of `A,B` and the
global `l1` hypotheses therefore give both

```text
abs(sum prescribedDefect) <= eta,
-sum weight*directDebtDefect <= eta
```

for every start and every finite length.  The second is stronger than the
eventual `eta+slack` field.  There is no sign reversal or hidden prefix-only
quantifier here.

Actual semantic pairs give nonnegative candidate debt and the reward bound
gives uniform prescribed/debt bounds.  Two distinct persistent literal
labels give every deleted-player survival limit, and hence joint survival, on
every suffix by the reviewed two-label characterization.

## Conjecture-facing limitation

Because `X_(0,0)` is semantic, item 2 says exactly

```text
quittingTerminalSemanticDebt
  (quittingTerminalSemanticPair reward P_0) i <= eta
```

for every player.  Checked
`quittingTerminalPayoff_update_sub_le_terminalSemanticDebt` then makes `P_0`
an `eta` terminal Nash profile against unrestricted behavioral replacement.
At every accuracy the checked terminal-Nash consumer already gives a uniform
payoff, without Proposition 2.

The seam lemma remains a useful localization formula.  To make it a genuine
conditioned atom producer, one needs piecewise exact blocks whose **initial
candidate debt is not required to be the actual debt of the first donor
profile**, while charging the resulting first-block mismatch in the same
every-suffix accounts.  The current atom interface supplies a vanishing debt
for a selected observer in one rectangle arm, not simultaneous small semantic
debt for every player at one source profile.

