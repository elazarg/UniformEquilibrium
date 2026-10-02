# Independent audit: Fin4 strict-solo constrained plateau boundary

**Reviewer:** CODEX_EULER  
**Target:**
[`CODEX_MINER__FIN4_STRICT_SOLO_REGENERATION_PLATEAU_BOUNDARY.md`](../notes/CODEX_MINER__FIN4_STRICT_SOLO_REGENERATION_PLATEAU_BOUNDARY.md)  
**Verdict:** **MATHEMATICAL PASS, with two mandatory scope-wording repairs.**
The compact constrained-face theorem, root-isolation argument, adaptive solo
recycle, and same-profile reset relay are correct.  The note must not call the
arbitrarily selected constrained minimizer source-reachable, and its last
“does not imply” paragraph must be presented as the exact missing interface,
not as a universal logical counterexample under the complete hard residual.
Keep internal: the result isolates a sharp plateau but does not close a named
conjecture branch, produce a return, or decrease a maintained discrete rank.

## 1. Claim checked

Under the repaired strict-solo Section 10 source, fix the unique possible
debtor `e` and define

```text
K_e = {X in terminalSemanticCarrier reward |
  punishment_i <= X.1_i for every i and
  debt_i(X)=0 for every i != e}.
```

The note claims:

1. `K_e` is nonempty compact and every `X in K_e` has
   `D(X)=d_e(X)>=Gamma`;
2. at a minimizer of `D` on `K_e`, every exact root has zero absorption by
   opponents of `e`;
3. adaptive exact solo prefixing either gives a uniform payoff or converges
   to a constrained-minimum carrier where all Continue is exact; and
4. an actual best-response reset of `e` clears its debt and forces a fixed
   distinct label `f` to carry debt at least `Gamma` in a reset cluster, but
   supplies no floor-safe chronological restart or rank descent.

## 2. Compactness and nonemptiness of `K_e`

The carrier is compact.  Prescribed-coordinate floor inequalities are closed,
and terminal semantic debt is continuous, so the zero-debt equations for
`i!=e` define a closed face.  Hence `K_e` is compact.

The independently reviewed floor-entrance/tight-limit dichotomy in
`CODEX_RAMSEY__UNIQUE_DEBTOR_FLOOR_ENTRANCE_AND_SOLO_RECYCLE.md` supplies one
element of this face from the repaired Section 10 source.  In the finite arm,
exact prefixes preserve the three zero debts and all floors at the entrance;
in the infinite arm, compact closure gives the punishment-tight carrier.  No
actual-profile attainment is needed.

The checked carrier-wide theorem
`QuittingTerminalExploitabilityWitness.terminalGap_le_terminalSemanticDebtSum`
gives `Gamma<=D(X)` for every `X` in the carrier.  On `K_e`, non-`e` debts are
zero, so `D(X)=d_e(X)>=Gamma`.  Thus the compact minimum exists and is
strictly positive.

## 3. Exact-prefix invariance and opponent-root isolation

Let `X` minimize `D` on `K_e`, and let `q` be exact Nash against `X.1`.
The semantic prefix remains in the carrier.  The checked floor-forward
theorem preserves every prescribed floor because `X.1` is floor-safe.
`quittingTerminalSemanticDebt_prefix_le`, together with nonnegativity of
carrier debt, preserves each equation `d_i=0` for `i!=e`.  Therefore
`Prefix(q,X)` really belongs to `K_e`; there is no hidden cap-versus-
prescribed mismatch here because the root is exact against `X.1`.

The unique-debtor contraction gives

```text
D(Prefix(q,X)) <= (1-A_(-e)(q)) D(X).
```

Constrained minimality gives the reverse weak inequality, and `D(X)>0`.
Hence `A_(-e)(q)=0`.  For a finite product root, zero opponent-union
absorption forces every opponent marginal to be pure Continue.  Theorem 4.1
is exact.

## 4. Adaptive solo recycling

At a constrained minimizer every exact root is on the solo `e` face.  If all
Continue is exact, the plateau is immediate.  Otherwise an exact root has
`p=q_e(Quit)>0`.  It cannot have `p=1`: the static full-gap collider `c!=e`
would strictly prefer Quit at the row with sure `e` and all remaining labels
Continuing, contradicting exact complementarity.  Thus `0<p<1`, and owner
complementarity forces `X.1_e=r_e({e})`.

The checked unique-debtor solo-prefix identity preserves the complete debt
vector.  Floor forward preserves `K_e`, and minimality is retained.  The
owner's singleton equality is affine and remains exact.  Therefore the
dependent-choice iteration is legitimate.

On an infinite iteration, root absorption is exactly `p_n`.  If
`sum p_n` diverges, the checked infinite-orbit cumulative-charge theorem gives
a uniform payoff.  If it converges, `p_n->0`; the `2M p_n` movement bound
makes prescribed coordinates Cauchy, and the constant debt vector makes cap
coordinates Cauchy.  Compact closure gives `Z in K_e`.  The solo roots
converge to all Continue, and closedness of the finite exact-root graph gives
exact all-Continue Nash at `Z.1`.  Theorem 4.1 applies at the limit.  I found
no indexing, orientation, or compactness gap.

### Mandatory source-connectedness repair

The floor recursion proves only that `K_e` is nonempty.  The proof then
minimizes over **all** of `K_e`; it does not prove that the chosen minimizer
`X_*` is reached from the floor-entrance output by a finite or infinite exact
prefix chronology.  This does not affect the existential theorem, but the
status and Sections 1/5 must replace “source-connected regeneration” or
“starting from ... reaches” by:

> the repaired source proves `K_e` nonempty; compact constrained minimization
> then selects a same-table minimizer from which the adaptive orbit starts.

No path from the original Section 10 source to that minimizer is asserted.

## 5. Same-profile reset relay

Choose actual realizing profiles `sigma_n` for `Z` and owner strategies
`beta_n` within `1/n` of the unrestricted cap.  Own-strategy cap invariance
and payoff approximation give

```text
U_e(update sigma_n e beta_n) -> Z.2_e,
B_e(update sigma_n e beta_n) -> Z.2_e,
d_e(update sigma_n e beta_n) -> 0.
```

The checked theorem
`exists_other_terminalGap_subsequence_of_semanticDebt_reset` then supplies
one fixed `f!=e` and a strict subsequence with debt at least `Gamma`.  A
further compact subsequence gives `W`; continuity gives

```text
d_e(W)=0, d_f(W)>=Gamma,
W.1_e=W.2_e=Z.2_e.
```

Since `Z in K_e` and `d_e(Z)>=Gamma`,
`Z.2_e=Z.1_e+d_e(Z)>=chi_e+Gamma`.  All equalities and the distinct-recipient
claim are correct.  They concern actual same-profile unilateral resets before
compactification, not Bellman prefixes.

## 6. Exact scope of the failed rank implication

Theorem 6.1 asserts no control over the other two debts at `W`, no floors for
them, no membership of `W` in `K_f`, and no exact Bellman chronology from
`Z` to `W`.  The transfer identities are lower bounds on newly appearing
opponent debt, not total-debt or support descent.  The displayed vector pattern

```text
(Gamma,0,0,0) -> (0,Gamma,0,0)
```

correctly shows that the scalar transfer account is compatible with unchanged
total debt and support size.

However, the local padded regression deliberately lacks the full terminal
witness and punishment-normal hard residual.  It therefore does not prove a
universal counterexample to every stronger implication under those ambient
hypotheses.  Replace the sentence

> “The exact minimal failed implication is ... does not imply ...”

by

> “The exact output interface stops here: Theorem 6.1 does not assert, and no
> checked declaration currently derives, floor safety/unique-debtor target
> structure, debt/support descent, or a chronological return.  The regression
> shows the underlying reset algebra alone cannot supply those fields.”

This is the second mandatory scope repair.  It preserves the useful negative
audit without overstating the regression.

## 7. Source and novelty verdict

The declaration names listed in the note are accurate, including the
carrier-wide terminal-gap floor, unique-debtor contraction, floor-forward
transport, reset-debt subsequence theorem, and global/minimum-reference
transfer accounts.  The result is not subsumed verbatim by the reviewed
Ramsey recycle: the constrained compact minimization proves that **every**
exact root at the selected plateau has zero opponent absorption.  Conversely,
the checked global Fin4 strict-minimum plateau is stronger on the global
minimum fiber and does not make this off-minimum constrained minimizer
chronologically reachable.

After the two wording repairs, retain this as a mathematically correct
internal boundary theorem.  I do not recommend export: it neither closes the
strict-solo branch nor supplies the missing target-floor, restart, or
well-founded-rank consumer.

