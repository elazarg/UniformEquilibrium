# Export-gate audit of `CAP_PUMP_SECOND_PERSISTENT_LABEL_REDUCTION`

Reviewer: `CODEX_GAUSS`

Reviewed packet:
[`CAP_PUMP_SECOND_PERSISTENT_LABEL_REDUCTION.md`](../exports/CAP_PUMP_SECOND_PERSISTENT_LABEL_REDUCTION.md)

## Verdict

**REVISE, then ACCEPT.**  The mathematical statement, proof, constants,
positive test, sharp two-player obstruction, novelty boundary, and downstream
two-label consumer all check.  The packet is a genuine strict reduction of
`PERSISTENT_TWO_LABEL_HAZARDS`, rather than an arbitrary-game source
producer.  I found no mathematical reason to demote it.

Two small source/semantics corrections are mandatory before final acceptance:

1. the robust survival adapters are currently cited under shortened names
   which are not the exact declaration names; and
2. the `Definitions and assumptions` prose momentarily identifies the
   abstract candidate-cap recursion with a literal unrestricted behavioral
   best-response recursion, although the next paragraph correctly permits
   nonsemantic candidate caps.

After those wording repairs, every export-gate item is met in the packet's
strict reduction scope.

## 1. Cap recursion and constants

Fix one row and abbreviate the cap recursion by

```text
b=max(Q,C+Ob_next),
|b_next|<=K,
|C|<=M(1-O).
```

Since the maximum dominates its Continue branch,

```text
b_next-b <= (1-O)b_next-C.
```

If the left side is positive, the right side is positive as well; bounding
its absolute value therefore gives

```text
(b_next-b)_+ <= (K+M)(1-O).
```

This remains valid through a switch of the active max branch.  Summing
positive increments dominates the signed within-block rise, so the packet's
block bound has exactly coefficient `K+M`.

The seam identity

```text
R_k-V_k=b(k,N_k,i)-b(k+1,0,i)
```

and insertion of the block source give

```text
sum_(k<n)(R_k-V_k)
 =sum_(k<n)(b(k,N_k,i)-b(k,0,i))+b(0,0,i)-b(n,0,i).
```

The last difference is at most `2K`, proving equation (5) with no missing
endpoint or sign.  Divergent favorable variation, summable reverse
variation, and finite opponent-absorption budget would contradict this
finite bound.

The rowwise union bound

```text
1-O_i <= sum_(j!=i)p_j
```

then produces one fixed persistent opponent by finiteness.  If `i` is already
persistent, this opponent is automatically a distinct second label.  The
known-mover refinement separates `a` before summing and therefore has exactly
the packet's coefficient `(K+M)P_a(n)` and the same `2K` boundary term.

The `K+M=0` edge case causes no problem: inequality (9) then prevents its
left side from being unbounded, so the label conclusion has an impossible
premise rather than a hidden division.

## 2. Exact sharp boundary and the `-2` wording

In the two-player zero-reward regression, the observer cap map is `H(z)=hz`.
The donated endpoint cap `1` prefixes to local source cap `h`, whereas the
actual next candidate source cap `h` prefixes to `h^2`.  Thus

```text
E_i=h-h^2>0,
secant=h,
R_k=1-h=p(k,a),
V_k=0.
```

With `K=1` and `M=0`, after `n` blocks equation (9)'s left side is literally

```text
n(1-h)-0-2-n(1-h)=-2.
```

The packet's wording “the bounded constant `-2`, not an unbounded excess” is
therefore exact.  Calling this zero **linear asymptotic** excess is also
correct; calling the displayed quantity itself zero would not be.

Joint survival and survival after deleting `i` are `h^n`, while deleting
`a` leaves survival one.  Hence exactly one deleted clock fails.  The choice
`h=min(eta/2,1/2)` lies in `(0,1)` for every `eta>0` and makes the initial
candidate debt no greater than `eta`.  The example is correctly labelled an
interface obstruction, not a game counterexample.

The three-player positive test also checks.  With hazards `alpha,beta`,

```text
1-O_i=alpha+beta-alpha*beta,
(1-O_i)-alpha=(1-alpha)beta>0.
```

Thus the mover-subtracted excess grows linearly and the remaining player is
indeed the second persistent label.

## 3. Probability, behavior, and candidate semantics

The probability mode is exact.  Independence is required only within each
displayed product row; multiplication across dates follows the conditional
root sequence along the unique surviving public history.  A persistent
marginal series remains divergent after every finite prefix, so the checked
two-label criterion gives all suffixwise joint and one-player-deleted
survivals.

For an actual terminal-semantic cap, the unrestricted best-response envelope
does satisfy the scalar max recursion: the player chooses Quit or Continue at
the current row, and after Continue may use an arbitrary behavioral strategy
from the successor.  Nonattainment of the successor supremum does not change
the affine supremum calculation.

The theorem, however, deliberately assumes the same recursion for bounded
**candidate** caps which need not belong to one actual semantic profile.  The
sentence

> The cap recursion (1) is the ordinary unrestricted behavioral best-response
> recursion.

should therefore be replaced by wording such as:

> For literal semantic caps, (1) is the unrestricted behavioral best-response
> recursion.  The scalar theorem assumes the same exact recursion for the
> displayed candidate caps; it does not infer their semantic provenance.

This preserves the useful abstract scope and removes any suggestion of an
actual-data seal.  For the same reason, the `Adapter and consumer` section
should call its input a “supplied literal root chronology with bounded
candidate caps,” not a produced source-matched semantic chronology.  The
roots are literal; the candidate annotations may be artificial.

## 4. Source names and consumer correspondence

The exact checked names

- `hasTwoPersistentQuittingMarginals_iff_all_suffix_survival_zero`, and
- `QuittingChronologicalDebtShadowingSurvivalFields.of_twoPersistent`

in
`UniformEquilibrium/Quitting/Paths/PersistentDeletedClockTwoLabel.lean`
are correctly cited.  The exact-spine consumer
`nonempty_quittingChronologicalDebtShadowingCertificate_of_exactSpine`
and the cap secant theorem
`exists_quittingTerminalSemanticPrefix_secant` are also correctly named.

The two robust adapters are not named `.of_summableError` and
`.of_fixedFraction` in the current source.  Their exact names are

```text
QuittingChronologicalDebtShadowingSurvivalFields.of_consecutiveBlock_summableError
QuittingChronologicalDebtShadowingSurvivalFields.of_consecutiveBlock_fixedFraction
```

in `PersistentDeletedClockTwoLabel.lean`.  The packet should use these names
where it discusses robust consumers.  The shortened wording inherited by the
question file is not precise enough for an export source audit.

## 5. Novelty and export qualification

The already formalized two-label reduction starts from two persistent labels
and converts them to clock fields.  It does not manufacture an opponent label
from bounded cap motion.  Cedar Proposition 4 establishes the favorable seam
sign and its forcing effect, but not the bounded internal replenishment
telescope.  Equations (5) and (9) therefore supply a new quantitative bridge
between the cap-pump language and the existing two-label consumer.

This is not disqualified merely because its source hypothesis remains to be
produced: the packet is presented under the export gate's reduction clause,
not as a conditional arbitrary-game producer.  It strictly replaces the
second-label selection obligation by one of two exact scalar cap accounts,
and Proposition 94 proves that the mover subtraction in the observer case is
necessary.  The positive and negative tests identify both sides of the new
boundary.

The remaining nonclaims are honest: no atom/reset source, exact spine,
initial debt, full certificate, equilibrium payoff, or counterexample is
produced.  With the declaration-name and candidate-semantics repairs above,
the packet has a complete proof, exact tests, a named live obligation, a
checked downstream consumer, a source/novelty audit, substantive independent
reviews, and a noncircular handoff.  My resulting verdict is **ACCEPT**.
