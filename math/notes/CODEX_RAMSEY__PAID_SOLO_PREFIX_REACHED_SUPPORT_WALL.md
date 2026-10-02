# A zero-drop charged solo gate reaches a literal carrier support wall in bounded depth

Author: `CODEX_RAMSEY`

Status: **proved ordinary mathematics; internal best-attempt reduction, not a
paid near-return producer.**  The result starts from the reviewed zero-drop
solo/blocker gate and replaces its artificial coordinatewise threshold by a
literal carrier-enriched exact prefix.  It proves that fixed-root reuse must
hit a strict outsider support wall after uniformly bounded depth.

**Post-review update.**  Proposition 9 of
[`CODEX_CEDAR__FOUR_PLAYER_CONJECTURE_CAPSTONE.md`](CODEX_CEDAR__FOUR_PLAYER_CONJECTURE_CAPSTONE.md)
now supplies the exact root-selection completion, independently audited in
[`CODEX_RAMSEY`, Proposition 9](../feedback/CODEX_CEDAR__FOUR_PLAYER_CONJECTURE_CAPSTONE__BY_CODEX_RAMSEY__PROPOSITION_9.md):
after bounded literal restarts, the wall yields strict semantic-debt descent,
a full-gap triple join, or the checked stationary handoff.  Section 21 of
Euler's inventory, audited
[`here`](../feedback/CODEX_EULER__FIN4_SEARCH_SPACE_INVENTORY__BY_CODEX_RAMSEY__SECTION_21.md),
consumes the triple join into the pair-base stationary two-debtor source.
Thus the selection wall is no longer open; the remaining paid problem is to
iterate the debt descent through support change or construct a charged
connector from the common stationary two-debtor source.

**Final seam audit.**  Section 7 below records the completed connector
attempt.  The pair-base handoff forces the paid debtor into the Never-high
orientation, and the checked fixed-incidence regression permits an
all-Continue-only cap root.  Thus no source-matched charged successor follows
from the retained atom/toggle data.  This final audit is a stopping-boundary
record, not an additional reviewed theorem.

Independent review:
[`CODEX_CEDAR`](../feedback/CODEX_RAMSEY__PAID_SOLO_PREFIX_REACHED_SUPPORT_WALL__BY_CODEX_CEDAR.md),
`REVISE -> PASS` after correcting the Bellman relation arrow in `(3.2)` from
tail to prefixed current and distinguishing it from reverse behavioral
chronology.

Question:
[`PAID_ADMISSIBLE_PAYOFF_NEAR_RETURN.md`](../questions/PAID_ADMISSIBLE_PAYOFF_NEAR_RETURN.md)

Upstream reviewed inputs:

- Proposition 5 in
  [`CODEX_CEDAR__FOUR_PLAYER_CONJECTURE_CAPSTONE.md`](CODEX_CEDAR__FOUR_PLAYER_CONJECTURE_CAPSTONE.md),
  reviewed independently by Euler and Ramsey;
- Proposition 6 in the same note, reviewed in
  [`CODEX_RAMSEY`, Proposition 6](../feedback/CODEX_CEDAR__FOUR_PLAYER_CONJECTURE_CAPSTONE__BY_CODEX_RAMSEY__PROPOSITION_6.md);
- the exact semantic-prefix debt accounts in
  `TerminalSemanticOwnStrategyTransport.lean`; and
- carrier closure under literal root prefixing in
  `TerminalSemanticPair.lean`.

## 1. Self-contained data

Let `I` be finite, let `M>0`, let rewards and every carrier payoff coordinate
be bounded in absolute value by `M`, and let

```text
X=(U,B) in quittingTerminalSemanticCarrier reward.
```

This may be a compact-closure carrier point rather than the semantic pair of
one attained profile.  Fix an owner `k` and a hazard `p in (0,1)`.  Assume:

```text
d_k(X)=D(X)>0,
d_j(X)=0                         for j!=k,              (1.1)
U_k=s_k:=r({k})_k,                                      (1.2)
q=soloRoot(k,p) is exact Nash at U.                     (1.3)
U_j>=P_j                           for every j.          (1.3a)
```

For outsider `j!=k`, put

```text
R_j=r({k})_j,
Q_j=(1-p)r({j})_j+p r({k,j})_j,
g_j=Q_j-R_j.                                           (1.4)
```

Assume that one named blocker `i!=k` satisfies

```text
g_i>=g>0.                                               (1.5)
```

The reviewed Proposition 5 supplies exactly `(1.1)--(1.5)`, with
`p>=alpha=a/8`, and Proposition 6 makes the lower bound uniform,
`g>=g_a>0`.

Define repeated literal semantic prefixes by

```text
X^0=X,
X^(n+1)=Prefix(q,X^n),
U^n=(X^n).1.                                            (1.6)
```

The definition makes sense regardless of whether `q` remains exact at later
tails.  When it is exact through a given depth, `(1.6)` is a literal exact
carrier-enriched Nash--Bellman prefix through that depth.

## 2. Exact affine and debt identities

### Lemma 2.1 (literal solo-prefix formula)

For every `n`,

```text
U^n_k=s_k,
U^n_j=R_j+(1-p)^n(U_j-R_j)          for j!=k.           (2.1)
```

**Proof.**  A solo row absorbs at `{k}` with probability `p` and jointly
Continues with probability `1-p`.  Thus

```text
U^(n+1)_k=p s_k+(1-p)U^n_k=s_k,
U^(n+1)_j=p R_j+(1-p)U^n_j.
```

Induction gives `(2.1)`. `QED`

### Lemma 2.2 (the unique-debtor vector is preserved while the row is exact)

If `q` is exact at `U^m` for every `m<n`, then

```text
d_k(X^n)=d_k(X),
d_j(X^n)=0                         for j!=k.             (2.2)
```

In particular every `X^m`, `m<=n`, is a literal carrier point with the same
positive-debt support `{k}` and the same total debt.  Its prescribed payoff
remains above punishment by exact floor-forward invariance.

**Proof.**  Use

```text
quittingTerminalSemanticDebt_prefix_eq_capDefect_add_continueMass_mul.
```

For `j!=k`, the tail cap equals its prescribed payoff by `(1.1)`, so exact
Nash at `U^m` makes the cap-coordinate root defect zero.  The old debt is
also zero, hence the prefixed debt remains zero.

For `k`, the old cap is `B_k=U^m_k+d_k=s_k+d_k`.  Against the solo row at
that cap, Continue exceeds Quit by exactly `d_k`; because the prescribed
owner mixture assigns Quit probability `p`, its cap-coordinate Nash defect
is `p d_k`.  Joint Continue mass is `1-p`.  Therefore

```text
d_k(X^(m+1))=p d_k(X^m)+(1-p)d_k(X^m)=d_k(X^m).
```

Induction proves `(2.2)`. `QED`

This is why the construction is a **zero semantic-debt-drop** spine rather
than a disguised macroscopic-descent arm.

## 3. The reached support-wall theorem

### Proposition 3.1 (bounded exact reuse or a literal strict support wall)

Under `(1.1)--(1.5)`, there is a least natural number `N>=1` such that

```text
q is not exact Nash at U^N.                            (3.1)
```

Every earlier row is a literal exact carrier prefix of charge `p`:

```text
U^m -> U^(m+1),             0<=m<N.                   (3.2)
```

Here the charged-relation arrow runs from the continuation tail `U^m` to the
prefixed current payoff `U^(m+1)`.  Behavioral execution reads the same row in
the reverse chronology: play the prefix producing `U^(m+1)`, then continue at
`U^m`.

At the reached literal carrier tail `U^N`, some outsider `j!=k` has strict
immediate-Quit gain against the old solo row,

```text
Delta_j(U^N,q)>0.                                     (3.3)
```

The owner remains exactly indifferent there.  Thus failure is genuinely an
outsider support/root-selection wall, not loss of the owner equation, loss
of carrier provenance, or a punishment-floor seam.

Moreover, if `p>=alpha>0`, `alpha<1`, and `g_i>=g>0`, then one may take

```text
N <= H(alpha,g,M),                                    (3.4)
```

where any integer `H>=1` satisfying

```text
2M(1-alpha)^(H+1)<g                                  (3.5)
```

is valid.

**Proof.**  For outsider `j`, the Quit-minus-Continue endpoint gap of `q`
at `U^n` is exactly

```text
Delta_j(U^n,q)
 =Q_j-[pR_j+(1-p)U^n_j]
 =g_j-(1-p)^(n+1)(U_j-R_j).                          (3.6)
```

At `n=0`, exactness gives `Delta_j(U,q)<=0` for every outsider.  For the
named blocker `i`, `(3.6)` converges to `g_i>=g>0`.  Hence exactness must fail
at some finite positive depth; let `N` be the first such depth.  The owner
condition remains equality because `(2.1)` keeps its tail coordinate equal
to `s_k`.  Therefore failure is witnessed by an outsider, proving `(3.3)`.
Carrier provenance, zero debt drop, and the edge statement follow from
Lemmas 2.1--2.2.

For the uniform bound, `|U_i-R_i|<=2M`, `1-p<=1-alpha`, and `(3.6)`.  If
`n=H` satisfies `(3.5)`, then

```text
Delta_i(U^H,q)
 >=g-2M(1-alpha)^(H+1)>0.
```

Thus first failure occurs no later than `H`. `QED`

### Corollary 3.2 (the only infinite fixed-root branch would already solve the question)

Without the strict blocker hypothesis `(1.5)`, if `q` remains exact at every
`U^n`, then the one-edge paths `(3.2)` themselves give the maintained
near-return family, because

```text
||U^(n+1)-U^n||_infinity
 <=2M p(1-p)^n ->0,                                   (3.7)
```

while every edge has absorption charge exactly `p>0`.

Thus these are Bellman relation edges `U^n -> U^(n+1)`; their literal
behavioral prefix chronology is `U^(n+1)` followed by continuation `U^n`.

Thus the reviewed strict blocker does not leave a hidden fixed-root
recurrence architecture.  It forces the second, reached-wall arm of the
dichotomy after bounded depth.

## 4. What an exact root at the wall must do

Let `z` be any exact product root at `U^N`; finite mixed-Nash existence
supplies at least one.  If the witness `j` in `(3.3)` does not Quit surely in
`z`, then Continue has positive support and exactness gives

```text
Delta_j(U^N,z)<=0.
```

Coupling the opponent product laws of `q` and `z` yields the source-specific
root displacement

```text
sum_(ell!=j)|z_ell-q_ell|
 >= Delta_j(U^N,q)/(4M)>0.                            (4.1)
```

If `z_j=1`, its absorption is one.  Hence every exact selection at the wall
either activates the witness surely or moves the opponent root a fixed
positive distance from the incoming solo row.  This is an operational
root-selection statement, but `(4.1)` does **not** by itself lower carrier
debt: the displaced selection may be all-Continue, using the entire distance
to delete the old owner hazard.

## 5. Exact frontier change and subsequently reviewed completion

The result eliminates two misleading architectures in the reviewed
zero-drop blocker arm.

1. The artificial tail obtained by changing only the blocker coordinate is
   unnecessary for locating the next obstruction.  A bounded literal word
   of the same charged root reaches a **carrier point** with unchanged
   unique-debtor semantics.  Attained behavioral realization is inherited
   only when the starting carrier point is itself attained.
2. Reusing the fixed charged solo row at all scales cannot be the missing
   near-return mechanism: without a blocker it would solve the question by
   `(3.7)`, while the reviewed blocker forces finite failure.

At the time of the original argument, the remaining obstruction was:

```text
At the reached carrier X^N, select an exact root which either
  (a) has positive opponent absorption for k, yielding semantic debt descent,
  (b) activates a new owner/support and enters an existing support consumer,
or
  (c) prove that an all-Continue/solo-owner selection jump is already solved.
```

Ordinary mixed-Nash existence alone does permit a jump to all-Continue, so
`(4.1)` did not supply the selection.  The subsequently reviewed Proposition
9 closes this local wall by compactly separating non-solo roots and, in the
solo branch, restarting with a strictly larger owner rate; an infinite restart
would compactify backward to the checked forbidden fixed-owner semantic
spine.  Its finite outputs are strict semantic-debt descent or the typed Fin4
handoff branches summarized above.

This note remains **not separately export-ready** because the stronger
Proposition 9/Section 21 composition subsumes its frontier value.  That
composition still does not iterate debt descent after support change or
produce the paid payoff-near-return family.

## 6. Source and novelty audit

Inspected declarations:

- `quittingTerminalSemanticDebt_prefix_eq_capDefect_add_continueMass_mul` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticOwnStrategyTransport.lean`;
- carrier prefix closure and exact debt monotonicity in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`;
- `infiniteOrbit_exists_value_limit` in
  `UniformEquilibrium/Diagnostics/Quitting/Capacity/InfiniteOrbitLimit.lean`;
- the fixed-root normalized-delivery obstruction reviewed as Section 41 of
  `CODEX_CEDAR__PAID_ROW_REENTRY.md`; and
- the source-changing support-entry diagnostics in
  `TerminalSemanticSoloOwnerRefinement.lean`.

Section 41 treats normalization at the stationary delivery of a supplied
root.  The present result instead follows the literal semantic carrier and
locates the first loss of exactness, with a uniform finite-depth bound and
unchanged unique-debtor provenance.  It is a new local reduction, not a new
all-behavior compiler.

## 7. Final source-matched successor audit after the stationary handoff

This section records the last attempted composition after the reviewed
Proposition 9/Section 21 completion.  It adds no producer claim.

### 7.1 The pair-base handoff is necessarily in the Continue/Never paid arm

Consider the pair-base stationary output of Section 21.  Two base players
`k,i` Quit surely and the other two players use an induced Nash point.  The
terminal witness localizes a debtor `d` to `{k,i}` with

```text
B_d(sigma)-U_d(sigma)>=Gamma>0.                        (7.1)
```

The prescribed strategy of `d` is already immediate Quit.  Therefore the
literal immediate-Quit replacement changes nothing and its pure endpoint is

```text
Q_d=U_d(sigma).                                        (7.2)
```

Against stationary opponents the exact unrestricted cap formula is

```text
B_d(sigma)=max(Q_d,N_d),                               (7.3)
```

where `N_d` is the Always-Continue/Never endpoint.  Equations `(7.1)--(7.3)`
force

```text
N_d=B_d(sigma)>=U_d(sigma)+Gamma.                      (7.4)
```

Thus the paid high endpoint of the actual pair-base two-debtor source is
necessarily Continue/Never, never immediate Quit.  In particular the
immediate-Quit singleton-gap/exact-root entrance in
[`LARGE_BASE_PAID_ENDPOINT_ATOM_DISPATCH.md`](../exports/LARGE_BASE_PAID_ENDPOINT_ATOM_DISPATCH.md)
does not apply directly to this common handoff source.

This is an all-behavior statement, not a stationary-only comparison: the
other sure base member ends play at date zero after any deviation by `d`, so
every behavioral deviation reduces to its initial Continue/Quit action.

### 7.2 What the reviewed owner repair does and does not change

The reviewed large-base re-selection/owner-repair route (Sections 75--76 of
`CODEX_CEDAR__PAID_ROW_REENTRY.md`) converts the large-base source to an
actual stationary paid profile `tau`, with the repaired owner at its cap and
a free debtor of size at least `Gamma`.  If `tau` is floor safe and the free
debtor's high endpoint is immediate Quit, the reviewed endpoint-root
dichotomy gives either a literal fixed-charge exact predecessor at its actual
tail or macroscopic collision mass in the same source row.

The remaining orientation is again Never.  Its fixed positive terminal atom
is source matched, but it is not the absorption charge of an exact root.
The checked regression

```text
positive_incidence_and_toggle_but_only_allContinue_capNash
```

in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceCapReturn.lean`
shows that positive same-law incidence plus a strict membership toggle can
coexist with the all-Continue root being the only exact cap--Nash root.  Hence
the terminal atom cannot be promoted to a charged Bellman successor by a
generic incidence argument.

The positive alternative in that same file,
`QuittingTerminalExploitabilityWitness.exists_fixedLaw_resetFace_dispatch`,
requires a minimum-source/reset-face package not supplied by the reselected
stationary handoff.  Invoking it here would assume the missing source
adapter.

### 7.3 Exact stopping boundary

The in-flight source-matched connector attempt therefore ends at the
following literal seam:

```text
actual floor-safe stationary paid source
  + high endpoint = Never
  + fixed source-matched terminal atom

does not imply

an exact positive-charge floor-admissible successor.
```

On the pair-base source the Never orientation is forced by `(7.1)--(7.4)`.
After owner repair, immediate Quit is already covered and only the Never
orientation remains.  Existing checked regressions show that the all-Continue
cap wall is compatible with all atom/toggle fields currently retained.

Accordingly no marked fixed-charge regeneration rule, support-changing debt
iteration, or payoff near-return has been proved here.  A genuine next step
must add one of two pieces unavailable in the present data: a source-native
reset-face/minimum adapter that triggers the checked strict-debt dispatch, or
a new theorem excluding the all-Continue cap face in the Never-oriented paid
source.  Generic finite recurrence or payoff-cell rank machinery cannot
replace either piece.
