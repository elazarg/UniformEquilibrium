# Two-sided singleton walls and unique-root capacity shift

Author: CODEX_SPINOZA

## Status

**Exact ordinary mathematics; strict reduction, not Lean-checked and not a
terminal consumer.** A vanishing full terminal-semantic seam transfers the
late-reset singleton cap pin and debt floor to its low sibling. Hence every
exact product root on both sides has a uniform positive absorption floor and
spends a fixed amount of the same named semantic-debt coordinate.

At the common limiting payoff, either its exact-root set contains two
distinct positive-absorption roots, or it is a singleton and all nearby exact
roots on both sides converge uniformly to that one root. In the singleton
case a fixed canonical capacity gap does not disappear: it shifts, with
\(o(1)\) loss, to common exact successors. Iteration ends at a later
multi-root face or produces an all-summable outward exact-predecessor spine.

## Question

What exact root data cross the vanishing reset-child seam, and does uniqueness
of the limiting positive root eliminate the canonical capacity recharge?

## 1. Two-sided singleton wall

Let \(I\) be finite, let \(r\) be a quitting reward table with
\(|r_i(S)|\le M\), \(M>0\), and let

\[
 X_n=(u_n,B_n),\qquad Y_n=(v_n,C_n)
\tag{1}
\]

be terminal semantic pairs satisfying

\[
 \lVert X_n-Y_n\rVert_\infty\longrightarrow0.
\tag{2}
\]

Fix player \(j\), put \(s_j=r_j(\{j\})\), and assume

\[
 B_{n,j}\longrightarrow s_j,\qquad
 d_j(X_n):=B_{n,j}-u_{n,j}\ge\delta>0.
\tag{3}
\]

Then

\[
 C_{n,j}\longrightarrow s_j,\qquad
 d_j(Y_n)=C_{n,j}-v_{n,j}\ge\delta-o(1).
\tag{4}
\]

After discarding finitely many indices, both sides satisfy

\[
 d_j\ge\gamma:=\delta/2,\qquad
 |\mathop{\rm cap}_j-s_j|\le\gamma/4.
\tag{5}
\]

### Theorem 1.1

For every sufficiently large \(n\), every exact product root \(q\) against
either \(u_n\) or \(v_n\) obeys

\[
 \boxed{\operatorname{Abs}(q)\ge
 \alpha:=\min\{1,\delta/(32M)\}>0.}
\tag{6}
\]

Prefixing \(q\) to the corresponding full terminal semantic pair decreases
the named debt, and hence total debt, by at least

\[
 \boxed{\Delta:=\min\{\delta/4,\delta^2/(64M)\}>0.}
\tag{7}
\]

#### Proof

The fixed-cap-pin coordinate expenditure theorem with
\(\gamma=\delta/2\) gives (7). Let \(\beta\) be the probability that some
opponent of \(j\) Quits at \(q\). If
\(\beta\ge\gamma/(16M)\), joint absorption is at least that amount.
Otherwise the endpoint-stability estimate and (5) make Quit strictly better
than Continue for \(j\). Exact complementarity forces \(q_j=1\), so joint
absorption is one. This proves (6). QED

The bound is uniform over **all** exact root selections on both sides. The
low side need not be a reset child; full-semantic closeness transfers both
the complete cap pin and the debt floor.

## 2. Limiting root set

Pass to a subsequence on which both semantic sequences converge to
\(Z_*=(u_*,B_*)\). Then

\[
 B_{*,j}=s_j,\qquad d_j(Z_*)\ge\delta.
\tag{8}
\]

Let \(\mathcal R(u)\) be the nonempty compact exact-root set against \(u\).
Its graph is closed.

### Theorem 2.1: positive multi-root or singleton collapse

Exactly one alternative holds.

1. There are distinct \(q^0,q^1\in\mathcal R(u_*)\) with

   \[
   \operatorname{Abs}(q^0),\operatorname{Abs}(q^1)\ge\alpha.
   \tag{9}
   \]

   In particular their root distance \(\rho_*>0\).

2. There is one root \(q_*\) with \(\mathcal R(u_*)=\{q_*\}\), and

   \[
   \sup_{q\in\mathcal R(u_n)\cup\mathcal R(v_n)}
      \lVert q-q_*\rVert_\infty\longrightarrow0.
   \tag{10}
   \]

   Moreover \(\operatorname{Abs}(q_*)\ge\alpha\).

#### Proof

The limiting pair (8) satisfies the same fixed-pin hypotheses, so every root
in \(\mathcal R(u_*)\) has absorption at least \(\alpha\). If the compact
root set is not a singleton, choose two distinct points.

Suppose it is the singleton \(\{q_*\}\). Failure of (10) would give a fixed
positive distance and exact roots at \(u_n\) or \(v_n\) staying that far from
\(q_*\). Root-simplex compactness gives a further limit. Closedness of exact
endpoint Nash puts that limit in \(\mathcal R(u_*)\), contradicting
singletonness. QED

### Corollary 2.2: matched literal prefixes

In the singleton case, arbitrary choices
\(q_n\in\mathcal R(u_n)\) and \(r_n\in\mathcal R(v_n)\) satisfy

\[
 q_n-r_n\longrightarrow0.
\tag{11}
\]

Continuity of complete semantic prefixing gives

\[
 \operatorname{Prefix}(q_n,X_n)
 -
 \operatorname{Prefix}(r_n,Y_n)
 \longrightarrow0.
\tag{12}
\]

Both prefixes are literal and exact, have charge at least \(\alpha\), and
spend at least \(\Delta\) of named and total semantic debt. Equation (12) is
a same-depth matching statement, not an edge between the siblings.

## 3. The capacity gap shifts to the common successor

Let \(\phi(u)\) be bounded full-box exact predecessor capacity and assume

\[
 \phi(u_n)-\phi(v_n)\ge\kappa>0.
\tag{13}
\]

In the singleton case, choose \(\varepsilon_n\downarrow0\). Choose a finite
path from \(u_n\) within \(\varepsilon_n\) of \(\phi(u_n)\), let \(q_n\)
be its first root, and put \(u'_n=F(q_n,u_n)\). Choose any
\(r_n\in\mathcal R(v_n)\) and put \(v'_n=F(r_n,v_n)\).

### Theorem 3.1

One has

\[
 u'_n-v'_n\longrightarrow0
\tag{14}
\]

and

\[
 \boxed{\phi(u'_n)-\phi(v'_n)\ge\kappa-o(1).}
\tag{15}
\]

#### Proof

Theorem 2.1 gives \(q_n,r_n\to q_*\), so Bellman continuity proves (14).
The suffix of the nearly maximizing high path gives

\[
 \phi(u'_n)\ge
 \phi(u_n)-\operatorname{Abs}(q_n)-\varepsilon_n.
\tag{16}
\]

Prepending the exact low root to paths from \(v'_n\) gives

\[
 \phi(v_n)\ge
 \operatorname{Abs}(r_n)+\phi(v'_n).
\tag{17}
\]

Subtract (17) from (16), use (13), and use continuity of absorption together
with \(q_n-r_n\to0\). This proves (15). QED

Thus singletonness removes root-selection mismatch but does not prove
continuity of capacity. The discontinuity moves one exact predecessor step.

## 4. Iteration and its honest boundary

Repeat Theorem 3.1 whenever the root set at the next common limiting payoff
is a singleton. At step \(k\), pass far enough along the current sequences
that the loss in (15) is at most \(\kappa/2^{k+2}\). The total loss over all
finite stages is then less than \(\kappa/2\). For every fixed depth \(K\),
this gives

\[
 u^0_*\longrightarrow u^1_*
 \longrightarrow\cdots\longrightarrow u^K_*,
\qquad
 u^{k+1}_*=F(q^k_*,u^k_*),
\tag{18}
\]

with capacity gap at least \(\kappa/2\) surviving at depth \(K\). Hence
either:

1. some finite-depth common payoff has at least two exact roots; or
2. there is an infinite exact predecessor spine with a unique root at every
   displayed payoff.

Under the checked Fin4 no-uniform-payoff capacity bound, every finite initial
segment of the latter outward predecessor spine has uniformly bounded total
charge, so

\[
 \sum_{k\ge0}\operatorname{Abs}(q^k_*)<\infty.
\tag{19}
\]

In particular \(q^k_*\to\) all Continue. The first charge is at least
\(\alpha\), but the wall need not survive after the first predecessor.

This outward spine is not automatically a chronological infinite
Nash--Bellman tail. Every finite segment can be reversed over its final
payoff, but an infinite outward word has no final payoff from which to reverse
it. Consequently the checked punishment-floor violation theorem for
chronological dynamic tails does not apply, even if \(u^0_*\) lies below a
punishment floor. Calling (19) a summable punishment-floor port would be an
orientation error.

## 5. Fin4 renewed-source adapter

For the small-full-semantic-seam renewed branch, take

\[
 X_n=\operatorname{Sem}(S_{m_n+1}),\qquad
 Y_n=\operatorname{Sem}(P_{m_n}).
\tag{20}
\]

The high side is the actual sufficiently late reset child. The reviewed
late-reset theorem supplies fixed \(j,\delta\) and (3). The full-semantic
seam supplies (2). Thus all the preceding theorems apply literally.

The surviving exact alternatives are:

- a first limiting complementarity face with two distinct roots, both
  carrying the fixed positive absorption floor;
- after one or more singleton shifts, a later multi-root face without the
  original quantitative wall; or
- an all-summable outward exact-predecessor spine.

The last two are the exact reason the tempting claim “unique first root
contradicts the capacity gap” is not presently justified.

## Checked sources inspected

- FIXED_CAP_PIN_APPROXIMATE_ROOT_DEBT_EXPENDITURE, exact cap-pin theorem;
- CODEX_HAHN__LATE_RESET_RENEWS_ESCAPING_CAP_CLOCK_SOURCE, all-root floor;
- CODEX_HAHN__RENEWED_SOURCE_FLOOR_ELIMINATES_DELAYED_CAPACITY_ESCAPE,
  independently reviewed at SHA-256
  279feaea606e31690e7c5115b5d42b000a14a97e3ba30ac24d42093b226cf7e4;
- CODEX_SPINOZA__TWO_SURE_RENEWAL_CAPACITY_BARRIER_MODULUS_FAILURE, frozen
  at SHA-256
  bf5db04c65cbaa9fc82346773a74537bab2f09a0f1c4ffd7620dad3d25c4a73b;
- isClosed_isZeroQuittingRootEndpointNash_simplex in
  UniformEquilibrium/Quitting/Bellman/Finite/NashBellmanSpine.lean;
- ChargedRelation.value_tgt_add_charge_le_value_src in
  MathUE/ChargedPathBudget.lean; and
- the orientation audit in
  CODEX_SOURCE_GATE__OFFMINIMUM_POSITIVE_ROOT_ZENO_FACE_SATURATION.

## Boundary and nonclaims

- Prescribed-payoff closeness alone does not transfer the complete cap pin or
  semantic debt; full-semantic closeness is essential.
- Uniform collapse of nearby root sets uses singletonness of the limiting
  exact-root set. It gives no continuous choice on a multi-root face.
- Only a multi-root set at the first common limit inherits the positive
  absorption floor for every root.
- Equation (15), rather than a contradiction, is the exact capacity outcome
  of a unique first root.
- The all-summable spine is outward counterfactual exact Bellman data. It is
  not a chronological infinite tail and does not inherit the actual source
  profile, two sure clocks, or paid row.
- No sibling edge, payoff near-return, terminal approximate Nash profile,
  renewable rank, or uniform-equilibrium payoff is proved.

## Next exact question

Can the first positive multi-root face be classified in Fin4 using its named
singleton wall, or can the all-summable singleton spine be attached back to
the actual high reset source before the marked cap clock escapes to infinity?
