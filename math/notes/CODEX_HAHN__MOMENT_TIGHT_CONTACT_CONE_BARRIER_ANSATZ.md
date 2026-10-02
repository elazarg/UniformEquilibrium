# Moment-tight contact cones for exact semantic-barrier search

Author: `CODEX_HAHN`

## Status

**Exact finite certificate ansatz in ordinary mathematics; no candidate and
no Lean implementation.**  The prescribed-payoff moment polytope is an
unconditional closed invariant of the semantic prefix action.  Intersecting
the contact-cone template with this polytope removes the artificial
noncarrier states responsible for the raw maximum-debt no-go, without
weakening the all-behavior soundness of a successfully verified barrier.

The resulting invariance test is a finite first-order sentence over the
reals with explicit barycentric variables.  It is strictly narrower than the
previous full-box contact-cone test, but it is not known to have a solution.
It is also not a complete certificate grammar.

## 1. Prescribed-payoff provenance

Fix a rational four-player reward table `r`, normalized by

\[
 |r_i(S)|\le 1
 \qquad(S\ne\varnothing).
\]

Adjoin the Never atom

\[
 r(\varnothing)=0
\]

and define the reward-moment polytope

\[
 M_r=\operatorname{conv}\{r(S):S\subseteq I\}\subseteq[-1,1]^4.
\tag{1}
\]

Every actual prescribed terminal payoff belongs to `M_r`: its terminal law
is a probability distribution on the fifteen nonempty coalitions and Never,
and its payoff is the corresponding reward moment.

More importantly, `M_r` is exactly stable under an arbitrary semantic root.
If

\[
 u=\sum_{S\subseteq I}\lambda_S r(S),
 \qquad \lambda_S\ge0,
 \qquad \sum_S\lambda_S=1,
\tag{2}
\]

and a product root `x` has coalition probabilities `pi_x(S)` and joint
Continue probability `alpha=pi_x(empty)`, then the prefixed prescribed payoff
is

\[
 u'=\sum_{\varnothing\ne S\subseteq I}\pi_x(S)r(S)+\alpha u.
\tag{3}
\]

It has the explicit barycentric representation

\[
 \lambda'_S=\pi_x(S)+\alpha\lambda_S
       \quad(S\ne\varnothing),
 \qquad
 \lambda'_{\varnothing}=\alpha\lambda_{\varnothing}.
\tag{4}
\]

All coefficients in (4) are nonnegative and sum to one.  Thus

\[
 u\in M_r\quad\Longrightarrow\quad u'\in M_r.
\tag{5}
\]

This is an exact law-free shadow of terminal provenance.  It does not assert
that every point of `M_r` is realized by an independent quitting law.

## 2. The moment-tight semantic domain

Write a semantic state as `z=(u,b)` and put

\[
 \delta_i=b_i-u_i,
 \qquad s_i=r_i(\{i\}),
 \qquad \kappa_i=b_i-s_i.
\tag{6}
\]

Define

\[
 \mathcal Z_r^{\rm mom}
 =\{(u,b)\in[-1,1]^4\times[-1,1]^4:u\in M_r\}.
\tag{7}
\]

By (5) and the exact unrestricted-cap recursion, every arbitrary product-root
prefix maps `Z_mom` into itself.  The all-Never semantic point lies in this
domain because its prescribed coordinate is zero.

The box-only no-go for

\[
 \max_i\delta_i\ge\gamma
\]

uses a state with prescribed vector

\[
 u_j=1-\gamma,
 \qquad u_i=1\ (i\ne j).
\tag{8}
\]

There is no reason for (8) to lie in `M_r`; exact moment-separation tests
frequently exclude such abstract payoff vectors.  Therefore that no-go does
not falsify a barrier whose quantifiers are restricted to (7).

## 3. Moment-tight contact-cone cells

Fix rational parameters

\[
 \gamma>0,
 \qquad L\ge0,
 \qquad C\ge0,
\]

and put

\[
 H_\gamma(\kappa)
 =\prod_{i<4}\kappa_i
  -\gamma\sum_{i<4}\prod_{j\ne i}\kappa_j.
\tag{9}
\]

For an active maximum-debt label `a`, let `P_a^mom` consist of the states in
`Z_mom` satisfying

\[
 \begin{aligned}
 &\delta_a\ge\gamma,
   &&\delta_a\ge\delta_i &&(i<4),\\
 &\delta_i+L(\delta_a-\gamma)\ge\gamma
   &&&&(i<4),\\
 &\kappa_i+L(\delta_a-\gamma)\ge\gamma
   &&&&(i<4),\\
 &H_\gamma(\kappa)+C(\delta_a-\gamma)\ge0.
 \end{aligned}
\tag{10}
\]

Set

\[
 P^{\rm mom}(r,\gamma,L,C)=\bigcup_{a<4}P_a^{\rm mom}.
\tag{11}
\]

Every point of (11) has maximum debt at least `gamma`.  At a point where the
maximum debt equals `gamma`, the relaxation terms vanish and (10) gives the
known positive-minimum contact geometry:

\[
 \delta_i=\gamma,
 \qquad \kappa_i\ge\gamma,
 \qquad
 \gamma\sum_i\kappa_i^{-1}\le1.
\tag{12}
\]

The all-Never seed still imposes the same necessary relaxation bound.  If

\[
 m=\max_i\max(0,s_i)
\]

and all-Never belongs to (11), then

\[
 m>\gamma,
 \qquad
 L(m-\gamma)\ge\gamma.
\tag{13}
\]

Moment tightening neither hides nor repairs this seed obstruction.

## 4. Exact finite verification sentence

Membership `u in M_r` can be expressed using sixteen barycentric variables:

\[
 \lambda_S\ge0,
 \qquad
 \sum_{S\subseteq I}\lambda_S=1,
 \qquad
 u_i=\sum_S\lambda_Sr_i(S).
\tag{14}
\]

For each input cell `a`, exact invariance of (11) is the statement

\[
 \begin{array}{c}
 \forall b,x,\lambda:\quad
 \lambda\in\Delta_{16},\quad
 u=\sum_S\lambda_Sr(S),\quad
 (u,b)\in P_a^{\rm mom},\quad x\in[0,1]^4
 \\
 \Longrightarrow
 T_x^r(u,b)\in\bigcup_{c<4}P_c^{\rm mom}.
 \end{array}
\tag{15}
\]

The output moment condition does not need a new existential search: use the
explicit output weights (4).  The cap maximum is encoded by its two endpoint
inequalities and complementary product equality.  After splitting the four
input cells, four output cells, and sixteen cap-branch patterns, (15) is a
finite Boolean combination of rational polynomial inequalities.

Thus a proposed rational table and rational `gamma,L,C` can be verified by
exact real-algebraic certificates.  The current direct-hazard search does not
verify (15): it proves a finite-clock lower tree and invokes the independent
clock-compression theorem.  Its expression engine may be reusable, but the
proof object and quantifier direction are different.

## 5. Soundness

### Proposition 5.1

Suppose `r,gamma,L,C` satisfy:

1. the all-Never semantic point belongs to (11);
2. (15) holds for every input cell; and
3. `gamma>0`.

Then every behavioral profile has unrestricted terminal exploitability at
least `gamma`.

### Proof

The union (11) is closed.  It contains all-Never and is invariant under every
product-root semantic prefix by (15).  Hence it contains every finite root
word with all-Never tail and, by closure, the entire terminal-semantic
carrier.  Every point in (11) has one debt coordinate at least `gamma`.
For actual carrier points, the maximum debt is exactly unrestricted terminal
exploitability.  QED

This is a genuine negative certificate if found.  The moment restriction is
safe because it is independently invariant and contains the seed; it is not
an assumption that actual terminal laws are arbitrary simplex laws.

## 6. Why this is the next finite test

The moment-tight domain imports one piece of global terminal information that
the failed full-box debt barriers forgot, while staying finite and exact.
It also has three practical advantages:

1. failed invariance returns a rational/algebraic state with an explicit
   reward-moment decomposition, not an arbitrary payoff vector;
2. deterministic-root images automatically retain their literal coalition
   reward provenance; and
3. affine separation of `M_r` can cheaply reject impossible input cells
   before any nonlinear root analysis.

A disciplined search should first test (15) on deterministic roots and
one-player root edges.  If a witness exits (11), its barycentric support and
active cap branches say exactly which additional provenance inequality is
missing.  Full quantifier elimination is warranted only for survivors.

## 7. Boundary and nonclaims

- The template remains incomplete.  A true positive carrier need not admit
  the three-parameter presentation (10).
- Membership in `M_r` is necessary but not sufficient for semantic-carrier
  membership; correlated terminal laws can satisfy (14) without product
  stopping-time provenance.
- Verification only on exact Nash roots is unsound.  Condition (15) ranges
  over every independent product root.
- A numerical survivor is not a certificate.  The complete implication (15)
  must be proved exactly.
- No reward table, positive barrier, uniform-equilibrium payoff, or
  counterexample is produced here.

## 8. Sources inspected

- `formalized/QUITTING_CONTROLLER_TESTER_VALUE_AND_BARRIER_DUALITY.md`;
- `formalized/EXACT_FIN4_SCALE_RESOLUTION_AND_COUNTEREXAMPLE_SEMIDECISION.md`;
- `notes/CODEX_MINER__ESCAPE_AWARE_SEMIALGEBRAIC_BARRIER_ENCODING.md`;
- `notes/CODEX_TABLE_NORMAL__FIN4_COUNTEREXAMPLE_ONE_WAY_REWARD_NORMAL_FORM.md`;
- `notes/CODEX_HAHN__CONTACT_CONE_SEMANTIC_BARRIER_ANSATZ.md`;
- `notes/CODEX_HAHN__RAW_MAX_DEBT_SUPERLEVEL_BARRIER_NOGO.md`;
- `Experiments/counterexample_search/exact_semantic_carrier_screen.py`; and
- `Experiments/fin4_exact_search/fin4_exact_search/direct_oracle.py`.

