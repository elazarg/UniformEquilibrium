# Unique-Continue delayed capacity paths are uniformly approximately floor-safe

Author: `CODEX_SPINOZA`

## Status

**Exact ordinary mathematics; a genuine scope repair, not a Fin4 consumer and
not Lean-checked.**  In an all-player punishment-normal quitting game, a
canonical exact predecessor path whose tail payoffs approach a payoff admitting
the all-Continue exact root is uniformly approximately punishment-floor safe,
with an error controlled only by the source payoff.  The error does not grow
with path length.

Consequently the delayed-capacity paths from
`CODEX_SPINOZA__CANONICAL_CAPACITY_FINITE_HORIZON_USC_AND_DELAYED_ESCAPE`
do satisfy the punishment-floor inequality required of an approximate forward
packet, with tolerance tending to zero, in its unique-all-Continue branch.
They have exact Bellman matching, exact root Nash, and one fixed positive total
charge.  They still do not supply arbitrarily large charge or a literal
connection between paths selected from different actual renewed sources.

## Question

The canonical capacity value is defined on the full payoff box, whereas the
maintained approximate-forward compiler requires every displayed value to lie
above the behavioral punishment floor up to one uniform tolerance.  Does the
moving far-end capacity escape near a unique all-Continue limit meet this
floor requirement?

The answer is yes under punishment normality.  The remaining obstruction is
source-compatible concatenation, not floor admissibility.

## 1. Data and orientation

Let \(I\) be finite and let \(r\) be a finite quitting reward table.  Write

\[
 s_i=r_i(\{i\}),\qquad P_i=\chi_i
\]

for player \(i\)'s singleton payoff and behavioral punishment value.  Assume
every player is punishment-normal:

\[
 P_i\le s_i\qquad(i\in I).                         \tag{1}
\]

An exact predecessor edge from tail \(V\) to current payoff \(W\), carrying
product root \(q\), means

\[
 W=F(q,V),qquad q\text{ is exact endpoint Nash against }V. \tag{2}
\]

This is the orientation of the canonical boxed charged relation: the source
state stores \(V\), and the target state stores its exact predecessor \(W\).

Define the maximal positive floor deficit

\[
 \epsilon(V)=\max_{i\in I}[P_i-V_i]_+.             \tag{3}
\]

## 2. Exact edges do not amplify floor deficit

### Lemma 2.1

For every exact predecessor edge (2),

\[
 \boxed{\epsilon(W)\le\epsilon(V).}                \tag{4}
\]

More precisely, for every player \(i\),

\[
 [P_i-W_i]_+
 \le c_{-i}(q)[P_i-V_i]_+
 \le [P_i-V_i]_+,                                  \tag{5}
\]

where \(c_{-i}(q)\) is the probability that all opponents of \(i\) Continue
at \(q\).

#### Proof

If \(W_i\ge P_i\), the left side is zero.  If \(W_i<P_i\), the checked
floor-violation inequality gives

\[
 0<c_{-i}(q),\qquad
 P_i-W_i\le c_{-i}(q)(P_i-V_i).                    \tag{6}
\]

The left side is positive, so (6) also forces \(P_i-V_i>0\).  Since
\(0<c_{-i}(q)\le1\), (5) follows.  Taking the maximum over \(i\) proves (4).
QED

### Corollary 2.2: arbitrary path length

Let

\[
 V^0\longrightarrow V^1\longrightarrow\cdots\longrightarrow V^H
\tag{7}
\]

be any finite canonical exact predecessor path, with \(V^0\) its tail/source.
Then

\[
 \epsilon(V^t)\le\epsilon(V^0)\qquad(0\le t\le H). \tag{8}
\]

Thus the same error controls every date, independently of \(H\) and of the
total absorption charge.  If \(V^0\ge P\) exactly, every state in (7) is
exactly floor-admissible; this is also the content of the checked constructor
`QuittingPunishmentFloorAdmissibleEdge.ofExactEdge`, iterated along the path.

## 3. An all-Continue exact root is automatically floor-safe

### Lemma 3.1

Suppose all Continue is an exact product root against a payoff \(U_*\). Under
(1),

\[
 \boxed{U_{*,i}\ge s_i\ge P_i\qquad(i\in I).}       \tag{9}
\]

#### Proof

The checked all-Continue endpoint-Nash characterization says precisely that
all singleton payoffs satisfy \(s_i\le U_{*,i}\). Punishment normality (1)
then gives (9).  QED

Uniqueness of the all-Continue root is not needed for (9); it enters only in
the delayed-capacity theorem which produces the far-end paths.

### Corollary 3.2

If \(U_n\to U_*\) and all Continue is exact at \(U_*\), then

\[
 \epsilon(U_n)\longrightarrow0.                    \tag{10}
\]

Every finite exact predecessor path starting at \(U_n\), of arbitrary and
possibly \(n\)-dependent length, therefore satisfies

\[
 V^t_i\ge P_i-\epsilon(U_n)
 \quad\text{for every state, player, and date}.     \tag{11}
\]

## 4. Repair of the delayed-capacity branch

Assume now the unique-all-Continue alternative of the delayed-capacity
theorem. Thus \(U_n\to U_*\), all Continue is the unique exact root at
\(U_*\), and the canonical capacity satisfies

\[
 \phi(U_n)\ge c>0.                                  \tag{12}
\]

For every growing integer \(N\), choose \(n(N)\) large enough that

\[
 \phi_N(U_{n(N)})\le {1\over N},
 \qquad
 \epsilon(U_{n(N)})\le {1\over N}.                 \tag{13}
\]

Choose a finite exact predecessor path \(\Pi_N\) from \(U_{n(N)}\) with total
charge at least \(c/2\). Then:

\[
 \begin{aligned}
 &\operatorname{charge}(\Pi_N)\ge c/2,\\
 &\operatorname{charge}(\Pi_N\upharpoonright N)\le1/N,\\
 &V^t_i\ge P_i-1/N\quad\text{at every state of }\Pi_N,\\
 &\text{every row has exact Bellman matching and zero support-Nash error.}
 \end{aligned}                                      \tag{14}
\]

In particular, for every tolerance \(\delta>0\), some \(\Pi_N\) is a literal
finite approximate-forward packet at tolerance \(\delta\), with exact roots
and total charge at least \(c/2\). Moreover at least \(c/3\) of its charge is
pushed strictly past its first \(N\) rows for all large \(N\).

This removes the floor-admissibility caveat from the delayed branch.  The
packet charge remains bounded below by one constant, not arbitrarily large.

## 5. Fin4 hard-residual adapter

In the Fin4 no-uniform-payoff residual, the checked full normal-core theorem,
followed by
`QuittingLCPClassification.all_punishmentNormal_of_normalCore_eq_univ`, gives
(1) for all four players. Hence the high-capacity payoff sequence in the
small-semantic-seam/unique-all-Continue branch satisfies the hypotheses above.

Combining with the preceding renewal reduction gives an exact dichotomy:

1. the common limit admits a non-all-Continue exact root of positive charge;
   or
2. for every \(\delta>0\), an actual-source-derived tail payoff launches one
   exact finite \(\delta\)-floor packet of fixed positive charge whose charge
   escapes beyond every prescribed finite depth.

The phrase "actual-source-derived" refers only to the tail payoff: the
canonical predecessor path itself is counterfactual exact Bellman data.  No
profile realization or common ancestry between paths at different \(N\) is
asserted.

## Checked sources inspected

- `quittingPunishmentValue_sub_le_continueMass_mul_of_nashBellmanEdge` in
  `UniformEquilibrium/Quitting/Debt/Dynamic/PunishmentFloorViolation.lean`;
- `QuittingPunishmentFloorAdmissibleEdge.ofExactEdge` in
  `UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorAdmissibleChargedRelation.lean`;
- `isZeroQuittingRootNash_allContinue_iff_singleton_le` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`;
- `QuittingLCPClassification.all_punishmentNormal_of_normalCore_eq_univ` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/NormalCorePunishmentNormal.lean`;
- `notes/CODEX_SPINOZA__CANONICAL_CAPACITY_FINITE_HORIZON_USC_AND_DELAYED_ESCAPE.md`,
  frozen at SHA-256
  `652703e08c5add2cfd59320f6174533a82b6ce2aab44c13e955fc82064e4526a`;
- `notes/CODEX_SPINOZA__TWO_SURE_RENEWAL_CAPACITY_BARRIER_MODULUS_FAILURE.md`,
  frozen at SHA-256
  `bf5db04c65cbaa9fc82346773a74537bab2f09a0f1c4ffd7620dad3d25c4a73b`;
- `notes/CODEX_HAHN__TWO_SURE_CLOCK_CHILD_IS_UNIVERSAL_PREFIX_DESCENDANT.md`,
  reviewed at SHA-256
  `8296721fcfad9e373c012b01481ae414ef0f7c0cda86f7a1868a46ec563f82ad`;
  and
- `questions/FIN4_APPROXIMATE_FORWARD_PACKET_OR_CAPACITY_BARRIER.md`.

## Boundary tests and nonclaims

- Punishment normality is essential for inferring floor safety from the
  all-Continue endpoint inequalities. Without \(P_i\le s_i\), an exact
  all-Continue root may sit below the punishment floor.
- The deficit propagation is one-sided and sharp.  It does not make a
  slightly under-floor source exactly admissible; it prevents the error from
  growing.
- The theorem produces one fixed-charge packet at every accuracy, not packets
  of arbitrarily large charge.  Therefore it does not answer the maintained
  approximate-forward-packet question by itself.
- Paths selected at different \(N\) need not be nested. A diagonal limit
  gives the constant all-Continue path at every fixed date and loses the far
  charge.
- The first \(N\) rows carrying vanishing charge does not make the far suffix
  source-compatible with either prescribed sure clock.  Reversing or deleting
  those rows changes the literal tail source.
- No terminal approximate Nash profile, uniform-equilibrium payoff, charged
  return, or renewable finite rank is proved.

## Next exact question

Can the two-sure universal-prefix ancestry identify the far charged suffix of
\(\Pi_N\) with a descendant of the same actual cap child, so that packets for
successive renewals concatenate?  If not, the exact missing equality is
between the counterfactual payoff reached after the vanishing-charge delay and
the complete terminal semantic pair of the next actual horizontal child.
