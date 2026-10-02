# A contact-cone semantic barrier ansatz for exact Fin4 negative search

Author: `CODEX_HAHN`

## Status

**Exact finite certificate ansatz and a seed obstruction; ordinary
mathematics, not Lean-checked.**  This note does not produce a counterexample.
It gives the smallest barrier template I found which simultaneously:

- is a genuine closed all-product-root invariant semantic certificate;
- forces the known equal-debt, singleton-moat, and harmonic conditions at a
  positive maximum-debt contact;
- admits the finite pure-coalition toggle screens as table constraints; and
- is a finite first-order formula over the reals, hence is exactly checkable.

The completely rigid version is impossible: imposing the contact conditions
throughout the barrier prevents the barrier from containing the all-Never
seed.  More sharply, the all-Never seed gives an explicit lower bound on the
linear relaxation slope.  Thus any useful finite barrier of this type must
have a genuine interior layer between all-Never and its minimum-debt contact.

No rational table or positive barrier has been found here.  Failure of one
bounded contact-cone degree or coefficient box would not prove existence of a
uniform-equilibrium payoff.

## 1. Exact question

Let `I = Fin 4`, let the rational reward table satisfy

\[
 |r_i(S)|\le 1
 \qquad(S\ne\varnothing),
\]

and let

\[
 z=(u,b)\in\mathcal Z=[-1,1]^4\times[-1,1]^4.
\]

Write

\[
 \delta_i(z)=b_i-u_i,
 \qquad
 s_i=r_i(\{i\}),
 \qquad
 \kappa_i(z)=b_i-s_i.
\tag{1}
\]

For a product root `x in [0,1]^4`, let `T_x^r z` be the exact semantic-prefix
map, including the unrestricted behavioral-cap maximum.  Can one choose a
rational table and a small rational semialgebraic set `P` such that

\[
 e_\infty(r)\in P,
 \qquad
 T_x^r(P)\subseteq P\quad\hbox{for every product root }x,
 \qquad
 \max_i\delta_i(z)\ge\gamma>0\quad(z\in P)?
\tag{2}
\]

Such data are already a complete all-behavior counterexample certificate.
The roots in (2) are arbitrary controller roots, not only exact Nash roots.

## 2. Why the raw floor and the rigid contact set are the wrong endpoints

The raw set

\[
 P_{\rm raw}=\{z:\max_i\delta_i(z)\ge\gamma\}
\tag{3}
\]

is a legitimate but unnecessarily large template.  It contains many
noncarrier states with only one active debt coordinate.  The one-player
small-root calculation which proves equal debts at an actual barrier contact
does not apply uniformly to all of (3); rather, it explains why an invariant
barrier must remove or control those artificial boundary points.

At the opposite extreme, define the rigid contact set by requiring

\[
 \delta_i\ge\gamma,
 \qquad
 \kappa_i\ge\gamma
 \qquad(i<4)
\tag{4}
\]

everywhere.  This incorporates the known contact conclusions, but it cannot
contain all-Never for any positive `gamma`.

Indeed the all-Never semantic point is

\[
 e_\infty=(0,b^\infty),
 \qquad
 b_i^\infty=\max\{0,s_i\}.
\tag{5}
\]

At this point

\[
 \delta_i(e_\infty)=\max\{0,s_i\},
 \qquad
 \kappa_i(e_\infty)=\max\{0,-s_i\}.
\tag{6}
\]

For every player, at least one of the two quantities in (6) is zero.  Hence
(4) fails for every `gamma > 0`.

This is not merely a defect of one table.  It is a structural incompatibility
between the mandatory all-Never seed and globalizing the minimum-contact
conditions.

## 3. The contact-cone template

Choose rational parameters

\[
 \gamma>0,
 \qquad L\ge0,
 \qquad C\ge0.
\]

For the harmonic contact polynomial put

\[
 H_\gamma(\kappa)
 =\prod_{i<4}\kappa_i
  -\gamma\sum_{i<4}\prod_{j\ne i}\kappa_j.
\tag{7}
\]

For each possible active maximum-debt coordinate `a`, define the basic closed
cell `P_a(gamma,L,C)` by

\[
 \begin{aligned}
 &z\in\mathcal Z,\\
 &\delta_a\ge\gamma,
   \qquad \delta_a\ge\delta_i &&(i<4),\\
 &\delta_i+L(\delta_a-\gamma)\ge\gamma &&(i<4),\\
 &\kappa_i+L(\delta_a-\gamma)\ge\gamma &&(i<4),\\
 &H_\gamma(\kappa)+C(\delta_a-\gamma)\ge0.
 \end{aligned}
\tag{8}
\]

Set

\[
 P(\gamma,L,C)=\bigcup_{a<4}P_a(\gamma,L,C).
\tag{9}
\]

This is a finite union of four basic closed rational semialgebraic sets.
Every point in it has maximum debt at least `gamma`.

### Proposition 3.1: the boundary is the required contact face

If `z in P(gamma,L,C)` and

\[
 \max_i\delta_i(z)=\gamma,
\]

then

\[
 \delta_i(z)=\gamma\quad(i<4),
 \qquad
 \kappa_i(z)\ge\gamma\quad(i<4),
 \qquad
 \gamma\sum_{i<4}{1\over\kappa_i(z)}\le1.
\tag{10}
\]

#### Proof

Choose a cell `P_a` containing `z`.  Its first line in (8) and the assumed
maximum give `delta_a = gamma`, so every relaxation term
`L(delta_a-gamma)` vanishes.  The next two lines of (8) give
`delta_i >= gamma` and `kappa_i >= gamma`; maximality gives
`delta_i <= gamma`.  Thus all debts equal `gamma`.

Every `kappa_i` is positive, so division of `H_gamma(kappa) >= 0` by their
product gives the harmonic inequality in (10).  QED

The finite pure-coalition shadow should be imposed on the reward table, not
on every semantic state.  For each nonsingleton coalition `S`, require the
finite disjunction

\[
 \begin{split}
 &r_i(S\setminus\{i\})-r_i(S)\ge\gamma
        \quad\hbox{for some }i\in S,\\
 &\hspace{22mm}\text{or}\\
 &r_i(S\cup\{i\})-r_i(S)\ge\gamma
        \quad\hbox{for some }i\notin S.
 \end{split}
\tag{11}
\]

These are the exact member-leave/outsider-join alternatives forced by a
positive maximum-debt floor at the deterministic root `S`.  They are
necessary search filters, not a substitute for (2).

## 4. Exact all-Never seed obstruction

Put

\[
 m=\max_i\max\{0,s_i\}=max_i\delta_i(e_\infty).
\tag{12}
\]

### Theorem 4.1: a positive contact cone needs quantitative relaxation

If

\[
 e_\infty\in P(\gamma,L,C),
\]

then

\[
 m>\gamma,
 \qquad
 L(m-\gamma)\ge\gamma.
\tag{13}
\]

In particular `L > 0`, and the rigid template `L=0` is impossible.

#### Proof

Let `e_infty` lie in cell `P_a`.  Then `delta_a(e_infty)=m` after choosing
an active cell, and put `h=m-gamma >= 0`.

For each player `i`, the debt and moat cone inequalities in (8) give

\[
 \delta_i(e_\infty)+Lh\ge\gamma,
 \qquad
 \kappa_i(e_\infty)+Lh\ge\gamma.
\tag{14}
\]

By (6), at least one of the two first terms in (14) is zero.  Therefore
`Lh >= gamma`.  Since `gamma > 0`, both `L > 0` and `h > 0`, proving (13).
QED

Equivalently, every feasible slope obeys the explicit lower bound

\[
 L\ge {\gamma\over m-\gamma}.
\tag{15}
\]

There is a similar optional bound on the harmonic relaxation.  If exactly
one solo reward is nonnegative and the other three are negative, then exactly
one `kappa_i(e_infty)` vanishes and (7) gives

\[
 H_\gamma(\kappa(e_\infty))
 =-\gamma\prod_{s_j<0}(-s_j).
\]

Consequently seed membership also requires

\[
 C(m-\gamma)
 \ge\gamma\prod_{s_j<0}(-s_j).
\tag{16}
\]

If at least two solos are nonnegative, the harmonic polynomial at all-Never
is zero and gives no additional seed restriction.

## 5. Finite exact certificate sentence

For fixed rational `r`, `gamma`, `L`, and `C`, the following are finite
first-order sentences over real closed fields:

1. `gamma > 0`, normalization of `r`, and the toggle disjunctions (11);
2. `e_infty(r) in P(gamma,L,C)`;
3. for every cell index `a`, state `z`, and root `x`,

   \[
   z\in P_a(\gamma,L,C),\ x\in[0,1]^4
   \Longrightarrow
   T_x^r z\in\bigcup_{c<4}P_c(\gamma,L,C).
   \tag{17}
   \]

The semantic prefix uses the exact product-root polynomials.  For each cap
coordinate its maximum can be encoded by a fresh output coordinate `b'_i`
and the three polynomial conditions

\[
 b'_i\ge Q_i,
 \qquad b'_i\ge C_i,
 \qquad (b'_i-Q_i)(b'_i-C_i)=0.
\tag{18}
\]

The four output cells in (17) are a finite disjunction.  Thus quantifier
elimination, exact cylindrical decomposition, or a rational
Positivstellensatz proof can verify the complete implication.  Root sampling
does not.

### Proposition 5.1: soundness

Any rational data satisfying items 1--3 are an all-behavior positive-gap
certificate:

\[
 \operatorname{Expl}_r(\sigma)\ge\gamma
 \qquad\hbox{for every behavioral profile }\sigma.
\tag{19}
\]

#### Proof

The set `P` is closed, contains all-Never, and is invariant under every
product-root semantic prefix.  The terminal-semantic carrier is the smallest
closed set with those two properties, so every actual semantic pair lies in
`P`.  Equation (8) gives one debt coordinate at least `gamma` at every point
of `P`.  The unrestricted terminal exploitability is exactly the maximum
debt coordinate.  QED

## 6. Relation to the executable exact search

The existing `fin4_exact_search` lower certificate is not this object.  Its
`DirectHazardLowerTreeCertificate` subdivides the finite-clock hazard cube
and proves a lower threshold for an exact max-polynomial exploitability
objective.  The analytic `24/N` compression theorem then transports that
finite-clock threshold to all behavioral profiles.  It is complete at every
fixed rational scale through a parallel upper-profile enumeration.

By contrast, (17) is a direct eight-dimensional semantic induction
certificate with the reward table and barrier coefficients potentially
endogenous.  The current Python verifier has no declaration or JSON surface
for such a certificate.  Reusing its interval-expression DAG would be
possible, but its present lower-tree soundness theorem does not verify a
universal set-invariance implication.

This distinction matters operationally:

- a table proposed by contact-cone synthesis can be handed unchanged to the
  existing complete exact resolver;
- a contact-cone proof itself needs a separate exact real-algebraic checker;
- failure of contact-cone synthesis says nothing about the table's exact
  finite-clock lower tree, and failure of one lower-tree run says nothing
  about the existence of a simple contact cone.

## 7. Boundary tests

1. **All-Never.**  Theorem 4.1 rejects the tempting globally rigid use of the
   contact equalities.  A synthesis run that accepts `L=0` has encoded the
   seed incorrectly.
2. **Local contact-sharp regression.**  The table
   `r_i(S)=-1` when `i in S` and `0` otherwise has a local forward orbit with
   equal debts, sharp harmonic moats, unique all Continue, and paid debt
   transfer.  Its global all-Never point has zero debt.  Condition 2 rejects
   it for every positive `gamma`.
3. **Universal roots.**  Exact-Nash-root invariance is insufficient.  The
   quantifier in (17) ranges over the full product-root cube.
4. **Complete caps.**  Replacing (18) by a finite-horizon, stationary, or
   prescribed-strategy cap invalidates Proposition 5.1.
5. **Toggle screens.**  Conditions (11) alone admit known exact-equilibrium
   regressions.  They only reduce the table search and do not certify (17).
6. **Template incompleteness.**  A true positive carrier floor has a closed
   invariant certificate, namely the carrier itself.  No theorem says it has
   the contact-cone presentation (8)--(9).

## 8. Narrow source audit

The exact semantic action and finite semialgebraic certificate language were
read from `CODEX_MINER__ESCAPE_AWARE_SEMIALGEBRAIC_BARRIER_ENCODING` and the
checked controller--tester barrier record.  The smallest-invariant-set fact is
`terminalSemanticCarrier_eq_closure_neverGeneratedSemanticReachable`; exact
prefix closure is `quittingTerminalSemanticPrefix_mem_carrier`.

The contact equations used in Proposition 3.1 are the maximum-debt contact
consequences recorded in the global-route and noncarrier-excursion audits:
equal four debts, singleton moats, the harmonic inequality, and the finite
pure-root toggle floor.  They are used here only as necessary boundary
conditions, not as a producer of a counterexample.

The exact Python interface inspected was
`Experiments/fin4_exact_search/fin4_exact_search/direct_oracle.py`.  Its
verified object is a finite-clock hazard subdivision tree, not a semantic
invariance certificate.

## 9. Next exact test

Fix a small rational screened-hard reward family and enumerate rational
`gamma`, `L`, and `C` satisfying the seed bound (15).  Check (17) first on all
sixteen deterministic roots and on the one-player root edges.  Any failure
returns an exact state/root counterexample and should refine (8) with one
additional affine face.  Only survivors should be sent to full real-algebraic
verification of (17) and to the existing all-behavior exact resolver.

The first theorem-level target is either:

- one rational table and exact proof of (17), which settles Fin4 negatively;
  or
- an exact impossibility theorem for the whole three-parameter contact-cone
  family, which would show that positive barriers require more than a
  linearly relaxed contact geometry.

