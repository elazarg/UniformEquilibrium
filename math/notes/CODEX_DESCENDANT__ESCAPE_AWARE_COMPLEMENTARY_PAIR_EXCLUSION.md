# Escape-aware exclusion of complementary-pair period-two profiles

Author: `CODEX_DESCENDANT`

## Status

**Ordinary finite reduction; no candidate table produced.**  For a rational
Fin4 table whose normalized singleton matrix has no homogeneous simplex-LCP
solution, the complementary-pair period-two class has no Zeno escape:
exploitability tending to zero while all four hazards vanish would produce
exactly such a homogeneous solution.

Consequently, for each of the three complementary-pair schedules, exclusion
of all exact period-two Nash points is already a complete exclusion of every
vanishing-exploitability sequence in that schedule.  Exact-point exclusion is
a compact finite rational semialgebraic infeasibility problem and admits a
finite sign-cover certificate.

This supplies a substantially stronger candidate screen than numerical
period-two optimization.  It does not prove that a table passing the screen
has a positive all-behavior gap.  No screened-hard rational table passing all
three exact exclusions is exhibited here.

## 1. Question

Let (I=\operatorname{Fin}4), and fix a partition

\[
 I=A\sqcup B,\qquad |A|=|B|=2.                         \tag{1.1}
\]

Consider two-periodic behavioral profiles in which only the players of (A)
may Quit in phase (A), only the players of (B) may Quit in phase (B),
and every player has one phase hazard (x_i\in[0,1]).

What exact finite condition rules out both

1. an exact Nash point in this class; and
2. a sequence in the same class whose unrestricted terminal exploitability
   tends to zero by sending all hazards to zero?

The second item is essential.  Excluding isolated positive hazards while
leaving a normalized Zeno escape would not be a counterexample-facing screen.

## 2. Exact positive-scale equations

For a phase root (q), write

\[
 s(q)=\prod_i(1-q_i),\qquad
 C(q)=\sum_{\varnothing\ne S\subseteq I}\Pr_q(S)r(S).
\]

For (x=(x_i)_{i<4}), let (q^A(x)) and (q^B(x)) be the two roots selected
by (1.1).  If

\[
 \Delta(x)=1-s(q^A(x))s(q^B(x))>0,                     \tag{2.1}
\]

the two phase values are

\[
 V^A={C(q^A)+s(q^A)C(q^B)\over\Delta(x)},
 \qquad
 V^B=C(q^B)+s(q^B)V^A.                                \tag{2.2}
\]

These are rational functions with rational coefficients when the reward
table is rational.

Let (F_i^A(x)) and (F_i^B(x)) be Quit payoff minus Continue payoff for
player (i) in the two phases, using the opposite phase value from (2.2).
The prescribed box-Nash conditions are

\[
\begin{array}{lll}
x_iF_i^{\phi(i)}\ge0,&
(1-x_i)F_i^{\phi(i)}\le0,
& i<4,\\
F_i^{\bar\phi(i)}\le0,&&i<4,
\end{array}                                             \tag{2.3}
\]

where \(\phi(i)\) is the phase containing player (i).  Thus an interior
hazard satisfies equality at its active phase; zero hazard requires Continue
to be optimal; unit hazard requires Quit to be optimal.  At the other phase
the player is prescribed Continue.

After multiplying by the positive denominator (2.1), (2.3) is a finite list
of rational polynomial inequalities on the compact hazard cube away from the
single all-zero point.

Against periodic opponents, a player's best-response problem is a two-state
periodic optimal-stopping problem.  A deterministic optimal policy exists and
is one of the four phase policies Quit/Quit, Quit/Continue,
Continue/Quit, and Continue/Continue.  Hence (2.3) is equivalent to exact
Nash against the complete behavioral response class, not merely to a local
one-date test.

## 3. Classification of the Zeno boundary

Put

\[
 s_i=r_i(\{i\}),\qquad
 M_{ij}=r_i(\{j\})-r_i(\{i\}).                         \tag{3.1}
\]

### Theorem 3.1

Suppose (x^n\in[0,1]^4\setminus\{0\}) are complementary-pair period-two
hazards satisfying

\[
 \max_i x_i^n\longrightarrow0,
 \qquad
 \operatorname{Expl}_r(x^n)\longrightarrow0.          \tag{3.2}
\]

Then (M) has a homogeneous simplex-LCP solution:

\[
 \exists\lambda\in\Delta(I):
 \quad M\lambda\ge0,
 \qquad \lambda_i(M\lambda)_i=0\quad(i<4).             \tag{3.3}
\]

### Proof

Let

\[
 t_n=\sum_i x_i^n,
 \qquad
 \lambda_i^n={x_i^n\over t_n}.
\]

Pass to a subsequence with \(\lambda^n\to\lambda\in\Delta(I)\).
Over one two-phase period, singleton absorption by (j) has probability

\[
 x_j^n+O(t_n^2),                                       \tag{3.4}
\]

every collision has probability (O(t_n^2)), and total absorption has
probability

\[
 t_n+O(t_n^2).                                         \tag{3.5}
\]

Therefore both phase payoff vectors converge to the same singleton mixture

\[
 u_i=\sum_j\lambda_jr_i(\{j\}).                        \tag{3.6}
\]

For every (i), quitting immediately in either phase has payoff tending to
(s_i).  Since exploitability tends to zero,

\[
 u_i\ge s_i,
 \qquad	ext{hence}\qquad
 (M\lambda)_i=u_i-s_i\ge0.                             \tag{3.7}
\]

If \(\lambda_i>0\), player (i)'s prescribed hazard has first-order weight
bounded below relative to total absorption.  A strict inequality
(u_i>s_i\) would let player (i) remove that first-order Quit mass and gain
a fixed positive amount in the eventual singleton mixture.  Equivalently,
use the exact payoff decomposition

\[
 u_i=\lambda_i s_i+
       \sum_{j\ne i}\lambda_jr_i(\{j\});               \tag{3.8}
\]

and compare the prescribed clock with Never against the same opponents.  The
Never payoff converges to

\[
 {\sum_{j\ne i}\lambda_jr_i(\{j\})\over1-\lambda_i}
\]

when \(\lambda_i<1\).  Vanishing debt forces equality with (u_i), and
therefore (u_i=s_i).  When \(\lambda_i=1\), immediate Quit already yields
(u_i=s_i).  Thus

\[
 \lambda_i(M\lambda)_i=0.                              \tag{3.9}
\]

Equations (3.7) and (3.9) prove (3.3).  Notice that this argument uses the
Never deviation.  Ordinary terminal-law convergence alone would forget the
deleted opponent law when one hazard dominates all others. \(\square\)

### Partial converse boundary witness

If a homogeneous simplex solution has support of cardinality at least two,
it gives the usual normalized singleton rare-hazard upper sequence: use
hazards

\[
 x_i^n=\varepsilon_n\lambda_i,
 \qquad \varepsilon_n\downarrow0,                      \tag{3.10}
\]

in the prescribed phase of player (i).  The endpoint and deleted-law
calculation above shows that unrestricted exploitability tends to zero.  The
same conclusion holds for singleton support \(\{k\}\) when
\(r_k(\{k\})\ge0\).

Without that last sign, the converse is false: when only (k) has leading
hazard, its Never deviation has limiting payoff zero rather than a deleted
singleton mixture, and a negative own singleton payoff is not stable.  No
converse is used below.  The necessary implication in Theorem 3.1 is the
escape-exclusion input.

The forward implication is the only part needed below.  If hazards vanish at
different nested scales, normalization by their sum still yields a possibly
proper-support \(\lambda\); the Never comparison supplies complementarity on
that support.  No equal-rate or full-support assumption is used.

## 4. Hard tables have a positive hazard floor

The screened-hard normal form includes

\[
 \neg\operatorname{SingletonLCPFeasible}(M),            \tag{4.1}
\]

which is exactly the negation of (3.3).  Therefore Theorem 3.1 gives:

> For a screened-hard table, no complementary-pair period-two profile
> sequence can have both exploitability tending to zero and maximum hazard
> tending to zero.

More quantitatively, compactness of the simplex gives a positive residual
margin for (3.3), and the first-order expansion in Section 3 is uniform.
Hence there are \(\tau,c>0\), depending only on the table, such that

\[
 \max_i x_i\le\tau
 \quad\Longrightarrow\quad
 \operatorname{Expl}_r(x)\ge c                         \tag{4.2}
\]

throughout all three complementary-pair schedules.  No numerical value of
\(c\) is needed for the finite reduction.

This is the escape-aware point.  A positive-scale exact-root computation by
itself would miss the all-zero singularity.  The existing no-homogeneous
screen closes that singularity exactly.

## 5. Finite exact exclusion certificate

Fix one complementary-pair schedule in a screened-hard table, and suppose it
has no exact Nash point.  If its exploitability infimum were zero, take a
minimizing hazard sequence.  By (4.2) its maximum hazard is eventually at
least \(\tau\).  Compactness of the hazard cube gives a nonzero limit (x).

There are three cases.

1. **At least two positive limiting hazards.**  After deleting any one
   player, at least one positive limiting opponent hazard remains.  Ordinary
   and every player-deleted periodic law are then continuous at (x), hence
   all four unrestricted caps are continuous.  The limit is an exact Nash
   point.
2. **One positive limiting hazard (x_k=h\in(0,1)).**  Exclusion of a
   homogeneous singleton solution implies that column (k) of (M) has a
   strictly negative entry: for some outsider (i),

   \[
    r_i(\{k\})<r_i(\{i\}).                              \tag{5.1}
   \]

   Player (i) can wait through the host phase and Quit in the other phase
   whenever (k) survives.  Its limiting gain is

   \[
    (1-h)\bigl(r_i(\{i\})-r_i(\{k\})\bigr)>0,           \tag{5.2}
   \]

   contradicting vanishing exploitability.
3. **One sure limiting hazard (x_k=1).**  The screened-hard collision exit
   gives an outsider (o) with

   \[
    r_o(\{k,o\})\ge r_o(\{k\})+\gamma.                 \tag{5.3}
   \]

   Quitting in the host phase therefore has limiting gain at least
   \(\gamma\), again a contradiction.

The only cap-discontinuous nonzero face is the one-host face, and the
no-homogeneous column sign plus the singleton-collision exit consume its two
subcases.  Thus every minimizing sequence yields an exact Nash point after
all, a contradiction.  Therefore

\[
 \inf_{x\in[0,1]^4\setminus\{0\}}
 \operatorname{Expl}_r(x)>0.                           \tag{5.1}
\]

Exact-root exclusion is a finite rational semialgebraic problem: after
clearing (2.1), assert the eight box-Nash inequalities (2.3), the four inactive
inequalities, the cube constraints, and a positive-scale disjunction such as

\[
 x_0+x_1+x_2+x_3\ge\tau.                               \tag{5.4}
\]

For a rational table and rational lower hazard threshold, a finite exact sign
certificate may partition the cube into rational boxes.  On each box it
records one of:

* a prescribed-active box-Nash polynomial with a sign excluding its required
  complementarity face;
* an inactive-phase endpoint polynomial which is strictly positive; or
* a cube/threshold constraint which excludes the box.

Rational interval or Bernstein bounds verify every label.  If the
semialgebraic Nash set is empty, compactness supplies a strict violation
margin, so sufficiently fine subdivision yields such a finite cover.
Equivalently, exact CAD or a Positivstellensatz identity can certify the same
infeasibility.

There are only three unordered partitions of four players into complementary
pairs.  Phase rotation does not create a new profile class.  Three such
infeasibility certificates, together with the no-homogeneous singleton
certificate and the screened-hard singleton-collision exit, therefore exclude
every exact and asymptotically exact complementary-pair period-two profile.

## 6. Combination with existing candidate filters

An exact rational negative-route candidate should now be required to carry:

1. the table-level screened-hard conditions T1--T6 of
   `CODEX_TABLE_NORMAL__FIN4_COUNTEREXAMPLE_ONE_WAY_REWARD_NORMAL_FORM.md`;
2. exact exclusion of pure terminal coalitions and any other explicitly
   enumerated finite-clock/product upper witness;
3. no homogeneous singleton-LCP solution, which closes the common Zeno
   boundary; and
4. one exact semialgebraic infeasibility certificate for each of the three
   complementary-pair schedules.

The four current campaign tables fail item 4.  In fact
`CODEX_DESCENDANT__TRACKED_CORPUS_ALTERNATING_PAIR_EQUILIBRIA.md` gives exact
rational Poincare--Miranda certificates for their interior roots, including
an explicit robust reward neighborhood around every table.

The combined package is still only a stronger candidate filter.  Periods
larger than two, overlapping active pairs, one-quitter cycles, arbitrary
finite clocks, and diffuse escape remain.  The escape-aware exact hierarchy
is still required to turn a surviving table into an all-behavior lower
certificate.

## 7. Search consequence and current outcome

A proof-producing search can use two nested finite layers:

1. reject a proposed rational table as soon as a rational box certifies a
   complementary-pair root; or
2. retain it only after exact sign covers certify absence of roots for all
   three partitions.

The first is an upper witness and is what eliminates the tracked corpus.  The
second does not prove a counterexample, but it prevents the global lower-tree
search from spending time on the dominant chronological escape found in every
tracked chain.

No rational table satisfying the screened-hard normal form and all three
exact exclusions has been produced in this investigation.  Nor is there a
proof that those finite constraints are inconsistent.  The new durable
conclusion is the exact reduction:

\[
\boxed{
\begin{array}{c}
\text{screened-hard table}\\
+\ \text{no exact complementary-pair period-two Nash point}
\end{array}
\Longrightarrow
\text{a uniform positive gap on that entire period-two class}.}
\tag{7.1}
\]

This gap is restricted to the displayed profile class.  It is not a terminal
gap against arbitrary behavioral profiles.

## 8. Exact nonclaims

This note does not provide:

* a rational table passing all of the new filters;
* an all-behavior positive-gap certificate;
* a proof that every screened-hard table has a complementary-pair root;
* a finite-horizon substitute for unrestricted caps; or
* a decision procedure for the Fin4 conjecture.
