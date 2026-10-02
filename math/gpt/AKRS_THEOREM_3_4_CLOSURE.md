# Corrected AGKRS Theorem 3.4: direct chronological proof

## Theorem

Let \(\Gamma=(I,r,c)\) be a finite quitting game, where \(c\in\mathbb R^I\)
is the payoff if nobody ever quits. Suppose that for every \(\varepsilon>0\)
there is an \(\varepsilon\)-equilibrium against every unilateral behavioral
deviation. Then one fixed alternative holds for every positive tolerance:

1. **S.1:** stationary approximate equilibria;
2. **S.2:** a sure first-stage quitter followed by an arbitrary behavioral
   punishment whose best-reply value is within the requested tolerance of
   that player's min--max value; or
3. **S.3:** an almost-surely absorbing profile which is sequentially
   approximately perfect at every stage.

Thus the literal corrected AGKRS Theorem 3.4 trichotomy holds. The proof does
not use Simon's classification. It uses the direct source alternative already
available in the repository: S.1, or a family of actual Nash root sequences
whose Nash errors and Never probabilities both tend to zero.

---

## 1. Normalization and the direct source

Subtract \(c_i\) from every terminal payoff of player \(i\). This preserves
all unilateral gains, all three branches, and the punishment error relative
to the min--max value. We therefore assume that the Never payoff is zero.

Write

\[
 a_i:=r_i(\{i\}).
\]

If \(a_i\le0\) for every \(i\), all Continue is an exact stationary
equilibrium: against opponents who always Continue, every behavioral strategy
of player \(i\) gives a convex combination of \(a_i\) and zero. This is S.1.

Otherwise the checked direct extraction gives a family
\(x^k=(x^k_n)_{n\ge0}\) such that

\[
 \epsilon_k\longrightarrow0,\qquad
 x^k\text{ is an }\epsilon_k\text{-equilibrium},\qquad
 \Pr_{x^k}(\theta=\infty)\longrightarrow0.                 \tag{1.1}
\]

Complete each \(x^k\) at a sufficiently late stage by one sure solo exit.
Denote the completed root sequence by \(\bar x^k\). The completion is
absorbing, its global Nash error \(\bar\epsilon_k\) tends to zero, and its
altered terminal mass tends to zero. In particular, every chronological
window bounded away from absorption clock one is eventually unchanged.

Take a chronological-law subsequential limit. Denote its absorption path by
\(\pi\), its cumulative total by \(\widehat\pi\), and its continuation-payoff
path by \(g(t)\). The existing chronological results give:

* absorption-path axioms A.1--A.4;
* exact row perfection at every jump \(t\) with
  \(\widehat\pi_t<1\); and
* for every \(t\in T(\pi)\setminus\{1\}\),

  \[
  a_i\le g_i(t).                                           \tag{1.2}
  \]

The only missing continuous-clock condition is the reverse inequality when
the singleton-\(i\) right derivative is positive.

---

## 2. The finite-block refusal identity

Fix a root-sequence profile \(x\), a player \(i\), and a finite consecutive
block \(B=[a,b)\). Let

* \(s_n\) be the probability that stage \(n\) is reached under \(x\);
* \(q_n\) be player \(i\)'s Quit probability at stage \(n\);
* \(V_n\) be player \(i\)'s prescribed continuation payoff at stage \(n\);
* \(Q_n\) be the payoff from choosing Quit surely at stage \(n\), against the
  displayed opponents; and
* \(C_n\) be the payoff from choosing Continue surely at stage \(n\) and then
  following the original strategy.

Then

\[
 V_n=q_nQ_n+(1-q_n)C_n.                                    \tag{2.1}
\]

Let \(y^i\) force player \(i\) to Continue at every stage in \(B\), and
otherwise follow \(x^i\). Let \(\widetilde s_n\) be the reach probability
under \((y^i,x^{-i})\).

### Lemma 2.1: exact performance difference

\[
 \gamma_i(y^i,x^{-i})-\gamma_i(x)
   =\sum_{n\in B}\widetilde s_n(C_n-V_n)
   =\sum_{n\in B}\widetilde s_nq_n(C_n-Q_n).              \tag{2.2}
\]

#### Proof

Let \(D_n\) be the modified continuation payoff minus \(V_n\). At an
unmodified stage,

\[
 D_n=(1-q_n)d_nD_{n+1},
\]

where \(d_n\) is the probability that all opponents Continue. At a modified
stage,

\[
 D_n=(C_n-V_n)+d_nD_{n+1}.
\]

After stage \(b-1\) the two strategies coincide, so the terminal boundary
term is zero. Backward substitution gives the first equality in (2.2); the
second follows from (2.1). \(\square\)

Forcing Continue can only increase reach, hence

\[
 \widetilde s_n\ge s_n.                                   \tag{2.3}
\]

If

\[
 V_n-Q_n\ge d>0\qquad(n\in B),                            \tag{2.4}
\]

then \(q_n<1\) and

\[
 C_n-Q_n=\frac{V_n-Q_n}{1-q_n}\ge d.
\]

Therefore

\[
 \gamma_i(y^i,x^{-i})-\gamma_i(x)
 \ge d\sum_{n\in B}s_nq_n
 \ge d\,\Pr_x(i\text{ quits alone in }B).                \tag{2.5}
\]

This is one legal behavioral deviation, so an \(\varepsilon\)-equilibrium
forces its left side to be at most \(\varepsilon\).

---

## 3. Positive singleton rate forces indifference

Fix \(t\in T(\pi)\), \(t<1\), and a player \(i\). Assume

\[
 \dot\pi_t(\{i\})>0.                                     \tag{3.1}
\]

Suppose for contradiction that

\[
 g_i(t)>a_i.                                              \tag{3.2}
\]

Choose \(d>0\) so that \(g_i(t)\ge a_i+8d\). Right
continuity gives \(u>t\), as close to \(t\) as needed, such that:

1. the payoff path on the right window remains above \(a_i+7d\);
2. the total conditional absorption in the window is so small that every
   one-row immediate-Quit payoff differs from \(a_i\) by less than \(d\); and
3. the singleton-\(i\) path increment in the window is some fixed \(m>0\).

Choose the two cuts to be continuity points of all relevant chronological
CDFs. Chronological-law convergence gives source blocks \(B_k=[a_k,b_k)\)
whose singleton-\(i\) terminal mass tends to \(m\).

The source continuation value at the final cut tends to the path payoff there.
For a row inside \(B_k\), the probability of absorption before the final cut
is bounded by the window's small conditional mass. Bounded-payoff
decomposition therefore gives, uniformly in that block,

\[
 V^i_{k,n}\ge a_i+6d.                                    \tag{3.3}
\]

Every row's opponent-absorption probability is also bounded by the window's
conditional mass, so

\[
 |Q^i_{k,n}-a_i|<d.                                      \tag{3.4}
\]

Thus \(V^i_{k,n}-Q^i_{k,n}\ge5d\) throughout \(B_k\). Apply
(2.5) to the deviation which forces player \(i\) to Continue on the whole
block. Its gain is eventually at least

\[
 5d\cdot\frac m2>0,
\]

contradicting \(\bar\epsilon_k\to0\). Hence

\[
 \dot\pi_t(\{i\})>0\quad\Longrightarrow\quad g_i(t)\le a_i. \tag{3.5}
\]

Together with (1.2), the chronological limit \(\pi\) is a sequentially
zero-perfect absorption path.

---

## 4. A full jump yields literal S.2

Assume that some jump \(t<1\) satisfies

\[
 \widehat\pi_t=1.                                        \tag{4.1}
\]

The chronological jump approximation supplies source stages with:

* roots \(\xi^k\to\xi\);
* reach probabilities bounded away from zero; and
* shifted global Nash errors \(\delta_k\to0\).

The jump consumes all remaining mass, so \(p(\xi)=1\). Since \(I\) is
finite, some fixed player \(j\) satisfies \(\xi^j=1\). Pass to a
subsequence and write

\[
 q_k:=\xi^{k,j}\longrightarrow1.                         \tag{4.2}
\]

Fix a requested tolerance \(\eta>0\). Let \(m_j\) be player \(j\)'s
behavioral min--max value. By the definition of the infimum, choose an
arbitrary behavioral punishment profile \(P\) with

\[
 \operatorname{BR}_j(P)\le m_j+\eta/4.                   \tag{4.3}
\]

Construct a new profile as follows. At its first stage, retain every
opponent component of \(\xi^k\), make player \(j\) Quit surely, and after
all Continue use \(P\). Let \(M\) bound all payoffs in absolute value.

For a player \(i\ne j\), couple the old shifted profile and the new one. They
can differ only on the event that player \(j\) would have Continued in the
old first row. This event has probability \(1-q_k\), both under prescribed
play and under every behavioral deviation of player \(i\). Hence

\[
 \operatorname{Regret}_i
 \le\delta_k+4M(1-q_k).                                  \tag{4.4}
\]

For player \(j\), let

* \(Q_k\) be her payoff from Quit at the first row;
* \(U_k\) be her old prescribed shifted payoff;
* \(A_k\) be the current-row payoff contribution when she Continues and an
  opponent quits; and
* \(d_k\) be the probability that all opponents Continue.

The old shifted Nash inequality, tested against Continue now followed by an
arbitrary tail best response, gives

\[
 A_k+d_k\operatorname{BR}_j(P_k^{\rm old})
 \le U_k+\delta_k.                                       \tag{4.5}
\]

Since every opponent profile has best-reply value at least \(m_j\), (4.3)
and (4.5) imply

\[
 A_k+d_k\operatorname{BR}_j(P)
 \le U_k+\delta_k+\eta/4.                                \tag{4.6}
\]

Also

\[
 |U_k-Q_k|\le2M(1-q_k).                                  \tag{4.7}
\]

The best unilateral deviation in the new profile is a mixture of Quit now and
Continue now followed by an arbitrary tail deviation. Therefore

\[
 \operatorname{Regret}_j
 \le\delta_k+2M(1-q_k)+\eta/4.                           \tag{4.8}
\]

For large \(k\), (4.4) and (4.8) are below \(\eta\), while (4.3) is the
literal behavioral punishment cap. Thus S.2 holds for every \(\eta>0\).

---

## 5. Without a full jump, a zero-perfect path yields literal S.3

Assume instead

\[
 t\in S(\pi)\quad\Longrightarrow\quad\widehat\pi_t<1.   \tag{5.1}
\]

We prove a standalone strengthening of the standard absorption-path density
construction.

### Proposition 5.1

Let \(\pi\) be a sequentially zero-perfect absorption path satisfying (5.1).
For every \(\alpha\in(0,1/2)\), there is an almost-surely absorbing root
sequence whose every row is \(E_\alpha\)-perfect against its actual tail,
where

\[
 E_\alpha\le K(I,M)\alpha\quad\text{and hence}\quad
 E_\alpha\longrightarrow0.                              \tag{5.2}
\]

#### 5.1 Relative grid

Use the relative grid from the absorption-path density construction:

* isolate and copy exactly every jump whose conditional absorption probability
  is at least \(\alpha\);
* every remaining cell \([s_n,s_{n+1})\) has normalized total absorption

  \[
  p_n:=\frac{s_{n+1}-s_n}{1-s_n}\le\alpha.              \tag{5.3}
  \]

At a copied jump, (5.1) makes the post-jump continuation genuine, and exact
SP.1 applies.

For a small cell define its normalized coalition law

\[
 y_n(S):=\frac{\pi_{s_{n+1}-}(S)-\pi_{s_n-}(S)}{1-s_n},
 \qquad S\ne\varnothing.                                \tag{5.4}
\]

Then \(\sum_Sy_n(S)=p_n\).

#### 5.2 Continuous nonsingleton mass is zero

The nonatomic Stieltjes part of every path coordinate is supported on
\(T(\pi)\). For \(s<t\) in \(T(\pi)\), monotonicity and
\(\widehat\pi_s=s\), \(\widehat\pi_t=t\) give

\[
 0\le\pi_t(S)-\pi_s(S)\le t-s.                           \tag{5.5}
\]

After removing the countable jump atoms, the coordinate measure is therefore
absolutely continuous with density in \([0,1]\). At differentiability points,
the ordinary derivative equals the lower right derivative. A.4 consequently
forces the density of every nonsingleton coordinate to be zero almost
everywhere. Thus all nonsingleton mass in a small cell comes from its small
jumps.

#### 5.3 Collision assignment

Let \(N=|I|\) and \(C_N=\binom N2\). At a small jump with product root
\(q\) and absorption probability \(p(q)<\alpha\),

\[
 \begin{aligned}
 \Pr_q(|S|\ge2)
 &\le\sum_{i<j}q_iq_j\\
 &\le C_Np(q)^2\\
 &\le C_N\alpha p(q).                                   \tag{5.6}
 \end{aligned}
\]

After weighting and summing over the jumps in one cell, its total collision
mass \(c_n\) satisfies

\[
 c_n\le C_N\alpha p_n.                                  \tag{5.7}
\]

Choose once and for all one member \(\chi(S)\in S\) for every
\(|S|\ge2\). Put

\[
 m_{n,i}:=y_n(\{i\})+
   \sum_{\substack{|S|\ge2\\\chi(S)=i}}y_n(S).          \tag{5.8}
\]

Then

\[
 m_{n,i}\ge0,\qquad \sum_im_{n,i}=p_n,                  \tag{5.9}
\]

and replacing \(y_n\) by the singleton law
\(z_n(\{i\})=m_{n,i}\) has \(\ell^1\)-error

\[
 \|z_n-y_n\|_1=2c_n\le2C_N\alpha p_n.                  \tag{5.10}
\]

The assignment preserves strategic support:

\[
 m_{n,i}>0\quad\Longrightarrow\quad y_n(\{i\})>0.       \tag{5.11}
\]

Indeed, if positive assigned mass comes from a collision at a small product
jump, then \(i\) is active there. Since \(p(q)<1\), every other player
Continues with positive probability, so that same jump gives strictly positive
singleton-\(i\) mass.

#### 5.4 Serial solo realization

Fix an order of the players. Replace a small cell by at most \(N\) solo rows.
If masses before player \(i\) total \(a_i\), let only player \(i\) randomize,
with hazard

\[
 h_{n,i}:=\frac{m_{n,i}}{1-a_i}.                         \tag{5.12}
\]

This block delivers singleton mass exactly \(m_{n,i}\), has total survival
\(1-p_n\), and

\[
 0<h_{n,i}\le\frac{p_n}{1-p_n}\le2\alpha               \tag{5.13}
\]

whenever the row is present.

#### 5.5 Uniform future-tail error

Because every block preserves its total absorption, the decoder's survival at
cell boundary \(s_n\) is exactly \(1-s_n\). Summing (5.10) over all future
cells gives

\[
 \begin{aligned}
 \|\text{decoded tail law at }s_n-	ext{path tail law at }s_n\|_1
 &\le\frac{1}{1-s_n}
   \sum_{m\ge n}(1-s_m)2C_N\alpha p_m\\
 &\le2C_N\alpha.                                        \tag{5.14}
 \end{aligned}
\]

Hence the payoff error at every cell boundary is at most

\[
 \tau_\alpha:=2MC_N\alpha.                              \tag{5.15}
\]

At an internal solo row, the remaining part of its current cell absorbs at
most the fraction \(p_n/(1-p_n)\le2\alpha\). Therefore its actual next-tail
payoff differs from the path payoff at the cell's final cut by at most

\[
 D_\alpha:=\tau_\alpha+4M\alpha.                         \tag{5.16}
\]

These estimates are relative to the current survival, so they remain uniform
arbitrarily close to absorption clock one.

#### 5.6 Path-payoff oscillation and local incentives

If two path cuts belong to one small cell, the conditional probability of
absorption between them is at most \(p_n/(1-p_n)\le2\alpha\). Bounded-payoff
decomposition gives

\[
 \|g(u)-g(v)\|_\infty\le4M\alpha.                       \tag{5.17}
\]

For every player \(j\),

\[
 a_j\le g_j(s_{n+1}-)+6M\alpha.                         \tag{5.18}
\]

To see this, choose an absorption point in the cell. At a continuous point,
SP.2(a) gives the inequality without error. At a small jump, SP.1 says that
the pure-Quit endpoint is no larger than the pre-jump mixed payoff; that
endpoint differs from \(a_j\) by at most \(2M\alpha\). Propagate to the
cell endpoint using (5.17).

If \(m_{n,i}>0\), then

\[
 |g_i(s_{n+1}-)-a_i|\le6M\alpha.                         \tag{5.19}
\]

By (5.11), the original cell has positive singleton-\(i\) mass. If a jump
contributes it, player \(i\) is active at that small jump, so exact SP.1 makes
its pre-jump mixed payoff equal to its pure-Quit endpoint, which is within
\(2M\alpha\) of \(a_i\). If the nonatomic singleton part contributes positive
mass, its absolutely continuous density is positive at some differentiability
point; there the path right derivative is positive and exact SP.2 gives
\(g_i=a_i\). Again use (5.17).

#### 5.7 Every decoded row is approximately perfect

Consider an internal solo row whose owner is \(i\).

For player \(i\), Quit yields exactly \(a_i\), while Continue yields the actual
next-tail payoff. By (5.16) and (5.19), the two endpoints differ by at most

\[
 \tau_\alpha+10M\alpha.                                 \tag{5.20}
\]

Both actions have positive probability, so all four perfection inequalities
hold at this error.

For \(j\ne i\), Continue is the only supported action. Since
\(h_{n,i}\le2\alpha\), both the pure-Quit endpoint and the prescribed
Continue endpoint differ from, respectively, \(a_j\) and the actual next-tail
payoff by at most \(4M\alpha\). Equations (5.16) and (5.18) imply

\[
 Q_j\le C_j+\tau_\alpha+18M\alpha.                       \tag{5.21}
\]

The support inequalities for Continue are exact.

At a copied large jump, exact SP.1 against the path continuation and the
boundary error (5.15) give row perfection at error \(2\tau_\alpha\).
Consequently every decoded row is \(E_\alpha\)-perfect with, for example,

\[
 E_\alpha:=(4C_N+18)M\alpha.                            \tag{5.22}
\]

The relative grid tends to clock one, and each emitted block preserves the
path's total absorption. Hence the decoded sequence absorbs almost surely.
This proves Proposition 5.1. \(\square\)

Letting \(\alpha\downarrow0\) proves S.3 for every positive tolerance.

---

## 6. Composition and fixed quantifiers

The direct source alternative gives S.1 or one chronological limit \(\pi\).
Section 3 proves that this fixed limit is zero-perfect. Exactly one of the
following holds:

* \(\pi\) has a full jump, and Section 4 gives S.2 at every tolerance; or
* \(\pi\) has no full jump, and Proposition 5.1 gives S.3 at every tolerance.

The path is selected before the final dichotomy, so the branch category does
not vary with the requested tolerance. The witnesses may depend on the
tolerance, exactly as in AGKRS. This proves the literal S.1/S.2/S.3 conclusion.

The corrected Simon stationarily-generated output is bypassed, not assumed
away. Therefore its diffuse fourth regime is consumed as a corollary of the
stronger direct theorem.

---

## 7. Lean decomposition

A direct formalization has four coherent units.

1. `RootSequenceFiniteBlockRefusal.lean`
   * exact identity (2.2);
   * singleton-mass gain bound (2.5).
2. `RootSequenceAbsorbingCompletionChronologicalSingletonEquality.lean`
   * source-window extraction from a positive right derivative;
   * SP.2(b) contradiction;
   * bundled zero-perfect chronological limit.
3. `AbsorptionPathSequentialPerfectSingletonDecoder.lean`
   * relative grid;
   * continuous-nonsingleton elimination;
   * collision assignment and support preservation;
   * serial solo realization;
   * uniform relative tail bound and row-perfectness estimate.
4. `RootSequenceAbsorbingCompletionAGKRSTrichotomy.lean`
   * full-jump S.2 compiler;
   * no-full-jump S.3 dispatch;
   * arbitrary-Never translation and literature adapter.

No Simon classification theorem, signed-lasso producer, summable-port return,
or real-valued well-founded rank is used.
