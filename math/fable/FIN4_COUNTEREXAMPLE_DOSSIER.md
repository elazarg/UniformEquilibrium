# The four-player quitting counterexample: problem and fact base

Reference document. It contains the problem statement and the established
facts only; analysis and construction attempts live in separate documents.
Everything is stated in ordinary mathematical language and is self-contained.

Status labels follow a three-level convention: **(checked)** — a
machine-verified proof exists; **(recorded)** — a rigorous
ordinary-mathematics proof is on record, not machine-verified; **(open)** —
open. A fact whose full proof appears in this text can be re-derived from
the text alone.

---

## 0. The problem

**Conjecture \(P\).** Every finite quitting game (defined in §1) has a
uniform-equilibrium payoff. \(P\) is settled affirmatively for at most three
players; \(P(4)\), the four-player case, is open, and a four-player
counterexample would transport to every larger player set **(checked)**.

**The question this dossier serves.** Facts R1–R14 of §6 are necessary
conditions on a hypothetical four-player counterexample. The question: is
their conjunction contradictory (which would prove \(P(4)\)), or does it
delimit a class of counterexamples — and in either case, exactly what
remains between the two outcomes?

---

## 1. The game

Fix a finite player set \(I\); the main case is \(I=\{0,1,2,3\}\). A
*quitting game* is a reward table

\[
r : \{\,S \subseteq I : S \neq \varnothing\,\} \to \mathbb{R}^I,
\qquad r_i(S) = \text{payoff of } i \text{ when exactly } S \text{ quits
first}.
\]

Play proceeds in stages \(t=0,1,2,\dots\); each stage every player
simultaneously chooses Continue or Quit. At the first stage whose quitter
set \(S\) is nonempty the game ends and pays \(r(S)\); if nobody ever quits
every player receives \(0\). Rewards are bounded: \(|r_i(S)|\le R\).

With one live state and perfect monitoring, a behavioral strategy of \(i\)
is a hazard sequence \(x_{t,i}\in[0,1]\) (quit probability at stage \(t\)
given live), equivalently a stopping law
\(\lambda_i\in\Delta(\mathbb{N}\cup\{\infty\})\) for the planned quit date
\(T_i\), independent across players. A profile is
\(\sigma=(\lambda_i)_{i\in I}\). With \(T=\min_i T_i\) and
\(S_T=\{i:T_i=T\}\), the terminal payoff is

\[
U_i(\sigma)=\mathbb{E}\bigl[r_i(S_T)\,\mathbf{1}_{\{T<\infty\}}\bigr].
\]

## 2. Uniform equilibrium and the terminal reduction

\(v\in\mathbb{R}^I\) is a *uniform-equilibrium payoff* when for every
\(\varepsilon>0\) there are a profile \(\sigma_\varepsilon\) and a horizon
\(T_0\) such that for all \(T\ge T_0\): \(\sigma_\varepsilon\) is an
\(\varepsilon\)-Nash equilibrium of the \(T\)-stage expected-average game
and its \(T\)-stage average payoff is within \(\varepsilon\) of \(v\). The
target \(v\) is fixed before \(\varepsilon\); a deviation replaces a
player's entire behavioral strategy, including Never and arbitrarily late
randomized stopping.

Write \(B_i(\sigma)=\sup_{\nu}U_i(\sigma[i\leftarrow\nu])\), the
unrestricted deviation cap. Since \(U_i\) is affine in \(\lambda_i\), pure
dates and Never suffice:
\(B_i(\sigma)=\sup_{t\in\mathbb{N}\cup\{\infty\}}
U_i(\sigma[i\leftarrow\delta_t])\).

**Fact 2.1 (positive endpoint; checked).** A uniform-equilibrium payoff
exists iff for every \(\varepsilon>0\) some profile is an
\(\varepsilon\)-Nash equilibrium of the terminal game:
\(B_i(\sigma)\le U_i(\sigma)+\varepsilon\) for all \(i\).

**Fact 2.2 (negative endpoint; checked).** No uniform-equilibrium payoff
exists iff there is one fixed \(\gamma>0\) with

\[
E_r(\sigma)=\max_i\bigl(B_i(\sigma)-U_i(\sigma)\bigr)\;\ge\;\gamma
\qquad\text{for every behavioral profile }\sigma.
\]

"Counterexample" below always means a table with this property.

## 3. Debt, carrier, and dependence on the table

Set \(d_i(\sigma)=B_i(\sigma)-U_i(\sigma)\ge0\),
\(D(\sigma)=\sum_i d_i(\sigma)\), \(D_*=\inf_\sigma D(\sigma)\),
\(\eta(r)=\inf_\sigma E_r(\sigma)\). Then
\(E_r\le D\le|I|\,E_r\), so a counterexample is equivalently \(D_*>0\).

**Fact 3.1 (carrier; checked).** The closure of
\(\{(U(\sigma),B(\sigma),\operatorname{law}(\sigma))\}\) in
\(\mathbb{R}^I\times\mathbb{R}^I\times\Delta(\Omega)\), with
\(\Omega=\{\text{Never}\}\cup\{S:\varnothing\ne S\subseteq I\}\), is
compact; \(D\) extends continuously and attains \(D_*\) at a carrier point
(not necessarily at a profile). Finite-support product profiles are dense:
their exploitability infimum equals the full behavioral one. A carrier
point is a *semantic pair* \(X=(u,c)\) with debts \(d_i(X)=c_i-u_i\), plus
its terminal law \(\mu\).

**Fact 3.2 (Lipschitz dependence; proof included).** For tables \(r,r'\) on
the same players,

\[
|\eta(r)-\eta(r')|\;\le\;2\,\lVert r-r'\rVert_\infty .
\]

*Proof.* For a fixed profile and fixed deviation, prescribed and deviation
payoffs are expectations of reward coordinates over one outcome law, so each
moves by at most \(\lVert r-r'\rVert_\infty\); take suprema over deviations,
maxima over players, infima over profiles. ∎

Consequences: the counterexample set \(\{r:\eta(r)>0\}\) is **open**; if it
is nonempty it contains rational tables and is not a measure-zero
exceptional family; and proving \(P(4)\) on any dense class of tables proves
it for all four-player tables.

## 4. The singleton comparison matrix and complementarity classes

### 4.1 Normalization

\[
M_{ij}=r_i(\{j\})-r_i(\{i\}),\qquad M_{ii}=0 .
\]

This is the table after translating each player \(i\)'s payoffs by
\(-r_i(\{i\})\) at all outcomes; in normalized terms \(i\)'s payoff from
quitting alone is \(0\) and from perpetual Never is \(-r_i(\{i\})\). The
translation preserves all equilibrium notions.

### 4.2 Complementarity problems

For \(M\in\mathbb{R}^{I\times I}\) and \(q\in\mathbb{R}^I\):

- **Standard LCP:** find \(z\ge0\) with \(w=q+Mz\ge0\) and \(z_iw_i=0\)
  for all \(i\). \(M\) is a *Q-matrix* when solvable for every \(q\).
- **Projective (simplex) LCP:** find \(z_0\ge0\), \(z\ge0\),
  \(z_0+\sum_iz_i=1\), \(w=z_0q+Mz\ge0\), \(z_iw_i=0\). \(M\) is
  *projective-Q* when solvable for every \(q\).
- **Homogeneous branch:** a projective solution with \(z_0=0\): some
  \(z\in\Delta(I)\), \(Mz\ge0\), \(z_i(Mz)_i=0\).
- **Split (checked):** projective-Q \(\iff\) Q or homogeneous-feasible.
- **\(\bar Q\):** every nonempty principal submatrix is projective-Q.

### 4.3 Low-dimensional classification (zero diagonal)

- Size 1: \([0]\) is homogeneous-feasible, hence projective-Q; never Q.
- Size 2, \(\begin{pmatrix}0&a\\b&0\end{pmatrix}\): Q \(\iff a>0\wedge
  b>0\); homogeneous \(\iff a\ge0\vee b\ge0\); hence projective-Q fails
  iff \(a<0\wedge b<0\) — a *mutual preemption pair*. *Proof.* For
  \(a,b>0\): \(q\ge0\) take \(z=0\); \(q_1<0\le q_2\) take
  \(z=(0,-q_1/a)\); \(q<0\) take \(z=(-q_2/b,-q_1/a)\). Conversely
  \(q=(-1,0)\) forces \(az_2=1\). Homogeneous: test \(z=e_1,e_2\); a mixed
  \(z\) forces \(a=b=0\). ∎
- Size 3 **(checked)**: with zero diagonal and no homogeneous solution, Q
  holds iff the six off-diagonal signs form one of the two strict directed
  3-cycles and the product of the three positive entries strictly exceeds
  the product of the absolute values of the three negative entries.
- Sign facts: Q forces a strictly positive entry in every row (solve
  \(q\equiv-1\)); no-homogeneous forces a strictly negative entry in every
  column (else \(z=e_j\)); with the full matrix Q and singletons always
  projective-Q, a \(\bar Q\)-failure occurs at a principal set of size
  exactly \(2\) or \(3\).

### 4.4 Punishment and normal layers

\(\operatorname{Pun}_i=\inf_{\sigma_{-i}}\sup_{\lambda_i}
U_i(\sigma_{-i},\lambda_i)\); player \(i\) is *normal* when
\(\operatorname{Pun}_i\le r_i(\{i\})\). Ceiling (proof: opponents
all-Continue): \(\operatorname{Pun}_i\le\max(r_i(\{i\}),0)\); so
\(r_i(\{i\})\ge0\) makes \(i\) normal. The \(\alpha\)-layers are
\(I_0=I\), \(I_{n+1}=\{i\in I_n:\exists j\in I_n,\ j\ne i,\ M_{ij}\le0\}\);
the *normal core* is \(K=\bigcap_nI_n\).

### 4.5 The five-regime gate (checked)

Every table lies in exactly one regime, computed from \(M\) and \(M_K\):

1. \(K=\varnothing\);
2. \(M_K\) homogeneous-feasible;
3. no homogeneous, \(M_K\) not Q;
4. \(M_K\) Q, no homogeneous, full \(M\) is \(\bar Q\);
5. \(M_K\) Q, no homogeneous, full \(M\) **not** \(\bar Q\).

Each of regimes 1–4 admits a uniform-equilibrium payoff **(checked)**;
every counterexample lies in regime 5, the *residual hard class*.

A further positive chamber cuts across the regimes **(checked)**: if
\(n\ge2\), every solo is nonnegative, and every
coalition has nonpositive aggregate reward
(\(\sum_ir_i(S)\le0\) for all \(S\)), a uniform-equilibrium payoff
exists. The proof sums the singleton moat of R15 below against the sign
of the social payoff. More generally **(checked)**, it suffices that
some strictly positive costate \(\theta\) satisfies
\(\theta\cdot r(S)\le0\) for every coalition and \(\theta\cdot s\ge0\) —
a polyhedral chamber, one linear-programming check per table. A
counterexample therefore admits no such costate.

## 5. Exact Nash–Bellman geometry

For a product row \(x\in[0,1]^I\) and continuation \(w\in\mathbb{R}^I\):

\[
F_x(w)_i=\sum_{\varnothing\ne S\subseteq I}\pi_x(S)\,r_i(S)
+\pi_x(\varnothing)\,w_i,
\qquad
\pi_x(S)=\prod_{i\in S}x_i\prod_{j\notin S}(1-x_j).
\]

\(x\) is an *exact Nash root against \(w\)* when
\(F_{x[i\leftarrow z]}(w)_i\le F_x(w)_i\) for all \(i\), \(z\in[0,1]\).
The *canonical box* is \(\{w:\lVert w\rVert_\infty\le R\}\). A *canonical
exact spine* is a sequence \((v_t,x_t)_{t\ge0}\) with every \(v_t\) in the
canonical box, \(v_t=F_{x_t}(v_{t+1})\), and \(x_t\) exact Nash against
\(v_{t+1}\); a *canonical block* is the finite version, with charge
\(H(B)=\sum_{t<L}\sum_ix_{t,i}\) and seam
\(\Delta(B)=\lVert v_L-v_0\rVert_\infty\). A *phantom* is a constant spine
\((b,C)^\infty\), \(C\) = all-Continue; it is exact iff
\(r_i(\{i\})\le b_i\) for all \(i\) (immediate from
\(F_{C[i\leftarrow z]}(b)_i=zr_i(\{i\})+(1-z)b_i\)).

**Fact 5.1 (one persistent clock compiles; checked).** If a canonical exact
spine has exactly one player \(p\) with \(\sum_tx_{t,p}=\infty\) and
\(\sum_tx_{t,j}<\infty\) for \(j\ne p\), and \(p\) is punishment-normal,
then \(r(\{p\})\) is a uniform-equilibrium payoff. *Sketch:* the outsider
clocks are summable, so the Bellman recursion contracts
\(v_t\to r(\{p\})\); projecting late rows to actual solo rows bounds every
outsider's full stopping-law cap against the stationary solo profile by
\(r_i(\{p\})+o(1)\) (any stopping law mixes one memoryless quit value with
the ride-along value); a finite solo prefix followed by an actual
\(\delta\)-punishment of \(p\) covers \(p\)'s Never deviation by the
punishment, not by a phantom continuation.

**Fact 5.2 (two persistent clocks compile; checked).** A canonical exact
spine with two distinct players of divergent clocks yields a
uniform-equilibrium payoff.

**Fact 5.3 (summable spines end in phantoms).** If all clocks of a
canonical exact spine are summable, then \(v_t\to b\) with
\(r_i(\{i\})\le b_i\), \(x_t\to C\), and the shifted spine converges to the
phantom \((b,C)^\infty\) **(recorded)**. If in addition the limit lies in
an open set on which all-Continue is the unique exact root, the spine is
constant all-Continue from time zero **(checked)**.

**Fact 5.4 (minimal-component alternative; recorded).** Every nonempty
compact shift-invariant family of canonical exact spines contains a spine
with a divergent clock or contains a phantom. *Sketch:* on a minimal
subfamily, either the one-stage activity is somewhere positive — then
minimality forces visits with bounded gaps and one clock diverges — or all
roots are all-Continue and exactness forces \(b\ge\) the solo vector.

**Fact 5.5 (near-returns amplify; recorded).** If canonical blocks
\(B_n\) exist with \(H(B_n)>0\), both endpoints converging to one common
vector, and \(\Delta(B_n)/H(B_n)\to0\), then for every \(\varepsilon>0\)
there is an infinite chronology with total Bellman-plus-Nash defect below
\(\varepsilon\) and one fixed player with a divergent clock; with Facts
5.1–5.2 this yields a uniform-equilibrium payoff.

**Fact 5.6 (ballistic obstruction; elementary).** Convergence of a cap
orbit does not produce near-returns: in the scalar model
\(c_{t+1}-c_t=h_td\), \(h_t>0\), \(\sum h_t<\infty\), every window
satisfies \(|c_b-c_a|/\sum_{t\in[a,b)}h_t=|d|\). Displacement proportional
to charge on every window is consistent with convergence.

## 6. Necessary conditions on a four-player counterexample

Throughout, \(r\) is a four-player counterexample with gap \(\gamma\),
minimum debt \(D_*>0\), rewards bounded by \(R\).

**R1 (checked).** \(\eta(r)\ge\gamma>0\); \(D_*>0\) attained on the compact
carrier; finite-clock density; no terminal \(\varepsilon\)-Nash profile for
\(\varepsilon<\gamma\); no exact terminal Nash profile of any kind.

**R2 (checked).** By Fact 3.2 a counterexample may be taken normalized and
rational. The set of rational counterexample tables is recursively
enumerable through exact rational certificates of a positive lower bound on
\(\eta\); a true counterexample is eventually certified; nontermination
proves nothing.

**R3 (checked).** \(r\) lies in regime 5 with: normal core \(K=I\); every
player punishment-normal; \(M\) a Q-matrix with no homogeneous solution and
a \(\bar Q\)-failure at a principal set of size 2 or 3; and a full-support
singleton packet: weights \(m\in\Delta(I)\) with
\(m_j\ge(1+6R/\gamma)^{-1}\) for every \(j\), and a target \(u\) with,
coordinatewise, \(r_i(\{i\})\le u_i\), \(\operatorname{Pun}_i\le u_i\),
\(u_i\le\sum_jm_j\,r_i(\{j\})\), each positively weighted owner exactly
indifferent at their own coordinate.

**R4 (checked).** For every \(j\) there is \(o\ne j\) with
\(r_o(\{j,o\})\ge r_o(\{j\})+\gamma\); the choices form a fixed-point-free
map on the four players. Some owner has \(r_j(\{j\})\ge\gamma\), and that
owner's singleton row carries zero owner debt with the collider's full gap
as an actual legal gain.

**R5 (checked).** Every carrier point attaining \(D_*\) has a law giving
positive mass to some nonempty coalition. The point has a source-faithful
causal realization: actual profiles whose semantic pairs converge to the
minimum, laws converging to the selected law, the atom occurring at literal
finite dates, arbitrarily deep exact cap–Nash prefixes retained. The atom
need not be current-root absorption: it may live in a remote suffix while
every marginal stopping law converges weakly to Never (the
"relative-timing bubble" is permitted).

**R6 (checked, Research).** The six entrance leaves of the
source-preserving atlas collapse: every surviving minimum-atom source
produces a literal source-attached singleton endpoint and then a forced
pure pair. After subsequence stabilization there are fixed distinct roles
\(j\) (singleton owner), \(o\) (forced partner), \(p\) (payer) and
cofinally many actual marked rows with: the same pure pair \(\{j,o\}\);
reached mass at least a fixed \(\lambda>0\); zero marked defect for \(o\);
positive marked defect for \(p\); an actual unilateral endpoint replacement
for \(p\) gaining at least a fixed \(g>0\), subtracted exactly from
\(p\)'s debt; lossless routing of the marked mass; the complete post-row
behavioral tail preserved verbatim; provenance from the one selected
minimum law.

**R7 (checked, Research).** The completion graph of this stream has exactly
two terminal structural modes for the post-mark tail debt: *uniform
escape* (tail debt \(\ge D_*+\delta\) for a fixed \(\delta>0\)) and
*minimum return* (tail debt \(\to D_*\)). This is a structural normal
form; no consumption theorem for either mode is asserted.

**R8 (checked).** Every canonical exact spine has
\(\sum_tx_{t,i}<\infty\) for every \(i\). (Two divergent clocks contradict
Fact 5.2; one divergent clock contradicts Fact 5.1, since R3 makes all
players punishment-normal.) By Fact 5.3 every canonical exact spine ends in
an all-Continue phantom.

**R9 (checked).** There is a finite \(H=H(r)\) with

\[
\sum_{t<L}\sum_{i}x_{t,i}\;\le\;H
\]

for every canonical exact block, uniformly over lengths and annotations.
(Unbounded charge would extract a summable-defect chronology with one
persistent label and contradict R8's compilers.) The bound is existential;
no formula for \(H\) is known.

**R10 (checked).** Along any exact cap–Nash prefix chain whose semantic
point keeps total debt above \(D_*\): every debt coordinate scales by the
common continuation factor, marked gains and inherited suffix atoms scale
by survival factors, and total prefix absorption is summable, while the
support and proportions of the debt vector can remain unchanged. Exact
prefixing cannot supply a persistent charge source: it returns toward the
minimum or converges to an inert all-Continue port with positive debt.

**R11 (checked core; scope exact).** In minimum return, for a payer \(p\)
with \(d_p\) bounded away from zero, replacing \(p\)'s post-mark strategy
by a near-best reply gives an actual positive gain and drives \(d_p\to0\)
with the other players and the upstream atom attached. At the limit,
exactly one of: (a) the target stays on the minimum fibre and no
previously-zero debt coordinate becomes positive — then the positive-debt
support strictly decreases (possible at most three times); (b) another
coordinate enters the support; (c) the target leaves the minimum fibre at a
\(p\)-zero strictly off-minimum endpoint. The established theorems force
this trichotomy at each attempt; they do **not** force an indefinitely
iterable leakage cycle, and the off-minimum chamber of (c) still needs a
consumer **(open)**.

**R12 (statuses separated).** *Checked or reviewed:* closed exact-prefix
saturation; the minimum-face alternative (exact root saturation either
returns to the minimum fibre or produces a strict inert passport); debt
scaling; neutral exact roots; law retention inside the supplied hull. The
strict residual object has: one killed player (\(d_p=0\)); total debt
strictly above \(D_*\); a retained positive law atom or upstream causal
passport; exact cap-root saturation with an all-Continue neutral root at
the port, often unique; finite total exact absorption; no charged return;
no renewable support drop. *Open:* a history-compatible source adapter or
consumer relating the upstream paid atom to the downstream saturated
killed face; the two objects may be different chronological stages and are
not yet co-realized.

**R13 (recorded).** If the post-mark continuation carries nonsingleton
terminal mass bounded below, collision anti-diffusion produces a literal
later row of fixed mass, yielding a paid same-witness renewed row or a
definite off-minimum tail escape. Only singleton clocks and Never mass can
remain genuinely diffuse.

**R14 (no-go results; checked where marked).** Separations a counterexample
may exploit, several with exact regression witnesses:

- terminal-law mass is not current-root absorption;
- a paid horizontal endpoint move is not an exact chronological edge;
- fixed-law minimality says nothing about law-changing directions;
- closeness of prescribed payoffs, terminal laws, or weakly convergent
  stopping laws does not control unrestricted deviation caps (uniform
  closeness of all unilateral payoff functionals does);
- eliminating one player's debt does not prevent support entry elsewhere;
- a pure same-stage cycle is not a temporal cycle;
- compact limits can lose relative timing and behavioral realizability;
- an exact positive root at a cap need not satisfy the payoff fixed-point
  identity of a stationary equilibrium;
- all-Continue exactness does not imply uniqueness.

**R15 (checked).** Every debt-minimal carrier pair \(z=(u,c)\) of a
counterexample satisfies, with \(s_i=r_i(\{i\})\),

\[
\sum_i u_i \;\ge\; \sum_i s_i + (n-1)\,D_* .
\]

(Sum the singleton moat \(c_i-s_i\ge D_*\) — a consequence of carrier
minimality — over the \(n\) players and subtract \(D_*\).) The minimum of
a counterexample is a socially profitable configuration: its aggregate
payoff exceeds the aggregate solo payoff by \((n-1)D_*\). A weighted form
holds as well: one such condition for every strictly positive costate,
with the weighted debt sum in place of \(D_*\).

## 7. The current residual

Under R1–R14, all exact backward-consistent dynamics of a counterexample
are asymptotically inert: canonical spines are all-summable and end in
phantoms (R8), total exact-block charge is bounded (R9), exact prefixing is
Zeno (R10), and each paid descent attempt ends in support drop, support
entry, or off-minimum exit (R11). Persistent motion, if any, must be
inexact or purely semantic.

**The sharp open problem (two-port coupling).** A counterexample source
supplies two established objects:

- *upstream port:* the marked paid forced-pair rows of R6 — actual
  profiles, fixed roles, mass and gain floors, retained atom;
- *downstream port:* the neutral saturation point of R12 — a carrier point
  with one killed debt coordinate, total debt above \(D_*\), law retained,
  and an all-Continue neutral exact root.

Open in both directions: construct an extension-compatible chronological
kernel realizing both ports as stages of one source-faithful history, or
prove that no such kernel exists. Consuming either R7 mode, or resolving
this coupling, is the live frontier.

**Sufficient targets for \(P(4)\)** (each contradicts the counterexample
hypothesis; none established):

1. produce canonical near-return blocks with \(\Delta/H\to0\) at a common
   endpoint (Fact 5.5 with Facts 5.1–5.2);
2. produce from source data a compact shift-invariant spine family with no
   phantom (Fact 5.4 against R8);
3. consume uniform escape (R7 mode 1);
4. prove the two leakage closures — a charged consumer for R11(c) and a
   no-new-debtor theorem excluding R11(b) at the aligned limit — and
   consume the strict inert chamber of R12.

**Sufficient target for \(\neg P\):** one explicit table with one exact
rational certificate of a positive lower bound on \(\eta\) (R2); such a
table would sit inside an open set of counterexamples (Fact 3.2) while
realizing the entire dynamic structure above.

## 8. Witness for the table-level fragment

The following table \(W\) shows that the finitely checkable conditions
R3–R4 (with all players normal) do not imply counterexamplehood. Solo rows

\[
r(\{0\})=(1,4,0,0),\ \ r(\{1\})=(4,1,0,0),\ \
r(\{2\})=(0,0,1,4),\ \ r(\{3\})=(0,0,4,1),
\]

pairs \(r(\{0,1\})=(1,1,1,1)\), \(r(\{0,2\})=(1,1,1,0)\),
\(r(\{0,3\})=(1,0,1,1)\), \(r(\{1,2\})=(0,1,1,1)\),
\(r(\{1,3\})=(1,1,0,1)\), \(r(\{2,3\})=(1,1,1,1)\); triples
\((1,0,0,0),(0,1,0,0),(0,0,0,1),(0,0,1,0)\) for
\(\{0,1,2\},\{0,1,3\},\{0,2,3\},\{1,2,3\}\); quad \((-1,-1,-1,-1)\).
Comparison matrix

\[
M_W=\begin{pmatrix}0&3&-1&-1\\3&0&-1&-1\\-1&-1&0&3\\-1&-1&3&0
\end{pmatrix}.
\]

**(checked, all together):** \(M_W\) has full normal core, is Q (for
\(q=(-T,0,0,0)\) the full-support solution
\(z=(2T/15,7T/15,T/5,T/5)\) zeroes all rows), has no homogeneous solution,
and fails \(\bar Q\) on the mutual pair \(\{0,2\}\) — regime 5. All solos
equal \(1\), so all players are normal; colliders exist with margin 1. \(W\)
has no stationary exact terminal Nash profile, and it **has** an exact
uniform-equilibrium payoff, achieved by a period-two profile.

So: the table-level fragment is jointly satisfiable, even jointly with
equilibrium existence, and \(W\) has minimum debt zero — it witnesses
nothing about the dynamic conjunction R1, R5–R14.

## 9. Status summary

A hypothetical four-player counterexample is forced into the source-attached
dynamic residual of §7. The finite table-level constraints are jointly
satisfiable and far from sufficient. The full dynamic conjunction is
neither known realizable nor known contradictory; deciding it is exactly
\(P(4)\). Checked work confines the exact Bellman geometry of any
counterexample to canonical all-summable spines with uniformly bounded
finite hazard capacity; the sharp live issue is the source-compatible
coupling or consumption of the upstream paid mark and the downstream strict
neutral saturation face. If a counterexample exists, Fact 3.2 places it in
an open family of counterexample tables, not a measure-zero exception.
