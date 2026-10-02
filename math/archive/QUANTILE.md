The decisive issue is that **prescribed play and a deviator who keeps continuing assign different probabilities to reaching the next face**. Equal, even zero, child regrets do not remove that difference.

The splice I tested fails for this reason. **I have not established any of alternatives 1–4.** Here is the exact calculation and a regression example satisfying all the source-specific conditions, so that this failure is not attributed merely to poorly chosen approximate equilibria.

## Exact cross-face splicing law

Let \(P=(q^0,\ldots,q^{T-1})\) be a finite product prefix, and let \(P\star x\) denote its concatenation with a complete behavioral continuation \(x\). Define

$$
c=\prod_{t<T}\prod_j(1-q_j^t),
\qquad
\lambda_i=\prod_{t<T}\prod_{j\ne i}(1-q_j^t).
$$

Thus \(c\) is prescribed joint survival, whereas \(\lambda_i\) is survival when player \(i\) always continues through the prefix.

Let \(a_i\) be the prescribed expected reward earned before \(T\), \(h_i\) the expected reward earned before \(T\) when \(i\) always continues, and \(k_i\) the best payoff from a pure quitting date strictly before \(T\). These quantities depend only on \(P\) and \(r\). Then

$$
U_i(P\star x)=a_i+c\,U_i(x),
$$

and, **with unrestricted behavioral deviations**,

$$
B_i(P\star x)
=
\max\{k_i,\ h_i+\lambda_i B_i(x)\}.
\tag{1}
$$

Indeed, a pure deviation either quits inside the prefix or continues through it and uses an arbitrary replacement law afterward. Randomizing over complete stopping laws cannot exceed the supremum of these pure-time payoffs.

Consequently, putting

$$
\Delta u_i=U_i(y)-U_i(x),\qquad
\Delta b_i=B_i(y)-B_i(x),
$$

gives the exact identity

$$
\begin{aligned}
d_i(P\star y)-d_i(P\star x)
={}&
\max\{k_i,h_i+\lambda_i B_i(y)\}\\
&-\max\{k_i,h_i+\lambda_i B_i(x)\}
-c\,\Delta u_i.
\end{aligned}
\tag{2}
$$

In particular,

$$
d_i(P\star y)
\le
d_i(P\star x)
+\lambda_i(\Delta b_i)_+
-c\,\Delta u_i.
\tag{3}
$$

Suppose player \(i\) is an exact best responder in **both** face sources. Then \(B_i(x)=U_i(x)\) and \(B_i(y)=U_i(y)\). Nevertheless, when the continuation value increases by \(\Delta u_i>0\), the additional regret can be

$$
(\lambda_i-c)\Delta u_i.
\tag{4}
$$

The deviator benefits more from the improved continuation because it avoids its own prescribed quitting risk.

This is a cross-face error in payoff levels, not a child-equilibrium error.

## A regression with exact sources on every proper face

Consider three players and the following reward table:

$$
\begin{array}{c|ccc}
S&r_1(S)&r_2(S)&r_3(S)\\ \hline
\{1\}&1&0&0\\
\{2\}&0&1&0\\
\{3\}&2&0&1\\
\{1,2\}&1&1&0\\
\{1,3\}&2&0&1\\
\{2,3\}&0&1&1\\
\{1,2,3\}&1&1&1
\end{array}
$$

Infinite continuation pays zero.

For each nonempty proper player set \(J\), prescribe that everyone in \(J\) quits at date zero, with one exception: for \(J=\{1,3\}\), prescribe that player \(3\) quits at zero and player \(1\) chooses Never.

Every prescribed child profile is an exact equilibrium against unrestricted deviations: each participating player obtains its maximum reward available in that child game.

For

$$
J=\{1\},\{2\},\{3\},\{1,2\},\{1,3\},\{2,3\},
$$

choose outsiders respectively

$$
2,\ 1,\ 2,\ 3,\ 2,\ 1.
$$

Each selected outsider gains exactly \(1\) by quitting immediately in the quiet lift.

Thus, with the numerical choices

$$
\gamma=1,\qquad M=2,\qquad \rho=\tfrac14,
$$

all the **source-specific** conditions hold: the child errors can be any positive sequence decreasing to zero, the profiles can be constant in that sequence, and their date-zero reach is \(1\).

Now take two of these sources:

$$
x=\text{quiet lift of the }\{1,2\}\text{ source},\qquad
y=\text{quiet lift of the }\{1,3\}\text{ source}.
$$

Their ambient semantic vectors are

$$
U(x)=(1,1,0),\qquad B(x)=(1,1,1),
$$

$$
U(y)=(2,0,1),\qquad B(y)=(2,1,1).
$$

Player \(1\) is protected in both children:

$$
d_1(x)=d_1(y)=0.
$$

Let \(P\) be one date at which player \(1\) quits with probability \(1/2\) and the other players continue. Here

$$
c=\tfrac12,\qquad \lambda_1=1.
$$

Before the face switch,

$$
U_1(P\star x)=B_1(P\star x)=1.
$$

After the switch,

$$
U_1(P\star y)=\tfrac32,\qquad
B_1(P\star y)=2,
$$

so

$$
d_1(P\star y)=\tfrac12.
$$

The profitable replacement is simply Never: player \(3\) then quits at the next date and gives player \(1\) payoff \(2\).

Thus an exact-to-exact face switch creates regret \(1/2\) for a player belonging to both children, while the continuation is reached with probability \(1/2\ge\rho\). Equation (4) is attained exactly.

**This table is not a counterexample to uniform-equilibrium existence.** Everyone quitting at date zero is an exact parent equilibrium. In particular, the global positive-gap hypothesis is absent. The example refutes the proposed splice estimate, not your requested implication.

## What remains unproved

To turn (1)–(3) into your compiler, one must select or construct cross-face transitions whose accumulated terms

$$
\lambda_i(\Delta b_i)_+-c\,\Delta u_i
$$

are controlled by the child errors—or prove another mechanism that compensates for them. Separate convergence of the face sequences does not make their limiting payoff levels coincide, and a lower bound on source reach does not make these terms small.

The external constructions I checked do not supply that step: the general sunspot result allows public signals, while the APS framework explicitly distinguishes invariant-set membership from implementable equilibrium payoffs. Neither gives the independent-profile compiler required here. ([arXiv][1])

I have therefore neither derived a cardinal bound nor constructed the required \(L\), and I have no certified positive-gap table. The calculation above is a verified failure of one cross-face construction, not a resolution of the question.

[1]: https://arxiv.org/abs/1707.02598?utm_source=chatgpt.com "Quitting Games and Linear Complementarity Problems"

----


The point to preserve is not merely terminal outcomes: a compression must also preserve ties, empty dates at which a deviator can preempt, and quitting **after every prescribed finite date**.

There is an explicit construction that does this. It gives two results: a common finite-clock representation of all face sources and their independent recombinations, and a **complete finite certificate scheme for positive unrestricted exploitability gaps**.

This does not yet establish alternatives 1–4. In particular, the finite certificate scheme below is proved complete, but I have not produced a reward table satisfying one of its positive certificates.

## 1. Uniform finite compression, including unrestricted caps

Write \(n=|I|\) and set

$$
A_n=(4n-2)M.
$$

**Theorem.** For every behavioral product profile \(p\) and integer \(K\ge1\), there is an independent profile \(q\) such that:

* every stopping probability is an integer multiple of \(1/K\);
* every prescribed stopping time belongs to

  $$
  \{0,\ldots,2nK-1,\mathrm{Never}\};
  $$
* for every player \(i\),

  $$
  |U_i(p)-U_i(q)|\le \frac{2nM}{K},
  \qquad
  |B_i(p)-B_i(q)|\le \frac{2(n-1)M}{K}.
  $$

Consequently,

$$
\boxed{\;|e_r(p)-e_r(q)|\le \frac{A_n}{K}.\;}
\tag{1}
$$

The horizon bound is independent of the original stopping laws. No tightness assumption, finite expected stopping time, or restriction on deviations is needed.

### Why the law approximation controls arbitrary deviations

For a stopping law \(\mu\), let

$$
F_\mu(t)=\mu(\{0,\ldots,t\}),\qquad
d_{\mathrm{CDF}}(\mu,\nu)=\sup_{t\in\mathbb N}|F_\mu(t)-F_\nu(t)|.
$$

Changing one player’s law by at most \(\delta\) in this metric changes **any player’s expected payoff by at most \(4M\delta\)**, uniformly over everyone else’s laws.

To prove this, fix the other players’ pure stopping times. Suppose their first finite stopping time is \(t\), with quitting coalition \(S\). As a function of the changed player \(j\)’s stopping time, payoff coordinate \(i\) has only three values:

$$
A=r_i(\{j\})\quad(s<t),\qquad
B=r_i(S\cup\{j\})\quad(s=t),\qquad
C=r_i(S)\quad(s>t).
$$

The last case includes Never. Its expectation is

$$
C+(A-B)F_\mu(t-1)+(B-C)F_\mu(t).
$$

Thus its change is bounded by

$$
\bigl(|A-B|+|B-C|\bigr)\delta\le4M\delta.
$$

When all other players choose Never, the expectation is

$$
r_i(\{j\})\lim_t F_\mu(t),
$$

which satisfies the same bound. Integrating over the other laws proves the claim.

Telescoping over changed coordinates gives

$$
|U_i(p)-U_i(q)|
\le4M\sum_j d_{\mathrm{CDF}}(p_j,q_j).
\tag{2}
$$

For a deviation by \(i\), only the opponents’ laws change. The estimate holds **uniformly over the entire replacement law of \(i\)**, so taking suprema gives

$$
|B_i(p)-B_i(q)|
\le4M\sum_{j\ne i}d_{\mathrm{CDF}}(p_j,q_j).
\tag{3}
$$

This does not assume that a best response is attained.

### Quantiles give the required finite laws

For

$$
u_k=\frac{2k-1}{2K},\qquad k=1,\ldots,K,
$$

let \(Q_\mu(u_k)\) be the least finite \(t\) with \(F_\mu(t)\ge u_k\), or Never when no such finite date exists. Put

$$
\mu^{[K]}=\frac1K\sum_{k=1}^K\delta_{Q_\mu(u_k)}.
$$

Then

$$
d_{\mathrm{CDF}}(\mu,\mu^{[K]})\le\frac1{2K}.
$$

Equations (2) and (3) give the stated payoff and cap errors.

The remaining issue is that these \(K\) atoms may occur at arbitrarily large dates.

### Compressing dates without creating new deviations

Let

$$
D=\{t_1<\cdots<t_L\}
$$

be the union of all finite support dates in the quantile-approximated profile. Define

$$
\phi(t_1)=\min(t_1,1),
$$

and

$$
\phi(t_{a+1})-\phi(t_a)
=\min(t_{a+1}-t_a,2).
\tag{4}
$$

Leave Never unchanged.

This preserves whether a date exists before the first support date, preserves ties, and preserves whether an empty date exists between consecutive support dates. Every compressed date is at most \(2L-1\).

**Prescribed payoffs and unrestricted caps are preserved exactly by this time change.** Every pure deviation is at a support date, in an available gap, after the last support date, or Never. Equation (4) preserves all those possibilities in both directions, with identical outcomes against every opponent pure tuple.

Since \(L\le nK\), the compressed profile has the claimed horizon.

The preservation of gaps matters: arbitrarily inserting an empty date between two originally consecutive dates can introduce a profitable deviation that did not previously exist.

## 2. A genuinely simultaneous cross-face version

The construction can be applied to the supplied faces **on one common clock**, and uniformly over their crossed combinations.

Take any finite collection of ambient source profiles

$$
p^1,\ldots,p^m,
$$

including quiet lifts from different faces. Quantile-approximate every coordinate law, then compress the union of all finite support dates using one map \(\phi\). Denote the resulting profiles by

$$
\widehat p^{\,1},\ldots,\widehat p^{\,m}.
$$

Their finite support lies before \(2mnK\).

For arbitrary weights satisfying

$$
\theta_{ia}\ge0,\qquad \sum_a\theta_{ia}=1,
$$

form the independent profiles

$$
x_i(\theta)=\sum_a\theta_{ia}p_i^a,
\qquad
\widehat x_i(\theta)=\sum_a\theta_{ia}\widehat p_i^{\,a}.
$$

Then, **simultaneously for every choice of the weights**,

$$
\boxed{\;
|e_r(x(\theta))-e_r(\widehat x(\theta))|
\le \frac{A_n}{K}.
\;}
\tag{5}
$$

The reason is that taking mixtures preserves the CDF error bound, while the common clock preserves caps for every recombination exactly.

These are independent coordinate mixtures—not a shared random face label. Different players may select laws from different sources, and (5) explicitly covers the resulting crossed profiles.

For your supplied sources, the same construction preserves quiet Never coordinates and gives

$$
e_{G_{J_B}}(\widehat\tau_{B,n})
\le
\varepsilon_n+\frac{(4|J_B|-2)M}{K}.
$$

The ambient immediate outsider gain remains at least

$$
\gamma-\frac{A_n}{K}.
$$

Thus separately selected faces can be represented in one finite model without silently dropping their crossed profiles or late deviations.

**What this does not prove:** that some choice of \(\theta\) makes the parent exploitability small. The construction faithfully represents that selection problem; it does not solve it.

## 3. Complete finite certificates for positive global gaps

Here is a stronger consequence than finite approximation of an individual source.

Let \(\mathcal G_K\) be the finite set of all independent profiles whose laws have masses in

$$
\{0,1/K,\ldots,1\}
$$

and support in

$$
\{0,\ldots,2nK-1,\mathrm{Never}\}.
$$

Define

$$
a_K(r)=\min_{q\in\mathcal G_K}e_r(q),
\qquad
\eta(r)=\inf_p e_r(p).
$$

Then

$$
\boxed{\;
\max\!\left\{0,a_K(r)-\frac{A_n}{K}\right\}
\le \eta(r)\le a_K(r).
\;}
\tag{6}
$$

The upper bound holds because every grid profile is an actual behavioral profile. For the lower bound, compress an arbitrary \(p\) to \(q\in\mathcal G_K\). Equation (1) gives

$$
a_K(r)\le e_r(q)\le e_r(p)+\frac{A_n}{K},
$$

and we take the infimum over \(p\).

For a rational reward table and a rational bound \(M\), \(a_K(r)\) is an exactly computable rational number. For each grid profile, the unrestricted cap is the maximum over

$$
\{0,\ldots,2nK,\mathrm{Never}\}.
$$

The extra finite test date \(2nK\) represents quitting after all prescribed finite dates. All later finite dates give the same payoff.

Therefore:

$$
\boxed{\;
\eta(r)>0
\quad\Longleftrightarrow\quad
\exists K\ge1:\ a_K(r)>\frac{A_n}{K}.
\;}
\tag{7}
$$

A certificate consists of \(K\) and a verified rational lower bound \(\beta\) satisfying

$$
e_r(q)\ge\beta\quad\text{for every }q\in\mathcal G_K,
\qquad
\beta>\frac{A_n}{K}.
$$

It certifies the **unrestricted behavioral gap**

$$
\gamma_{\mathrm{cert}}=\beta-\frac{A_n}{K}>0.
$$

Completeness is immediate from (6): when \(\eta(r)>0\), choose \(K>A_n/\eta(r)\); then

$$
a_K(r)\ge\eta(r)>\frac{A_n}{K}.
$$

For four players, this becomes the explicit bound

$$
\boxed{\;
\max\{0,a_K(r)-14M/K\}\le\eta(r)\le a_K(r),
\qquad H=8K.
\;}
$$

This is not merely a certificate against a chosen extension fibre. Its lower bound applies to **every independent behavioral profile**, by the compression theorem.

The verifier can be exhaustive and very expensive: the grid has

$$
\binom{(2n+1)K}{K}^{n}
$$

profiles. The result establishes finite verifiability and a terminating positive-certificate search whenever the gap is positive—not computational efficiency or a terminating test for \(\eta(r)=0\).

## 4. Consequence for a hypothetical cardinal-minimal counterexample

For two reward tables on the same player set,

$$
\|r-s\|_\infty\le\delta
\quad\Longrightarrow\quad
|\eta(r)-\eta(s)|\le2\delta.
\tag{8}
$$

Indeed, every prescribed payoff and every cap changes by at most \(\delta\).

Consequently, a real cardinal-minimal counterexample with gap \(\gamma\) has a rational perturbation of the **same cardinality** with gap at least \(\gamma/2\). The rational perturbation is still cardinal-minimal because the assumption that every smaller game has a uniform-equilibrium payoff concerns all smaller reward tables. By (7), this rational counterexample has a finite certificate against unrestricted behavioral deviations.

So the following implication is established:

$$
\begin{gathered}
\text{a cardinal-minimal counterexample exists}\\
\Longrightarrow\\
\text{a rational cardinal-minimal counterexample exists}\\
\text{with a finite, exhaustive, unrestricted-gap certificate.}
\end{gathered}
$$

It does **not** exhibit that rational table, and therefore is not alternative 4.

## Where the requested reduction still fails

There is a precise reason not to finish this argument by invoking Nash’s theorem on the finite clock. The grid’s unrestricted caps include a late test date outside its prescribed finite menu. Adding that date to the prescribed menu introduces a new later test date. Moreover, the general compression map depends on the union of players’ supports: changing one input law can change everyone’s compressed clock. It is not, by itself, a unilateral-deviation-preserving reduction between strategic games.

What remains unproved is a cross-face selection or construction that makes the parent’s unrestricted regret small—or transfers a positive parent gap to an actual smaller game. The results above remove unbounded timing support from **verification**, but do not supply that strategic implication.

The proofs and executable checks are recorded here: [mathematical note](QUANTILE_CLOCK_COMPRESSION.md) and [note with exact-arithmetic regression scripts](QUANTILE_CLOCK_COMPRESSION.zip). The scripts passed 120 exact-rational profile tests, 100 independent cross-face mixture tests, and targeted tie/gap tests. These are regression checks; the mathematical proofs above have not been checked in Lean.
