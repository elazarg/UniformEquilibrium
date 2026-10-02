# Result

Three distinctions control the construction.

1. A chosen finite root word, unilateral replacement, or positive-reach suffix is an executable operation on actual behavioral profiles.
2. A compact limit of semantic pairs, terminal laws, or normalized decorations need not be the state of any source-faithful limiting behavioral profile.
3. A regenerated source may be used recursively only after actualization and only with a rank and backward compiler that survive regeneration.

At the inspected main head `28031be6…`, the uniform-escape adapter compiles each chosen root to a literal profile, and the minimum-return adapter retains actual origin ranks and root words. But their outputs remain, respectively, a same-tail return/undercharge dispatch and a regeneration-or-strict-inert obstruction; the source explicitly says that these are not uniform-equilibrium conclusions.

The current interfaces therefore do **not** instantiate a complete program satisfying the question. The strongest result I can prove from the supplied data is:

> **Executable-adapter obstruction theorem.**
> The bare exact-maximal-root edge, the infinite changed-cap left-prefix edge, and the bare normalized-decoration limit cannot be visible edges of a compact executable trace. Respectively:
>
> * the exact maximal-root relation is not closed, even along total-variation-convergent actual four-player sources with a fixed positive local debt floor;
> * under \(D_*>0\), a retained positive suffix atom forces a fixed positive stopping-law escape defect along every infinite exact left-prefix chain;
> * convergent normalized decorations with fixed positive marked mass and actual gain need not have any source-faithful behavioral limit.
>
> The legal replacements are a summable relaxed-root decoder, a stopping-law tightness passport, or a pointwise post-limit ranked transition.

The first and third assertions have explicit rational four-player examples below. The second applies directly under the positive-global-minimum hypothesis of the question.

---

## 1. A sufficient finite program schema

The following seven instruction types are enough. Finiteness is only of the instruction alphabet.

### `ExactRootPrefix`

Data:

$$
(\sigma,x),\qquad
x\in\prod_{i<4}\Delta(\{\mathsf C,\mathsf Q\}),
$$

with a proof that \(x\) satisfies the required root relation at the actual continuation \(\sigma\). Its compiler is the literal behavioral profile

$$
x\star\sigma.
$$

A root selected separately at one actual node is harmless. If the selection persists through a compact trace, it additionally needs either:

* a closed comparison-transport passport for exact maximizers; or
* the summable relaxed-max decoder in §5.

The current uniform-escape `returnedProfile` is a valid finite instance of this instruction: it literally prefixes the retained continuation profile and proves the exact semantic-prefix identity.

### `PositiveReachSuffix`

Data:

$$
(\sigma,d,\rho),\qquad
\Pr_\sigma(\text{live at }d)\ge \rho>0,
$$

together with the literal residual stopping laws after date \(d\). For a compact family with moving \(d_n\), those residual laws form a new persistent port and must themselves carry the tightness passport below.

For fixed \(d\), conditioning is quantitatively stable. If \(s_n,s\ge\rho\), then for each player's stopping laws,

$$
d_{\rm TV}\!\left(
 \lambda_n(\,\cdot+d\mid T\ge d),
 \lambda(\,\cdot+d\mid T\ge d)
\right)
\le \frac{2}{\rho}\,d_{\rm TV}(\lambda_n,\lambda).
$$

No suffix with reach tending to zero may be installed as the successor of its limiting source.

### `NormalizedActualizer`

Data:

* a compact decoration point \(z\);
* actual rows \(\sigma_n\);
* comparison rows \(\widehat\sigma_n\);
* origin ranks \(o_n\);
* finite root words \(w_n\);
* exact equalities

  $$
  \sigma_n=w_n\star \sigma^{\rm base}_{o_n};
  $$
* convergence of the complete decorations to \(z\);
* positive marked-mass and actual-gain floors;
* a stopping-law tightness passport for every persistent endpoint, comparison, and postmark-tail port.

The current minimum-return actualizer already supplies the actual rows, origin ranks, root words, mass floor, gain floor, and convergent decorations. It correctly does **not** identify the compact minimizer with an attained source.  Its source-neutral repackaging explicitly does not claim renewed source data, origin-rank cofinality, or a downstream consumer.

### `SummableMacro`

This is the triangular decoder. At accuracy \(k\), an occurrence at tree address \(w\) receives budget

$$
e_{k,w}:=
\frac{2^{-k-2|w|-8}}{1+M},
$$

where \(M\) bounds the rewards. Since there are at most \(2^d\) addresses of depth \(d\),

$$
\sum_w e_{k,w}
 \le \frac{2^{-k-6}}{1+M}.
$$

It records separate bounds for:

$$
e^{\rm reach},\quad
e^{\rm payoff},\quad
e^{\rm cap},\quad
e^{\rm law},\quad
e^{\rm ancestry}.
$$

A triangular array must satisfy:

* fixed-column convergence;
* a uniform summable tail bound;
* exact finite ancestry at every row;
* no conversion of escaped finite stopping mass into Never.

### `ClosedCase`

A finite tag type \(A\), a closed relation for each terminal and successor branch, and executable child/backward maps. Finite pigeonhole gives a common constant-tag subsequence.

An equality/strict comparison that is made only after one actual source has been reconstructed need not be part of the compact trace.

### `RankedRegeneration`

This instruction is applied only after an actual source exists. It contains:

$$
(\sigma',\operatorname{origin},\operatorname{back},
  r',r),\qquad r'<r\in\mathbb N.
$$

Here:

* \(\sigma'\) is an actual child source;
* `origin` relates its chronology to the actual endpoint rows;
* `back` compiles every terminal child certificate to the parent obligation;
* the rank belongs to the immutable outer program state, not to data that regeneration may replace.

Thus regeneration cannot recompute or reset the phase or support rank.

### `Terminal`

This consumes one of:

* terminal approximate Nash profiles with full behavioral-deviation bounds;
* a source-attached positive-charge near-return packet;
* a child whose strictly smaller rank is already consumed;
* an explicit table and a full behavioral terminal-gap certificate.

---

## 2. The stopping-law passport and actualization theorem

Let \(\lambda^n_{p,i}\) be player \(i\)'s stopping law at a persistent port \(p\), viewed as a probability measure on

$$
\overline{\mathbb N}=\mathbb N\cup\{\infty\}.
$$

A **tight port passport** consists of candidate coordinates \(\lambda_{p,i}\) such that

$$
\lambda^n_{p,i}(t)\longrightarrow\lambda_{p,i}(t)
 \quad(t\in\mathbb N),
\qquad
\lambda^n_{p,i}(\infty)\longrightarrow\lambda_{p,i}(\infty),
$$

and a common envelope

$$
E_p(T):=
\sup_{n,i}\sum_{t>T}\lambda^n_{p,i}(t)
\longrightarrow 0.
$$

The sum here contains only finite dates; Never is controlled separately.

### Tight-port realization lemma

Under this passport:

1. each \(\lambda_{p,i}\) is a probability measure;
2. \(\lambda^n_{p,i}\to\lambda_{p,i}\) in total variation;
3. the limit laws are realized by an actual behavioral profile;
4. prescribed payoffs, unrestricted behavioral caps, terminal laws, and every fixed deleted-player law converge.

#### Proof

For any \(T\),

$$
\sum_{t\le T}\lambda_{p,i}(t)+\lambda_{p,i}(\infty)
 =
\lim_n
\left[
 \sum_{t\le T}\lambda^n_{p,i}(t)
 +\lambda^n_{p,i}(\infty)
\right]
\ge 1-E_p(T).
$$

Letting \(T\to\infty\) proves that the limiting coordinates have total mass one. The same finite-head/tail split proves total-variation convergence.

An exact behavioral realization is obtained from the hazards

$$
h_i(t)=
\begin{cases}
\dfrac{\lambda_{p,i}(t)}
 {\lambda_{p,i}(\{t,t+1,\ldots,\infty\})},
 &\lambda_{p,i}(\{t,t+1,\ldots,\infty\})>0,\\[1.2ex]
0,&\text{otherwise}.
\end{cases}
$$

These hazards induce exactly \(\lambda_{p,i}\).

Let \(K(\lambda)\) denote the labelled first-stopping law generated by the independent marginal laws. Product coupling and contraction under the first-stopping map give

$$
d_{\rm TV}\bigl(K(\lambda^n),K(\lambda)\bigr)
\le
\sum_j d_{\rm TV}(\lambda^n_j,\lambda_j).
$$

More importantly, uniformly over every replacement law \(\nu_i\),

$$
d_{\rm TV}\!\left(
 K(\lambda^n[i\leftarrow\nu_i]),
 K(\lambda[i\leftarrow\nu_i])
\right)
\le
\sum_{j\ne i}
d_{\rm TV}(\lambda^n_j,\lambda_j).
$$

Consequently, for \(|r|\le M\),

$$
|U_i(\lambda^n)-U_i(\lambda)|
\le
2M\sum_jd_{\rm TV}(\lambda^n_j,\lambda_j),
$$

and

$$
|B_i(\lambda^n)-B_i(\lambda)|
\le
2M\sum_{j\ne i}d_{\rm TV}(\lambda^n_j,\lambda_j).
$$

The cap inequality follows by taking the supremum after a bound that is uniform in \(\nu_i\). It therefore covers Never, arbitrarily late stopping, and every behavioral mixture, not merely stationary or bounded-memory deviations. The recently integrated stopping-law interface records precisely that replacement is a marginal overwrite and that the pure-time menu determines the full behavioral cap.

This lemma is the required actual-data adapter for a normalized minimizer, a moving suffix, or any exogenous port. Without its tail envelope, coordinate convergence does not imply an actual probability law.

---

## 3. Exact maximal roots do not form a closed selection relation

This resolves the requested exact-root check negatively for the bare adapter class.

### Proposition 1 — source-attached nonclosedness

There is a rational four-player reward table and a total-variation-convergent curve of actual behavioral tails \(\tau_t\), all having total semantic debt at least \(1/2\), such that:

* for every \(t>0\), the unique exact root Nash equilibrium is all-Continue;
* at \(t=0\), all-Continue is exact but is not absorption-maximal;
* hence the graph of “exact Nash and maximal absorption among exact Nash roots” is not closed.

#### Construction

Let the players be \(0,1,2,3\), and define, for every nonempty coalition \(S\),

$$
r_0(S)=
\mathbf 1_{\{1\in S,\;0\notin S\}},
$$

and, for \(j=1,2,3\),

$$
r_j(S)=-\mathbf 1_{\{j\in S\}}.
$$

Let \(q=1/2\). In \(\tau_t\):

* player \(1\) quits at date \(0\) with probability \(t\), and otherwise Never;
* player \(3\) quits at date \(0\) with probability \(q\), and otherwise Never;
* players \(0\) and \(2\) Never.

The prescribed payoff is

$$
U(\tau_t)=(t,-t,0,-q).
$$

The unrestricted caps are

$$
B(\tau_t)=(t,0,0,0).
$$

Indeed:

* player \(0\) obtains \(t\) by waiting or Never; quitting before player \(1\) can only suppress the rewarding \(\{1\}\)-type event;
* players \(1,2,3\) obtain cap \(0\) by Never, while every event in which they themselves quit pays at most \(0\).

Thus

$$
D(\tau_t)=\sum_i(B_i-U_i)=t+q\ge\frac12.
$$

Moreover \(\tau_t\to\tau_0\) in total variation as \(t\downarrow0\).

Now consider the one-stage root game against the continuation cap

$$
b(t)=(t,0,0,0).
$$

Players \(1,2,3\) strictly prefer Continue: Continue always gives \(0\), while Quit gives \(-1\). With those players continuing, player \(0\) compares

$$
\mathsf{Continue}:t,
\qquad
\mathsf{Quit}:0.
$$

Hence:

$$
t>0
\quad\Longrightarrow\quad
N(b(t))=\{\mathsf{AllContinue}\},
$$

whereas at \(t=0\), player \(0\) is indifferent and may use any mixture. Absorption is then maximized uniquely by player \(0\) quitting surely.

For \(t_n\downarrow0\),

$$
(\tau_{t_n},\mathsf{AllContinue})
$$

belongs to the exact-maximal-root graph for every \(n\), but its limit

$$
(\tau_0,\mathsf{AllContinue})
$$

does not. Therefore that graph is not closed, and no continuous exact-maximal selector exists on this actual-source curve.

This example has a fixed positive **local** debt floor, but its table has global infimum zero. It is not a counterexample to uniform-equilibrium existence. It proves that closedness cannot follow merely from actual source data, tight stopping-law convergence, positive tail debt, compactness of the root simplex, and closedness of the exact-Nash graph. Any positive-\(D_*\)-specific closedness theorem would need to use a genuinely stronger Fin4 passport.

The repository's fixed-cap theorem correctly proves existence of a maximal root at each individual cap, but its cap-indexed `Classical.choose` selector is only extensional under equality of caps; no continuity theorem is supplied.

---

## 4. Positive \(D_*\) forces an escape defect on every infinite left-prefix chain

This is the direct obstruction inside the hypothesis of the question.

### Proposition 2 — retained-atom omega-prefix escape

Let \(\tau\) be an actual tail with total debt \(D_0>0\). Let

$$
\sigma_0=\tau,
\qquad
\sigma_{n+1}=x_n\star\sigma_n,
$$

where \(x_n\) is an exact cap-Nash root against the semantic cap of \(\sigma_n\). Write

$$
c_n=\Pr_{x_n}(\text{all Continue}),
\qquad
C_n=\prod_{k<n}c_k.
$$

Assume:

$$
D(\sigma_n)\ge D_*>0
\quad\text{for all }n,
$$

and that \(\tau\) has a coalition \(S\) terminating at a finite stage \(s\) with probability

$$
m>0.
$$

Then for every \(i\in S\):

1. the marginal stopping laws of \(\sigma_n\) have no common finite-tail tightness envelope;
2. every fixed finite coordinate converges to zero;
3. the Never coordinates converge, but the resulting finite-plus-Never coordinates have total mass at most

   $$
   1-\frac{D_*}{D_0}m;
   $$
4. consequently, no source-faithful actual behavioral limit exists.

#### Proof

Exact cap-Nash prefixing gives the exact debt recursion

$$
D(\sigma_{n+1})=c_nD(\sigma_n).
$$

Therefore

$$
D(\sigma_n)=C_nD_0
$$

and

$$
C_n\ge q:=\frac{D_*}{D_0}>0.
$$

The retained terminal atom is shifted by one date at every prefix and multiplied by the joint Continue mass. Thus \(\sigma_n\) has the same coalition \(S\) terminating at date \(n+s\) with mass

$$
C_nm\ge qm.
$$

For every \(T\), choose \(n\) with \(n+s>T\). Then player \(i\)'s finite stopping mass after \(T\) is at least \(qm\). Hence no envelope \(E(T)\to0\) is possible.

Because \(C_n\) is decreasing and bounded below by \(q\), it converges to a positive limit. Therefore

$$
c_n=\frac{C_{n+1}}{C_n}\longrightarrow1.
$$

Writing \(a_n=1-c_n\), we have \(a_n\to0\). For fixed \(t\) and \(n>t\), the root appearing at absolute date \(t\) in \(\sigma_n\) is \(x_{n-1-t}\). Hence

$$
\Pr_{\sigma_n}(T_i=t)
\le a_{n-1-t}\longrightarrow0.
$$

Thus every fixed finite stopping coordinate converges to zero.

Let \(p_{i,k}\) be player \(i\)'s Continue probability in \(x_k\), and

$$
P_{i,n}=\prod_{k<n}p_{i,k}.
$$

Since an individual Continue probability dominates joint Continue,

$$
P_{i,n}\ge C_n\ge q.
$$

The products \(P_{i,n}\) converge to some \(p_i\ge q\), and

$$
\Pr_{\sigma_n}(T_i=\infty)
 =
P_{i,n}\Pr_\tau(T_i=\infty)
 \longrightarrow
p_i\Pr_\tau(T_i=\infty).
$$

Because the displayed coalition atom forces player \(i\) to stop at \(s\) with probability at least \(m\),

$$
\Pr_\tau(T_i=\infty)\le1-m.
$$

Therefore the total mass of the coordinatewise limiting finite and Never coordinates is at most

$$
p_i(1-m)
\le 1-qm.
$$

At least \(qm\) mass has escaped to later and later finite dates.

Promoting that mass to Never would violate convergence of the Never coordinate and would replace the retained terminal coalition atom by a nonabsorption event. Retaining it at a finite date is impossible because every fixed finite coordinate converges to zero. This proves the claim.

### Application to uniform escape

The changed-cap maximal-prefix construction in the repository has exactly the hypotheses used above:

* exact debt multiplication by the root Continue mass;
* exact shifting and scaling of a suffix atom;
* summability of root absorption;
* a global positive semantic minimum.

The existing compactification consequently returns only a terminal semantic/law carrier cluster. Its own statement explicitly says that maximality is not passed to the limit.  The finite punishment-prefix charge is also bounded by the available semantic excess, so the chain cannot invoke an unbounded-charge compiler.

Thus an infinite maximal-prefix ray cannot be inserted into the requested compact execution as an actual-source transition. This remains true even if a continuous exact-root selector were somehow supplied.

Its legal uses are only:

* stop at a finite prefix and consume it there;
* change the chronology with an explicit decoder that pays at least the escaped law mass;
* or reconstruct a different actual source from independently tight residual ports.

---

## 5. The valid replacement for maximal exact-root compactification

The nonclosedness example does not prevent a summable approximation decoder.

Let \(X\) be the compact root simplex, \(a(x)\) its absorption mass, and let

$$
g(b,x)\ge0
$$

be the maximum one-stage root-Nash defect at continuation cap \(b\). The map \(g\) is continuous and, conservatively,

$$
|g(b,x)-g(b',x)|
\le 2\|b-b'\|_\infty.
$$

Suppose \(b_n\to b\), and put

$$
\delta_n=\|b_n-b\|_\infty.
$$

Choose \(x_n\) to maximize \(a\) on the compact nonempty set

$$
N_n=
\{x:g(b_n,x)\le2\delta_n\}.
$$

Then every cluster point \(x\) of \(x_n\) is an absorption-maximal **exact** root at \(b\).

Indeed, \(g(b_n,x_n)\le2\delta_n\to0\), so continuity gives \(g(b,x)=0\). If \(y\) is any exact root at \(b\), then

$$
g(b_n,y)\le2\delta_n,
$$

so \(y\in N_n\), and hence

$$
a(y)\le a(x_n).
$$

Passing to the limit gives \(a(y)\le a(x)\).

After taking a subsequence with

$$
\delta_n\le e_{n,w},
$$

the root defects are summable. This is a valid type-2 comparison-transport decoder. It must additionally record the resulting one-step payoff, cap, debt, and law error bounds; the exact debt-scaling identity used by the current uniform-escape dispatch cannot simply be reused for the approximate roots.

The other legal alternative is simpler: first reconstruct one actual limiting tail using the tight-port theorem, then choose an exact maximal root at that one source and apply it pointwise outside the compact trace.

---

## 6. Moving normalized decorations do not actualize without tightness

The minimum-return actualizer is honest because it retains actual approximating rows. But those rows do not automatically have an actual source-faithful limit.

### Proposition 3 — constant decorations with complete stopping-mass escape

There is a rational four-player table and a fixed-label decorated family such that:

* the whole semantic/law decorations are constant;
* the postmark semantic/law decorations are constant;
* marked mass is exactly \(1\);
* actual payoff gain is exactly \(1\);
* the marked-owner defect is exactly \(0\);
* nevertheless the endpoint stopping laws have no tight subsequence.

#### Construction

Define

$$
r_1(S)=
\begin{cases}
1,&S=\{0\},\\
0,&\text{otherwise},
\end{cases}
$$

and let every other payoff coordinate be zero.

For rank \(n\), let:

* \(\sigma_n\): player \(0\) quits surely at date \(n\), all others Never;
* \(\widehat\sigma_n\): player \(2\) quits surely at date \(n\), all others Never;
* mark \(n\);
* marked terminal \(\{0\}\);
* marked owner \(0\);
* gain mover \(1\).

For every \(n\),

$$
U(\sigma_n)=B(\sigma_n)=(0,1,0,0),
$$

and the terminal law is the point mass at coalition \(\{0\}\). The postmark tail is all-Never, with zero semantic pair and Never outcome law. Moreover,

$$
\Pr_{\sigma_n}(\{0\}\text{ quits at stage }n)=1,
$$

and

$$
U_1(\sigma_n)-U_1(\widehat\sigma_n)=1.
$$

Player \(0\)'s marked-root defect is zero because that player's payoff is identically zero. Hence the complete base decoration is independent of \(n\).

But player \(0\)'s stopping law is

$$
\lambda^n_0=\delta_n.
$$

For every fixed finite \(t\),

$$
\lambda^n_0(t)\to0,
$$

and

$$
\lambda^n_0(\infty)=0\to0.
$$

The coordinatewise limit has total mass zero. Also, for every \(T\),

$$
\sup_n\sum_{t>T}\lambda^n_0(t)=1.
$$

Thus there is no tight subsequence and no source-faithful actual limit. The compact decoration point is behaviorally attainable by some unrelated profile, for example by quitting at date \(0\), but choosing that realization destroys the recorded ancestry. Promoting the escaped mass to Never changes the stored terminal law from \(\{0\}\) to Never.

This proves that convergence in the current normalized decoration carrier, even with fixed positive mass and gain, is insufficient for the requested coherent construction. The existing actualizer therefore needs a `TightPort` field on its endpoint, comparison, and postmark-tail rows before its limit can become a trace source.

---

## 7. Suffix and regeneration checks

### Vanishing reach

The graph of conditional suffixing is not closed at zero reach. For example, let an initial root absorb with probability \(1-\varepsilon_n\), and on its all-Continue event of probability \(\varepsilon_n\to0\) attach an arbitrary tail \(\eta_n\). The whole profiles converge to sure immediate absorption independently of \(\eta_n\), while their conditional suffixes are exactly \(\eta_n\).

Therefore:

* fixed-depth suffixing is trace-safe on a displayed reach floor \(\rho>0\);
* moving-depth suffixes require their translated residual laws to carry a separate tight-port passport;
* a zero-reach branch must be terminalized or decoded with an explicit escape budget.

Literal equality of postmark spines, which the Fin4 source-preserving and normalized-return files do provide, establishes ancestry but not stopping-law compactness.

### Source regeneration

The current three-role regeneration does produce an actual child source with:

* the same underlying hard residual;
* the exact endpoint semantic/law point;
* the exact retained routed atom.

But its module explicitly states that there is no oriented rank decrease and that the new chronology is not asserted to contain the incoming endpoint edge.

Consequently it is valid as a pointwise source constructor, but not as a recursive compact-trace edge. A usable replacement must add:

$$
\begin{aligned}
&\text{childActual},\\
&\text{childOrigin in the selected actualizer rows},\\
&\text{backward compiler},\\
&\operatorname{rank}(\text{child})
  <\operatorname{rank}(\text{parent}).
\end{aligned}
$$

The rank must be passed into regeneration from the immutable outer program state. Equality of residuals cannot itself orient the recursion.

The later actual-Zeno host-compression and finite-clock-clearing modules retain much more finite provenance, but their own interfaces explicitly stop before a renewable compression or terminal consumer.

---

## 8. Exact audit of the two Fin4 components

| Transition                                            | What is executable now                                                                  | Missing requirement                                                                                      |
| ----------------------------------------------------- | --------------------------------------------------------------------------------------- | -------------------------------------------------------------------------------------------------------- |
| Uniform-escape one-root prefix                        | Literal continuation and returned behavioral profile; exact semantic and law identities | Harmless only as a finite operation                                                                      |
| Maximal exact-root selection along a compact sequence | Pointwise maximizer exists at every cap                                                 | Exact-maximal graph is not closed; Proposition 1                                                         |
| Changed-cap maximal-prefix recursion                  | Every finite prefix is actual; debt and atom scaling are exact                          | Infinite source limit has escape defect at least \((D_*/D_0)m\); Proposition 2                           |
| Minimum-return minimizer                              | Compact point and actual raw descendants with origin ranks/root words                   | Persistent ports lack stopping-law tightness; Proposition 3 shows decoration convergence is insufficient |
| Postmark suffix                                       | Literal postmark spine retained; equality arm has positive stage mass                   | Moving residual laws still require a tight-port passport                                                 |
| Three-role regeneration                               | Actual child at exact endpoint law                                                      | No selected backward chronology and no rank decrease                                                     |
| Strict inert/Zeno transitions                         | Several literal finite clearing and host adapters                                       | No terminal or renewable-rank consumer                                                                   |

Therefore the supplied source-preserving residual cannot currently be compiled into a program yielding one of the four requested terminal outcomes. Any such claim would necessarily perform at least one prohibited operation:

* pass maximality through a nonclosed exact-root graph;
* treat an omega-left-prefix law cluster as an actual source;
* identify a normalized carrier point with an attained source;
* condition through vanishing reach;
* or recurse through regeneration without a nonresettable rank.

The minimal remaining passports are now exact:

1. **Uniform escape:** either a positive-minimum-specific competitor-transport theorem for exact roots, or the summable relaxed-root decoder together with an approximate same-tail dispatch and a finite consumer.
2. **Minimum return:** tight stopping-law passports for actualizer endpoint, comparison, and postmark-tail ports, or an explicit bounded-mark/escape-decoder dichotomy.
3. **Regeneration:** an actual ancestry map, backward compiler, and immutable natural rank decrease.

These are adapter obligations, not another recurrent-component classification.

The repository was inspected at exact main head `28031be6…`; no Lean source was changed or compiled locally, and the corresponding main CI run was still in progress when checked. This keeps the mathematical result here distinct from a published, compiled, or axiom-audited Lean theorem, as required by the attached runbook.  
