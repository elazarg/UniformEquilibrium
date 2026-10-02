# Canonical maximal-reset regeneration and its Zeno normal form

Author: `CHATGPT_EXTERNAL`

Status: `PROOF_DRAFT`; ordinary-mathematics boundary analysis, not a terminal
consumer.

Source: supplied as `ephemeral/RESET_REGEN/RESET_REGEN.md` and moved here
without rewriting the mathematical body.

## Result: the recursion has a canonical Zeno normal form

The one-step theorem gives substantially more than strict debt descent, but that additional structure does **not** orient the recursion by a finite rank. Instead, it isolates one precise infinite residual: a summable-absorption Zeno ray whose paid/reset passport remains uniformly nondegenerate.

Let \(x_n\) be successive actual sources obtained by repeatedly taking the positive maximal-root branch. Write

$$
q_n:=\text{the maximal exact cap root at }x_n,
\qquad
a_n:=\operatorname{Abs}(q_n),
\qquad
c_n:=1-a_n.
$$

Let \(d_n^i\) be player \(i\)'s debt at \(x_n\), \(D_n=\sum_i d_n^i\), \(g_n\) the retained paid-row gain annotation, and \(\mu_n\) the retained reset-owner/opponent incidence.

The exact prefix identities used in the uploaded theorem give

$$
0<a_n<1,\qquad
D_{n+1}=c_nD_n,\qquad
d_{n+1}^i=c_nd_n^i,\qquad
g_{n+1}=c_ng_n.
$$

The descendant is an actual prefixed behavioral profile, keeps the same global minimum, retains the zero reset debt and positive incidence, and receives a newly constructed paid row whose witnesses are shifted by one date.

Define

$$
P_0=1,\qquad P_n=\prod_{k<n}c_k.
$$

Induction gives the exact formulas

$$
D_n=P_nD_0,\qquad
d_n^i=P_nd_0^i,\qquad
g_n=P_ng_0.
\tag{1}
$$

The law-prefix formula also gives

$$
\mu_{n+1}\ge c_n\mu_n,
\qquad\text{hence}\qquad
\mu_n\ge P_n\mu_0.
\tag{2}
$$

The inequality in (2), rather than equality, allows new prefix atoms to add incidence.

Since every \(x_n\) is an actual source and \(D_*\) is the global minimum,

$$
D_*\le D_n=P_nD_0.
$$

Consequently

$$
P_n\ge \rho:=\frac{D_*}{D_0}>0,
\tag{3}
$$

and therefore

$$
g_n\ge \rho g_0>0,
\qquad
\mu_n\ge \rho\mu_0>0.
\tag{4}
$$

Thus an infinite regeneration does **not** wash out the paid/reset passport. It preserves it with explicit uniform floors.

### Summability of every infinite branch

Because \(a_n=1-c_n\) and \(0<c_n\le1\),

$$
a_n\le-\log c_n.
$$

Hence, for every \(N\),

$$
\sum_{n<N}a_n
 \le -\log\prod_{n<N}c_n
 =\log\frac{D_0}{D_N}
 \le\log\frac{D_0}{D_*}.
\tag{5}
$$

It follows that

$$
\sum_{n=0}^{\infty}a_n<\infty,
\qquad
a_n\longrightarrow0.
\tag{6}
$$

Moreover,

$$
P_n\downarrow P_\infty\ge\rho,
\qquad
D_n\downarrow D_\infty=P_\infty D_0\ge D_*.
\tag{7}
$$

For \(m<n\), the absorption of the composed block of roots is exactly

$$
1-\prod_{k=m}^{n-1}c_k
 =1-\frac{D_n}{D_m}
 =\frac{D_m-D_n}{D_m}.
\tag{8}
$$

The additive charged-path mass of any future block is bounded by

$$
\sum_{k=m}^{n-1}a_k
 \le \sum_{k=m}^{\infty}a_k
 \longrightarrow 0
 \quad(m\to\infty).
\tag{9}
$$

Equations (1)–(9) are the **paid/reset Zeno normal form**.

## Consequences for the four requested exits

### 1. The currently available finite ranks cannot orient this recursion

Every positive-survival step preserves the debt support exactly:

$$
d_n^i>0 \iff d_0^i>0.
$$

It also preserves the normalized debt vector:

$$
\frac{d_n^i}{D_n}=\frac{d_0^i}{D_0}.
\tag{10}
$$

The player labels, reset coordinate and incidence labels are retained, while the paid-row witnesses are merely shifted. Therefore a rank based on any combination of

$$
\text{player labels},\quad
\operatorname{supp}(d_n),\quad
d_n/D_n,\quad
\text{row orientation},\quad
\text{reset labels}
$$

is constant along the recursion.

In particular, the existing finite support rank—based on strict enlargement of the zero-debt set—does not move here. Its intended strict decrease requires a genuine support change, while (10) proves that no such change occurs under these prefixes.

A finite rank could still exist if one proves a new discrete change in root components, terminal atoms, binding faces, or an owner-repair chronology. None of those changes follows from the renewal fields presently retained.

### 2. Consecutive regeneration edges cannot themselves supply a positive-charge near-return

The useful half of the near-return hypothesis does hold. Since the root absorptions are summable, the semantic payoff, cap and terminal-law sequences are Cauchy.

For example, if \(|r_i(S)|\le M\), then

$$
\|u_{n+1}-u_n\|_\infty\le 2Ma_n,
$$

and similarly for the caps. Thus the displacement from \(x_n\) to the limiting semantic port tends to zero.

But the other half fails in the strongest possible way: by (9), the entire future charged path starting at \(x_n\) has charge tending to zero. The checked varying-source consumer requires an eventual **fixed positive lower bound** on total absorption together with displacement tending to zero.

For the recursive ray we therefore obtain

$$
\text{cap displacement}\longrightarrow0,
\qquad
\text{available future charge}\longrightarrow0.
\tag{11}
$$

So the regeneration sequence supplies a vanishing-charge near-return, not a positive cumulative admissible-payoff near-return.

A path beginning at a fixed early source has positive charge, but the hypotheses contain no recurrence statement forcing a late payoff back near that early payoff. Compactness alone permits an injective convergent payoff arc.

### 3. The descendants are uniformly separated from terminal approximate Nash profiles

For every \(n\),

$$
\max_i d_n^i\ge\frac{D_n}{4}\ge\frac{D_*}{4}.
$$

Thus no regenerated descendant is a terminal \(\varepsilon\)-Nash profile for

$$
\varepsilon<\frac{D_*}{4}.
\tag{12}
$$

Obtaining terminal approximate Nash profiles would therefore require a construction outside the regenerated descendant chain, not a limiting selection from it.

### 4. There is no contradiction with the exploitability gap

Strict descent is compatible with

$$
D_n\downarrow D_\infty\ge D_*>0.
$$

Indeed, the chain retains positive debt, positive paid gain and positive incidence uniformly by (3)–(4). The root absorption simply becomes summably small.

The semantic/law limit need not be the semantic pair of a limiting behavioral profile: the successively added roots occur at the **front** of the chronology, and their mass can escape to later and later effective locations. Hence the behavioral terminal-gap statement cannot simply be applied to the carrier limit.

Actual four-player maximal-root Zeno rays of this kind are already realized by the zero-minimum regression tables. Those examples also carry useful local paid and zero-debt fragments, but their singleton rewards leave a zero-debt all-Never point, so they do not satisfy \(D_*>0\) and are not an acceptable counterexample here.

I do not have an explicit positive-minimum, positive-all-behavior-gap table supporting the full infinite machine.

## Why the reset dispatch does not replenish charge

The returned reset point has the target's prescribed payoff, which looks like the desired return. The obstacle is exact and coordinatewise.

A dynamic reset root is exact Nash against the returned **cap**. It is exact Nash against the returned prescribed payoff precisely when

$$
\operatorname{Surcharge}_i
 =
c\,d_i
\qquad\text{for every player }i.
\tag{13}
$$

Positive survival and positive total debt explicitly rule out the easy converter in which all opponent-survival-weighted debts vanish. Thus fixed-law payoff equality does not by itself place the reset root in the punishment-floor admissible relation.

Equation (13) is the exact cap-to-payoff seam which would have to be proved to turn the fresh reset dispatch into usable cumulative charge.

## Why the owner-repaired source does not provide a two-state rank

The original and repaired profiles have distinct paid observers, but their cap ports are selected independently. The current constructor explicitly provides no law identification, no transported reset dispatch and no chronological or Bellman connector between the two ports.

Therefore the finite label

$$
\{\text{original},\text{repaired}\}
$$

does not descend. It labels two independent Zeno rays. Treating it as an alternating two-phase chronology would add exactly the compatibility theorem that remains absent.

## Exact reduced obligation

The recursive branch is now reduced to the following source-matched statement.

> **Zeno-passport charge-renewal lemma.**
> From an actual paid/reset Zeno ray satisfying the uniform floors
>
> $$
> g_n\ge \rho g_0,\qquad \mu_n\ge\rho\mu_0,
> $$
>
> construct a constant \(\kappa>0\) such that, for every \(\eta>0\), one actual source on the ray admits a finite punishment-floor-admissible path with
>
> $$
> \operatorname{charge}\ge\kappa
> $$
>
> and prescribed-payoff endpoint error at most \(\eta\).

This lemma immediately gives option 2 through the checked varying-source consumer, and hence contradicts the terminal exploitability witness. Its substantive content must be one of:

$$
\begin{array}{ll}
\text{(a)} & \text{prove the surcharge identities (13) for a reset root;}\\
\text{(b)} & \text{construct an actual-profile representative of the returned
reset point with an exact payoff-root edge;}\\
\text{(c)} & \text{construct a commuting original/owner-repaired chronology
that replenishes a fixed charge;}\\
\text{(d)} & \text{extract a genuine finite binding/coalition rank from the
uniform paid and incidence floors.}
\end{array}
$$

The one-step regeneration and its renewal hypotheses already provide every other ingredient. In particular, they provide endpoint convergence and a quantitatively nonvanishing passport; what they do not provide is **renewed admissible charge**.

So the strict-debt recursion is not yet oriented into one of the four terminal outputs. Its strongest rigorous reduction is the Zeno normal form (1)–(11), which rules out debt support, normalized-debt, finite-label and consecutive-charge ranks and isolates the cap-to-payoff/chronological charge-renewal seam as the remaining theorem.

I read the exact uploaded regeneration files and checked the current repository source, while keeping source inspection, compilation and publication status distinct as required by the project runbook. No source edit or compilation claim is being made here. 
