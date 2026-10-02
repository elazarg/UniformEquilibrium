# Review of the asymptotic descendant passport and root barrier

Reviewer: `SOCIAL_WEIGHT_REVIEW`  
Date: 2026-08-31  
Verdict: **PASS**, with minor precision edits before any export.

## Claim reviewed

The note starts from the strict four-profile descendant port, closes all
common-prefix descendants along the asymptotic tail of the selected ranks,
and claims:

1. the signed-law atom and mover-gain passports become exactly proportional
   on the tail hull;
2. minimization of the resulting single density gives either loss of both
   passports or the global root-defect barrier
   \[
   \operatorname{RootDefect}(q;B)\ge D\operatorname{Abs}(q);
   \]
3. every exact root against the prescribed payoff at a barrier point is all
   Continue or a solo root supported by the unique debtor, with singleton
   tightness; and
4. the retained local fields do not themselves consume the strict port.

I checked the argument against the named arbitrary-root debt ledger, the
generic single-density minimizer and vanishing-density construction, root
Nash existence, and the common-prefix/deleted-survival identities. I also
recomputed the explicit four-player regression and tried to violate the
boundary and equality conclusions directly.

## 1. Tail-hull proportionality is correct

For a raw common-prefix descendant, both passports are multiplied by the
same joint Continue factor $c\in[0,1]$. If
$A_n\to A_\infty>0$ and $G_n\to G_\infty>0$, then with
$\rho=A_\infty/G_\infty$,

\[
A(W\star X_n)-\rho G(W\star X_n)
=c(W)(A_n-\rho G_n)\longrightarrow0.
\]

The proof correctly does not divide by $c(W)$. The tail closures are nested,
nonempty compact subsets of the finite product of the joint semantic/law
carrier. Prefixing by one fixed root is continuous and turns an arbitrary
finite word into another arbitrary finite word, so every tail closure and
their intersection are prefix invariant. Thus continuity gives
$A=\rho G$ throughout the tail hull.

This adapter is genuinely different from the already checked fixed-gap
identity in `NormalizedPassportSingleDensityToll.lean`: here proportionality
is only asymptotic on the base sequence and becomes exact after passage to
the tail hull.

## 2. The arbitrary-root toll follows from the stated closure

The identity

\[
D(q\star Y^R)=cD(Y^R)+R(q;B(Y^R))
\]

is exactly
`prefixMap_wholeDebt_eq_continueMass_mul_add_capDefect`; it needs no Nash
hypothesis. The signed atom and payoff-gain coordinates scale by the same
$c$. Therefore the prefixed point lies in the one-density slice exactly when

\[
\alpha R\le cs,
\qquad s=A-\alpha D.
\]

Slice minimality then gives $R\ge(1-c)D$ on the feasible side, while failure
of feasibility gives $R>cs/\alpha$. This proves the minimum bound in (4.6).
When $s>0$, the radius condition

\[
1-c\le s/A
\]

does imply feasibility under the contrary assumption $R<(1-c)D$, and hence
the linear toll. No zero-debt-face invariance is silently used; dropping that
face is exactly what makes arbitrary prefixing legitimate.

The exact-root consequence is also correct. For $R=0$, feasibility is
automatic, and minimality gives $D\le cD$. Since every $R$-component remains
in the original positive-global-minimum carrier, $D\ge D_*>0$, so $c=1$ and
the root is all Continue. Finite root-game Nash existence then shows that all
Continue is itself exact.

## 3. Density-to-zero and full absorption are sound

After an additional subsequence of the scalar sequence $u_n\in(0,1]$, either
$u_n\to0$ or $u_n$ is bounded below. In the second case, bounded debt and
$\alpha_n\to0$ force $A(Y_n)\to0$, and tail-hull proportionality forces
$G(Y_n)\to0$ as claimed.

In the first case, every fixed root with Continue mass $c>0$ eventually lies
inside the toll radius. Root defect is continuous jointly in the continuation
cap and the finite product root, so the inequality passes to the selected
limit point. A root with $c=0$ is approximated by the standard Continue
tremble. Each trembled root has $c>0$, absorption and total root defect are
continuous on the finite root simplex, and no quotient by $c$ occurs. Thus
the barrier genuinely holds for **all** product roots, including pure
full-absorption roots.

The note should make the extra scalar-subsequence extraction explicit before
calling the two utilization cases exhaustive. This is only a presentation
repair.

## 4. Passport-loss anatomy is correct but not regenerative

If the raw descendants lose the signed passport, their common-word survival
$c_k$ tends to zero because the unprefixed atom has a uniform positive lower
bound. After taking limits of the four own-survival factors:

- two or more vanishing own-survival coordinates make every deleted survival
  vanish, hence all four prescribed payoffs, laws, and cap vectors coalesce;
- exactly one vanishing coordinate $h$ leaves only the $h$-cap potentially
  distinguishable.

The cap estimate is valid for unrestricted behavioral replacements: after
replacing player $i$, two common-prefix tails can differ only if every
opponent of $i$ survives, giving the stated $2M H_i$ bound. Forcing $h$ to
Continue changes the joint survival to $H_h$ and restores both scalar
passports at that scale. The note correctly does **not** infer debt
minimality, zero-observer preservation, exact-root rigidity, or a recursive
source from this operation.

## 5. The prescribed-payoff equality classifier is correct

Let $q$ be exact against $U$ and write $B=U+d$. Increasing the continuation
from $U$ to $B$ raises player $i$'s Continue endpoint by exactly $s_i d_i$.
The three action-probability cases give, respectively, cap-root defect
$0$, $q_i s_i d_i$, and at most $s_i d_i$. Hence

\[
R(q;B)\le\sum_i m_i d_i\le D\sum_i m_i\le D\operatorname{Abs}(q).
\]

The barrier reverses the outside inequality, so all inequalities are equal.
If absorption is positive, equality between singleton absorption and total
absorption eliminates all collision mass. For an independent product root,
this leaves at most one positive Quit coordinate $h$. Equality in the
debt-weighted bound gives $d_h=D$ and $d_i=0$ for $i\ne h$. Mixing
indifference gives $U_h=r_h(\{h\})$ when $q_h<1$; when $q_h=1$, equality in
the cap-defect upper bound gives the same identity. Expanding the continuing
players' endpoint inequality gives (6.4) with the displayed sign.

This is a valid barrier specialization of the more general classification in
`CODEX_ROOT__PRESCRIBED_PAYOFF_ROOT_LIFTING.md`: the barrier rules out its
strict-debt-descent arm. The equality details are useful, but the general
solo-debtor gate itself should not be advertised as wholly new.

The pure-coalition consequences are also correct. At a nonsingleton pure
root, the total defect is exactly the sum of four toggle regrets. At a
singleton, the owner term is $B_h-r_h(\{h\})\ge0$ because all Continue is
exact against $B$. Thus every nonempty coalition has total toggle/cap defect
at least $D$. The constants $D/4$, $D/2$, and $D/6$ follow by pigeonhole. If
the owner term is large, an unrestricted response chosen within $D/4$ of the
supremum gives actual gain strictly greater than $D/4$. Otherwise the finite
nonempty-coalition graph has an outgoing strict toggle at every vertex, so a
finite directed cycle exists. This remains a horizontal obstruction, not a
chronology, exactly as the note states.

The two arms in (6.5) are not necessarily disjoint: all Continue can be exact
against $U$ while a solo root is also exact. Say explicitly that this is an
inclusive alternative if the word “alternative” is retained.

## 6. Exact regression

I recomputed the table in Section 2. At $R=\{0\}$,

\[
U=(-1,0,0,-1),\qquad B=(0,0,0,-1),\qquad d=(1,0,0,0).
\]

Continue beats Quit by at least one for each player at every opponent corner,
so the root defect is at least $\sum_iq_i\ge\operatorname{Abs}(q)$ and all
Continue is the unique cap root. The signed atom is positive, the mover gain
is one, all Never has zero debt, and the response curl is exactly $\kappa$.
Thus both $\kappa=0$ and $\kappa=1$ variants establish the stated local
fences.

There is one normalization typo: with the export's definition
$A=K(\mu_R-\mu_Q)r_j$ and $K=16$, the regression's signed passport equals
$16$, not $1$. Equation (2.6) correctly computes the unscaled signed atom.
Label it “the unscaled atom” or multiply by $K$. This does not affect any
conclusion.

The example matches the displayed **target-local** geometry only; it cannot
match the positive-minimum source identity
$G_\infty=d_p(z_*)>0$, because its global minimum is zero. The note already
says this, but retaining the qualifier “target-side local” is essential.

## 7. Novelty and provenance

The novelty ledger is mostly accurate:

- the arbitrary-root debt ledger, one-density toll, tremble passage, and
  vanishing-density dichotomy already exist generically;
- host/full-screening survival algebra already exists in the actual-Zeno
  modules;
- the solo-debtor classification is a barrier equality specialization of the
  reviewed prescribed-payoff-root classification;
- the genuinely new adapter is the asymptotic tail-hull ratio, together with
  its application to the signed-atom four-profile carrier and the explicit
  equality/pure-coalition consequences;
- retaining the common-response curl is only a proposed stronger source
  interface, not a theorem from the exported port.

No finite raw source, marked date, exact chronology, minimum-fibre
regeneration, or terminal consumer is recovered from the tail closure. The
note consistently respects that provenance boundary.

## Required edits

Before promotion beyond an internal note:

1. remove the duplicated `(4.1)` equation tag;
2. state the extra subsequence selection for $u_n$ explicitly;
3. correct the $K=16$ normalization in the regression or call (2.6) the
   unscaled signed atom; and
4. mark (6.5) as an inclusive alternative.

These are not mathematical failures.

## Export recommendation

**Do not export yet.** The mathematics is valid and the tail-hull adapter is
new, but the result is a nonterminal reduction assembled partly from generic
checked components and partly from new unformalized adapters. It should be
considered for export only if the project wants a formalization packet for
the asymptotic-ratio carrier plus equality classifier, or if one of the two
remaining boundary arms acquires a consumer. In its present form it sharpens
the strict port without closing it.
