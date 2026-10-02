# State topologies and approximation modes

The exact replacement state in `MARKOV_COMPLETE.md` can be represented by the
tuple of marginal stopping laws.  Different topologies on that same data
support different operations.  No single topology below is both compact and
uniformly stable for every calendar suffix.

## 1. Exact operations on actual stopping laws

Let \(\mu_i\in\Delta(\overline{\mathbb N})\) be player \(i\)'s stopping law.

### Unilateral replacement

Replacing player \(i\) by a law \(\nu_i\) overwrites one coordinate:

\[
(\mu_j)_{j\in I}
\longmapsto
(\mu_1,\ldots,\mu_{i-1},\nu_i,\mu_{i+1},\ldots).
\tag{1}
\]

### One product-root prefix

For a product root \(q=(q_i)\), let \(S(t)=t+1\) for finite \(t\) and
\(S(\infty)=\infty\). Then

\[
\operatorname{Pref}_q(\mu)_i
=
q_i\delta_0+(1-q_i)S_\#\mu_i.
\tag{2}
\]

### Positive-survival suffix

For \(h\ge0\), put

\[
s_i(h)=\mu_i(\{h,h+1,\ldots,\infty\}).
\]

When every \(s_i(h)>0\), the literal reached suffix is represented by

\[
\operatorname{Tail}_h(\mu_i)(t)
=
\frac{\mu_i(h+t)}{s_i(h)},
\qquad
\operatorname{Tail}_h(\mu_i)(\infty)
=
\frac{\mu_i(\infty)}{s_i(h)}.
\tag{3}
\]

Conditioning preserves independence because the joint survival event factors
coordinatewise. On a region where every relevant survival probability is at
least \(\eta>0\), the map has the standard total-variation stability bound of
order \(\eta^{-1}\).

If some \(s_i(h)=0\), the initial stopping law does not determine player
\(i\)'s prescribed actions after that unreachable history. A behavioral
strategy still has a literal off-path suffix, but recovering it requires the
full hazard policy or an equivalent suffix-indexed tower.  Marginal stopping
laws alone therefore close only positive-survival suffix selection.

### Finite block concatenation

Let a block of length \(H\) have roots \(q^0,\ldots,q^{H-1}\), followed by
tail law \(\mu\). With

\[
c_i(t)=\prod_{u<t}(1-q_i^u),
\]

the concatenated law is

\[
\Pr(T_i=t)=c_i(t)q_i^t\quad(0\le t<H),
\tag{4}
\]

\[
\Pr(T_i=H+u)=c_i(H)\mu_i(u),
\qquad
\Pr(T_i=\infty)=c_i(H)\mu_i(\infty).
\tag{5}
\]

These are exact actual-profile formulas.

## 2. Operational total-variation topology

The distance

\[
d_{n-1}(K,L)
=
\sup_{|A|\le n-1,\,t_A}
\|K(A,t_A)-L(A,t_A)\|_{\mathrm{TV}}
\tag{6}
\]

controls every labelled pure intervention.  Common unilateral replacements
are nonexpansive in this distance, and bounded payoffs and unrestricted
behavioral caps are Lipschitz.

Every actual stopping-law profile has a sourcewise rational finite-clock
approximation in this topology.  For each player:

1. retain a sufficiently large finite initial segment;
2. retain the Never atom separately;
3. move the remaining finite tail to one later finite date; and
4. rationally approximate the finitely many masses.

The marginal total-variation errors can be made to have sum below any
prescribed \(\varepsilon\). A product coupling then gives

\[
\sup_{|A|\le n-1,\,t_A}
\|K_\sigma(A,t_A)-K_{\sigma^\varepsilon}(A,t_A)\|_{\mathrm{TV}}
<\varepsilon.
\tag{7}
\]

The approximant is one actual rational finite-clock profile and the estimate
is uniform over all static pure interventions.

This does not produce a finite set of approximating states at accuracy
\(\varepsilon\). There are infinitely many rational finite-clock profiles and
arbitrarily late dates. The isolated-spike theorem in
`SUFFIX_INFORMATION_OBSTRUCTION.md` proves that no finite global net can
control all suffix probes at one fixed resolution.

## 3. Compact pointwise topology

To keep finite-time escape distinct from Never, use the compact split clock

\[
\widehat T
=
\mathbb N\sqcup\{\mathsf{Esc},\mathsf{Never}\},
\]

where finite dates converge to \(\mathsf{Esc}\) and Never is isolated. A
terminal boundary outcome records Never or a pair

\[
(t,S),
\qquad
t\in\mathbb N\cup\{\mathsf{Esc}\},
\quad \varnothing\ne S\subseteq I.
\]

Marginal split-clock limits alone lose relative phases. For example,

\[
(\delta_m,\delta_m)
\quad\text{and}\quad
(\delta_m,\delta_{m+1})
\]

have the same coordinatewise limit but different terminal limits: an
escaping tie versus an escaping singleton. A compact carrier must therefore
retain joint terminal-response boundary data as well as marginal provenance.

A natural carrier is the closure of the actual-state graph

\[
\sigma\longmapsto
\left(
(\mu_i)_{i\in I},
\bigl(K_\sigma(A,t_A)\bigr)_{|A|\le n-1,\,t_A}
\right)
\tag{8}
\]

inside the countable product of the corresponding compact probability
spaces. This closure is compact and metrizable.

For every fixed actual replacement law, the replacement formula extends to
this pointwise closure by dominated convergence. Fixed root prefixes and
fixed finite blocks also extend. Fixed-depth suffix conditioning is
continuous on regions with a fixed positive survival floor.

The following do not follow from this construction:

- joint continuity for a replacement law that itself moves toward infinity;
- a canonical suffix at zero survival;
- one modulus uniform over all suffix depths or block lengths;
- an executable realization of every boundary transition; or
- a finite global strategic approximation.

Moving intervention labels can be recorded by additional closed graphs or
hyperspace relations, but a coherence and realization theorem is still
needed before such a relation becomes a deterministic recursive state.

## 4. Comparison

\[
\begin{array}{c|c|c|c}
\text{state/topology}
&\text{replacement}
&\text{suffix control}
&\text{compact}\\ \hline
\text{operational TV/sup}
&\text{exact, nonexpansive}
&\text{uniform static queries}
&\text{no}\\
\text{pointwise response graph}
&\text{fixed-law continuous}
&\text{each fixed positive-reach suffix}
&\text{yes}\\
\text{all-depth sup control}
&\text{exact}
&\text{one common modulus}
&\text{no}.
\end{array}
\]

Compactness and exact congruence at every fixed depth are compatible. The
incompatibility begins when approximate control must use one modulus uniform
over the unbounded suffix family.

## 5. Viable architectures

The exact results leave several coherent designs open.

1. **Finite-program projective state.** Use the compact pointwise carrier and
   request a modulus only after fixing a finite collection of operations and
   depths.
2. **Positive-reach state.** Use marginal stopping laws together with an
   explicit survival floor, and dispatch separately when that floor vanishes.
3. **Two-tier state.** Keep a compact semantic core for recurrence and a
   source-attached, generally noncompact chronological passport for the
   finitely many operations currently executed.
4. **Inverse system of finite-depth states.** Work levelwise and prove a
   diagonal controller whose requested depth grows within the error budget.
5. **Absorption-clock quotient.** Remove arbitrary calendar suffixes from the
   operation language and prove a separate realization theorem for the
   chronological outputs actually needed.
6. **Noncompact exact state with compact projection.** Perform legal operations
   on exact clock data but establish recurrence or well-founded progress only
   after projection, together with a lift back to actual profiles.

None of these architectures currently supplies a global terminal, recurrent,
or ranked synthesis theorem.
