# Independent audit of the compactness obstruction

## Claim audited

This review checks Sections 3--5 of meta/SUFFICIENT_STATE.md and compares
them with Sections 8--10 of meta/MARKOV_COMPLETE.md. It audits the
depth-uniform modulus, sequential compactness, the \(2^N\)-packing claim,
finite approximation, and the compact split-clock construction.

## Verdict

The isolated-clock argument proves a clean impossibility theorem, but only
under a genuinely **depth-uniform** continuity hypothesis. The proof is
correct once that hypothesis and the compact subset are explicit.

The present text overstates two consequences:

1. condition 2 of the maintained question does not unambiguously supply one
   modulus common to every suffix depth or to programs of unbounded length;
2. condition 5 is refuted only if one finite approximation at fixed accuracy
   must control every suffix probe simultaneously.

MARKOV_COMPLETE.md does not contradict the obstruction. Its compact closure
uses weak, pointwise continuity for each fixed operation. Its operational
total-variation metric gives uniform intervention control but is noncompact.
Its rational approximation is finite-support **per source**, not a finite
global state net.

## 1. Strongest correct compactness theorem

Let \(r^\star\) be the four-player probe table in SUFFICIENT_STATE.md, fix
\(p\in(0,1)\), and let \(\sigma^m\) have the sole nonzero hazard
\(x_2^m=p\). Define

\[
h_n(\sigma)=U_2\bigl((S_n\sigma)[3\leftarrow Q_3^0]\bigr).
\]

The probe identity gives \(h_n(\sigma)=x_2^n\), so

\[
h_m(\sigma^m)=p,\qquad
h_m(\sigma^\ell)=0\quad(m\ne\ell).
\]

The exact theorem supported by the proof is:

> **Depth-uniform probe obstruction.** Let \(X\) be a metric space, let
> \(\Phi\) map the profiles \(\sigma^m\) into a sequentially compact subset
> \(K\subseteq X\), and suppose there is one function
> \(\omega:[0,\infty)\to[0,\infty)\), with
> \(\omega(s)\to0\) as \(s\downarrow0\), such that for every \(m,\ell,n\),
> \[
> |h_n(\sigma^m)-h_n(\sigma^\ell)|
> \le
> \omega\bigl(d_X(\Phi(\sigma^m),\Phi(\sigma^\ell))\bigr).
> \]
> Then no such \(K,\Phi,\omega\) exist.

Choose \(\delta>0\) so that \(d<\delta\) implies \(\omega(d)<p\). The probe at
depth \(m\) gives

\[
d_X(\Phi(\sigma^m),\Phi(\sigma^\ell))\ge\delta
\quad(m\ne\ell).
\]

This is an infinite uniformly separated sequence. A convergent subsequence
would be Cauchy, which is impossible.

Only a common equicontinuity modulus for the scalar probes \(h_n\) is needed.
Strategic completeness, laws, caps, and update maps are one way to produce
these probes, but they should not obscure the minimal statement.

The compactness hypothesis must cover the spike profiles. Compactness only of
a smaller synthesis-reachable subset is not contradicted unless that subset
is proved to contain them.

## 2. Program length is the substantive ambiguity

The maintained question asks for approximate transition congruence “with a
uniform modulus,” but does not explicitly state

\[
\exists\omega\ \forall n\ \forall\sigma,\rho:\quad
|h_n(\sigma)-h_n(\rho)|
\le\omega(d(\Phi\sigma,\Phi\rho)).
\]

There are two different readings.

1. Every \(S_n\) is one member of a primitive operation family, and the same
   modulus is uniform over its parameter \(n\). Then the obstruction applies.
2. The primitive operation is \(S_1\), or each fixed \(S_n\) may have its own
   modulus. Then the obstruction does not follow. Even if \(S_1\) and
   replacement have fixed moduli, the modulus for \(S_1^n\) is an \(n\)-fold
   composition and generally depends on \(n\).

Thus the sentence in Section 3 saying that composing elementary moduli “is
still independent of \(n\)” is valid only under reading 1, where the suffix
operation already has a modulus uniform in \(n\). It is false when \(S_n\) is
built from \(n\) one-step shifts.

The compact product space of hazard streams separates the readings: every
fixed \(S_n\) is continuous, but the family \(\{S_n:n\ge0\}\) is not
equicontinuous.

The maintained question should either state the depth-uniform quantifiers
explicitly or allow operation-/depth-dependent moduli. Under the latter
reading, SUFFICIENT_STATE.md rules out a natural stronger architecture, not
the whole question.

## 3. The \(2^N\)-packing claim

For the \(2^N\) profiles \(x_2^t=pa_t\) on \(0\le t<N\), two different words
differ at some \(n<N\). Their depth-\(n\) probe values differ by \(p\), so
their images are \(\delta\)-separated. This is correct.

A net of radius strictly below \(\delta/2\), say \(\delta/3\), therefore needs
at least \(2^N\) points for every \(N\). The smaller radius avoids an
irrelevant closed-ball equality convention.

There is also a direct finite-abstraction version. Suppose a finite set
\(A_\varepsilon\), an encoding \(a(\sigma)\), and decoded values
\(\widehat h_n\) satisfy

\[
|h_n(\sigma)-\widehat h_n(a(\sigma))|\le\varepsilon
\quad\text{for every }\sigma,n.
\]

For \(\varepsilon<p/2\), distinct binary words require distinct codes. Hence
\(|A_\varepsilon|\ge2^N\) for every \(N\), impossible for finite
\(A_\varepsilon\).

This does not rule out:

- a finite approximation of the first \(N\) suffixes whose size grows with
  \(N\);
- an approximation chosen for one prescribed finite program; or
- a countable hierarchy of sourcewise finite-clock approximants.

Section 4 therefore refutes condition 5 only if condition 5 requires one
finite model at each accuracy with error uniform over the entire unbounded
suffix tower. The current wording does not make that quantifier explicit.

## 4. Exact topology trilemma

The examples correctly show:

- the product topology is compact and every fixed \(S_n\) is continuous;
- \(\{S_n:n\ge0\}\) is not equicontinuous there; and
- a sup-type metric makes suffixes uniformly stable but leaves isolated
  spikes pairwise separated, so it is not totally bounded.

The exact incompatible triple is:

1. all probes \(h_n\) factor through the state;
2. the family \(\{h_n:n\ge0\}\) has one common equicontinuity modulus; and
3. the state image containing the isolated spikes is relatively sequentially
   compact in a metric topology.

Exact all-depth congruence alone is compatible with compactness. The conflict
starts at **depth-uniform approximate congruence**. This qualification should
accompany the boxed trilemma and the assertion that the requested state does
not exist.

## 5. Comparison with MARKOV_COMPLETE.md

### Exact actual-state formulas

For actual profiles, labelled marginal stopping laws determine the
pure-intervention response hierarchy. Coordinate replacement, fixed
product-root prefixing, fixed positive-mass suffix conditioning, and fixed
finite-block concatenation have the stated exact formulas. This is algebraic
closure, not a compact depth-uniform operational modulus.

For the posterior replacement identity, the precise domain condition is that
each unchanged coordinate and the replacement law survive to \(h\) with
positive probability. The overwritten original coordinate need not survive
if the identity is stated directly for the updated tuple.

### Compact graph closure

The split-clock space and countable pointwise response graph give a compact
metrizable closure. The escaping-clock examples correctly show why marginal
weak limits lose tie/phase information and why joint response coordinates
are needed.

For every **fixed actual** replacement law \(\nu_i\), pointwise convergence of
the pure-response kernels and dominated convergence justify the successor
formula. This does not give joint continuity for arbitrarily varying
replacements in the split-clock weak topology. A moving replacement
\(\nu_m=\delta_m\) may follow a moving response spike invisible at every
fixed finite intervention; its integral need not be determined by pointwise
convergence. Varying replacements are controlled in the noncompact
operational topology when they converge in total variation.

Suffix conditioning is continuous for fixed \(h\) on a region with a fixed
positive survival floor. Neither the floor nor the modulus is uniform over
all \(h\). Fixed prefix maps and fixed finite blocks are continuous; no common
modulus for unbounded block length is supplied.

The optional hyperspace graph records possible moving-label limits. A further
selection/coherence theorem is still needed before it gives a unique
continuous successor for a simultaneously varying state and replacement.

### Uniform pure-intervention approximation

Equation (23) is valid for each actual source. Approximate each marginal in
total variation and telescope the product measures. Intervention coordinates
are identical, so the estimate is uniform over all actual pure intervention
labels. Mixture then also controls arbitrary behavioral replacements at the
evaluative level.

But this is a **sourcewise finite-support approximation**, not a finite set of
states at fixed accuracy. There are infinitely many rational finite-support
laws and arbitrarily late dates. The packing theorem excludes a finite global
net with the same all-depth operational guarantee.

Nor does the total-variation approximation extend to compact escape points:
\(\delta_m\) converges weakly to \(\delta_{\mathsf{Esc}}\), while its
total-variation distance from \(\delta_{\mathsf{Esc}}\) remains maximal.
Compactification and operational approximation use different topologies.

### Net conclusion

\[
\begin{array}{c|c|c}
\text{representation} & \text{continuity} & \text{compactness}\\
\hline
\text{split-clock response graph} &
\text{pointwise/fixed-operation} & \text{yes}\\
\text{sup-TV response metric} &
\text{all pure interventions/common replacements} & \text{no}
\end{array}
\]

The documents do not conflict. MARKOV_COMPLETE.md gives an exact
actual-state closure and two useful but different approximation modes. It
does not provide one topology simultaneously having compactness,
arbitrary-depth equicontinuity, and a finite global strategic approximation.

## Recommended maintained statement

Keep the result as a file-per-issue impossibility theorem with this scope:

> No metric compactification containing all isolated-clock profiles can make
> the entire suffix-then-fixed-replacement probe family equicontinuous with
> one depth-independent modulus. Equivalently, no finite abstraction of fixed
> accuracy can approximate all those probes simultaneously. Exact congruence
> and continuity at each fixed depth remain possible in the compact pointwise
> topology.

This is the strongest theorem proved by Sections 3--5, is sharp against
MARKOV_COMPLETE.md, and leaves no ambiguity about program length or
finite-approximation quantifiers.
