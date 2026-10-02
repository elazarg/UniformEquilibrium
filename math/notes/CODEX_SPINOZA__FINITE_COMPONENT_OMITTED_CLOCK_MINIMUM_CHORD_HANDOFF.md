# The omitted clock of a finite response component enters support descent or paid retraction

Author: CODEX_SPINOZA

## Status

**Exact ordinary mathematics; source-attached reduction, not Lean-checked.**
Nashifying a bounded finite pure-clock response component does not preserve
its two sure clocks, but its first omitted deadline has more structure than an
arbitrary escaping response.  Since Never is already an action of the finite
timing game, every positive omitted-deadline gain is paid entirely on the
all-opponents-Never cylinder.  The exact cap child consequently has a
uniformly positive singleton atom.

Relative to any retained sequence approaching the positive global minimum,
the omitted exact-cap edges have an exhaustive output:

1. an endpoint stays uniformly off minimum, and the reviewed signed
   source-retraction theorem produces its existing source-supported paid-port
   output; or
2. both endpoints approach the minimum, and the executable one-player
   response chord produces a minimum child with strictly smaller positive-debt
   support and an explicit positive singleton atom.  Same-law causalization
   then enters the checked renewable minimum-source support trace through a
   one-use origin rank.

Thus finite-alphabet mixed Nashification creates no new third residual.  The
uniformly off-minimum paid-port waist remains unconsumed.

## 1. Input and finite timing Nash law

Let \(I=\operatorname{Fin}4\), assume

\[
 |r_i(S)|\le M
\qquad(M>0),
\tag{1.1}
\]

and let

\[
 D_*=\min_{\mathcal C^{\rm law}}D>0.
\tag{1.2}
\]

Fix a hard-residual terminal exploitability witness

\[
 \max_i d_i(P)\ge\Gamma>0
\qquad\text{for every actual behavioral profile }P.
\tag{1.3}
\]

Let \(S_n\) be a retained actual source family whose joint
terminal-semantic/law points converge to a global minimum point \(z_*\).

For every \(n\), choose a finite horizon \(H_n\).  In the timing game with
pure actions

\[
 A_{H_n}=\{0,1,\ldots,H_n,\mathrm{Never}\},
\tag{1.4}
\]

choose any mixed Nash equilibrium \(\mu^n\), realized as an actual product
stopping-law profile.  In the intended application, \(H_n\) contains every
deadline of the bounded finite response component.  No compatibility of the
equilibria across \(n\) is assumed.

## 2. The first omitted time is the complete cap

Against opponents supported on (1.4), every pure time strictly after
\(H_n\) has the same payoff as \(H_n+1\).  Every earlier pure time and Never
belongs to the finite game.  Pure-time extremality and finite-game Nash
optimality therefore give, for every player \(i\),

\[
 d_i(\mu^n)=
 \Bigl[
 U_i(\mu^n[i\leftarrow H_n+1])-U_i(\mu^n)
 \Bigr]_+.
\tag{2.1}
\]

By (1.3), select \(i_n\) for which the right side is at least \(\Gamma\).
After subselection fix one label \(i\).  Put

\[
 X_n=\mu^n,\qquad
 Y_n=\mu^n[i\leftarrow H_n+1].
\tag{2.2}
\]

Then \(H_n+1\) attains the complete unrestricted cap at \(X_n\), and

\[
 U_i(Y_n)-U_i(X_n)=d_i(X_n)\ge\Gamma,
\qquad d_i(Y_n)=0.
\tag{2.3}
\]

These are literal actual profiles and an exact whole-strategy response edge,
not a finite-menu approximation.

## 3. The omitted gain forces a uniform singleton atom

Write

\[
 \beta_n=\prod_{j\ne i}\mu^n_j(\{\mathrm{Never}\}),
\qquad s_i=r_i(\{i\}).
\tag{3.1}
\]

The pure actions \(H_n+1\) and Never have identical outcomes unless all three
opponents choose Never.  On that event the former produces \(\{i\}\) and the
latter produces the all-Never payoff zero.  Hence

\[
 U_i(\mu^n[i\leftarrow H_n+1])
 -U_i(\mu^n[i\leftarrow\mathrm{Never}])
 =\beta_n s_i.
\tag{3.2}
\]

Never is an action of the finite timing game, so Nash optimality gives

\[
 U_i(\mu^n[i\leftarrow\mathrm{Never}])\le U_i(\mu^n).
\tag{3.3}
\]

Combining (2.3)--(3.3),

\[
 \beta_n s_i\ge\Gamma.
\tag{3.4}
\]

In particular \(s_i>0\), \(s_i\le M\), and

\[
 \boxed{\beta_n\ge\Gamma/M.}
\tag{3.5}
\]

The cap child \(Y_n\) therefore terminates at the literal singleton
\(\{i\}\) at date \(H_n+1\) with unconditional mass at least
\(\Gamma/M\).  This atom is present at every index, not only in a compact
law limit.

## 4. Off-minimum endpoint or minimum response chord

Set

\[
 E_n=\max\{D(X_n)-D_*,\,D(Y_n)-D_*\}\ge0.
\tag{4.1}
\]

After subselection there are two cases.

### Alternative A: source-supported paid retraction

If \(\limsup_nE_n>0\), choose one endpoint family \(Z_n\in\{X_n,Y_n\}\)
and \(\delta>0\) such that

\[
 D(Z_n)\ge D_*+\delta
\tag{4.2}
\]

cofinally.  Apply the four-coordinate signed retraction from \(Z_n\) toward
the retained minimum source \(S_n\).  The generic retraction theorem in the
reviewed Fin4 response-cycle packet depends only on the two actual endpoint
families and (4.2), not on membership in a cycle.  It produces, after a
subsequence, either a literal source-oriented paid unilateral replacement or
a source-supported paid first-disagreement row with fixed quantitative gain
and reach floors.

This is exactly the existing off-minimum paid-port output.  No terminal
consumer is claimed for it here.

### Alternative B: strict support descent on the minimum fibre

Assume \(E_n\to0\), so

\[
 D(X_n)\to D_*,
\qquad D(Y_n)\to D_*.
\tag{4.3}
\]

Fix \(0<\theta<1\) and mix only player \(i\)'s complete stopping law:

\[
 H_{n,\theta}=(1-\theta)X_n+_i\theta Y_n.
\tag{4.4}
\]

Then \(Y_n=H_{n,\theta}[i\leftarrow H_n+1]\) literally and

\[
 U_i(Y_n)-U_i(H_{n,\theta})
 =(1-\theta)d_i(X_n)
 \ge(1-\theta)\Gamma.
\tag{4.5}
\]

The opponents are unchanged along this one-player chord, so player \(i\)'s
complete cap is constant.  Hence \(H_n+1\) remains an exact cap attainer at
\(H_{n,\theta}\), and the target \(Y_n\) kills the mover debt exactly.

Jointly compactify the semantic/law points of \(X_n,Y_n,H_{n,\theta}\) and
call their limits \(x,y,h_\theta\).  One-player law affinity and coordinate
debt convexity give

\[
 D(h_\theta)\le(1-\theta)D(x)+\theta D(y)=D_*.
\tag{4.6}
\]

Global minimality gives the reverse inequality.  Equality of the sum forces
equality in every coordinate convexity inequality:

\[
 d_k(h_\theta)
 =(1-\theta)d_k(x)+\theta d_k(y)
\qquad(k\in I).
\tag{4.7}
\]

Moreover,

\[
 d_i(x)\ge\Gamma,\qquad
 d_i(y)=0,\qquad
 d_i(h_\theta)\ge(1-\theta)\Gamma.
\tag{4.8}
\]

Since \(D(y)=D_*>0\), its positive-debt support is nonempty, and (4.7)--(4.8)
give the strict inclusion

\[
 \boxed{
 \varnothing\ne\operatorname{supp}^+d(y)
 \subsetneq\operatorname{supp}^+d(h_\theta).}
\tag{4.9}
\]

The terminal law is affine in the one moved stopping law.  By (3.5), the
joint law at \(y\) has singleton-\(i\) mass at least \(\Gamma/M\), and the
joint law at \(h_\theta\) has singleton-\(i\) mass at least
\(\theta\Gamma/M\).  Thus both minimum joint-law points have a named
positive finite atom, while the actual chord edges (4.5) retain fixed gain.

Same-point source causalization therefore builds complete
FinFourMinimumAtomProducer objects at \(h_\theta\) and \(y\), using the
literal families (4.4) and (2.2).  Re-extract a tangent family at \(y\).  As
in the checked renewable support construction, give the one nonrecurrent
origin state for the incoming chord rank \(5\), and give every later tangent
node the rank

\[
 1+|\operatorname{supp}^+d|
\tag{4.10}
\]

Equation (4.8) gives \(d_i(y)=0\), so
\(|\operatorname{supp}^+d(y)|\le3\); its tangent-node rank is at most \(4\).
Thus the origin-to-\(y\) entry is strict, and
every later recursive minimum child is handled by the existing canonical
support descent.

No claim is made that the incoming response edge is itself a column of the
new tangent family.

## 5. Application to a bounded finite response component

Let a source-attached finite pure-clock response component use deadlines at
most \(H_n\).  Solving the timing game (1.4) may destroy the component's two
sure clocks.  Under no uniform equilibrium, Section 2 forces an omitted
deadline \(H_n+1\) of gain at least \(\Gamma\).

Sections 3--4 show that this omitted response is not an additional
projective residual:

\[
 \boxed{
 \begin{array}{c}
 \text{bounded finite response component}\\
 \Downarrow\\
 \text{finite timing Nash + first omitted exact cap clock}\\
 \Downarrow\\
 \text{source-supported off-minimum paid retraction}\\
 \text{or a positive-atom minimum chord with strict support descent.}
 \end{array}}
\tag{5.1}
\]

The result uses the retained minimum source in Alternative A and regenerates
a literal minimum source from the actual omitted-clock family in Alternative
B.  Finite ancestry of the original response-cycle vertices is not used as a
substitute for either construction.

## 6. Sources inspected

- formalized/FINITE_DEADLINE_NASH_PROJECTIVE_BOUNDARY_AND_COMPATIBILITY.md;
- formalized/FIN4_FINITE_PURE_CLOCK_EXACT_RESPONSE_CYCLE.md;
- formalized/FIN4_SIGNED_SOURCE_RETRACTION_AND_NEAR_MINIMUM_RESPONSE_CYCLE_CONTRACTION.md;
- formalized/FIN4_MINIMUM_RESPONSE_CHORD_ATOM_AND_SOURCE_REGENERATION.md;
- formalized/CANONICAL_FIN4_RENEWABLE_MINIMUM_SOURCE_SUPPORT_DESCENT.md;
- notes/CODEX_SPINOZA__CAP_BAND_CUT_MINIMUM_CHORD_RENEWABLE_SUPPORT_DESCENT.md;
- notes/SOCIAL_WEIGHT_REVIEW__OFF_MINIMUM_PURE_CLOCK_RESPONSE_CYCLE_TEMPORAL_ATTACK.md;
- UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean;
- UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawMinimumFiberAffine.lean; and
- ../Research/Quitting/SourceFaithfulMinimumLawCausalization.lean.

## 7. Boundary and nonclaims

- The finite menu must contain every date \(0,\ldots,H_n\) and Never.
  Otherwise an omitted internal time, not \(H_n+1\), may realize the cap.
- The factorization (3.2) uses the project convention that all Never pays
  zero.
- The exact singleton atom comes from the all-opponents-Never cylinder; no
  tightness or datewise pigeonhole argument is used.
- Alternative A still terminates at the generic off-minimum paid-port waist.
- Alternative B is a source-regenerated finite-rank entry, not an exact
  Nash--Bellman block or a terminal approximate Nash profile.
- The timing Nash laws need not be compatible across horizons, and no inverse
  limit of them is asserted.

## Next exact question

Can the fixed singleton atom of the omitted-clock child strengthen the
off-minimum retraction in Alternative A into a post-mark paid splice or an
exact charged return?  This is the only remaining bounded-component output
not already placed in the renewable support rank.
