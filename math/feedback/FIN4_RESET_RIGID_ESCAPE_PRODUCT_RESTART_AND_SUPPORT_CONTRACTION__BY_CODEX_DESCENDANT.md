# Adversarial review of the reset-rigid escape product restart

Reviewer: `CODEX_DESCENDANT`

Candidate reviewed:
`/tmp/FIN4_RESET_RIGID_ESCAPE_PRODUCT_RESTART_AND_SUPPORT_CONTRACTION.md`.

## Verdict

**REVISE / do not export the current packet.**

The product-minimum restart, both late-release identities, the minimum-fibre
convexity argument, and the one-way phase rank all survive my falsification
attempts.  There is, however, one exact hypothesis mismatch in the sole
route from the second release to the claimed strict-support child.

The packet version reviewed here
[`FIN4_MOVING_MARKED_PAIR_MINIMUM_CHORD_SUPPORT_DESCENT.md`](../formalized/FIN4_MOVING_MARKED_PAIR_MINIMUM_CHORD_SUPPORT_DESCENT.md)
assumed that its marked source coalition (K) was a **two-player coalition**
and that the mover (q\notin K) joins it.  The present candidate instead
applies that theorem with

\[
K=\{a\},\qquad K'=\{a,b\}.
\]

Thus the cited theorem did not instantiate.  The underlying argument appeared
to extend to every nonempty sure-quitter host (K), and in particular to the
singleton host used here, but that extension is neither stated nor proved in
the candidate.  It is load-bearing: its positive-residual arm supplies the
strictly earlier paid row, and its zero-residual/minimum arm supplies the
source-regenerated support child.  Until a nonempty-host/singleton-host
version is stated and independently checked, the packet has a deferred lemma
and fails mandatory gate criterion 2.

This is a bounded mathematical repair, not evidence against the intended
result.  With that repair, I found no second obstruction.

## 1. Product restart

The reconstructed profile

\[
\bar\rho=\bigotimes_{i<4}\mu_i
\]

is an actual independent behavioral profile, so global minimality gives
(D(\bar\rho)\ge D_*).  The strict/equality split is exhaustive.  In the
equality arm the hard-residual finite-atom theorem applies at the exact joint
point, not at an unrelated realizer.

If a finite law coordinate (m>0) is selected, countable additivity gives a
finite date with positive stage mass.  Repeating a deterministic all-Continue
root is legitimate because the global singleton moat gives

\[
B_i(\bar\rho)>r_i(\{i\})
\]

for every player.  The exact cap of one silent prefix is

\[
\max\{r_i(\{i\}),B_i(\bar\rho)\}=B_i(\bar\rho),
\]

so payoff, unrestricted cap, law, deleted laws, debt, and the finite atom are
unchanged.  Constant suffixes and words of (n+1) such roots really do fill
the fields of `QuittingMinimumLawCausalSuffixAtom`, and copying the table-level
hard residual gives the claimed complete source.

I tested the possible prefix counterexample in which a deviator Quits at a
new silent date.  It yields exactly the singleton term in the maximum above
and is excluded by the moat; there is no hidden early-deviation gain.

## 2. The two late releases

Profilewise common-quantile compression retains every marginal Never atom
and converges in the complete payoff--cap packet.  Taking (T_n) beyond all
finite support makes the first finite-cap replacement differ from the source
only on the joint-Never event.  Hence, before prefixing,

\[
\Pr(\{a\}\text{ at }T_n)=q_n,
\qquad
U_a(\widehat\rho_n^{[a,T_n]})-U_a(\widehat\rho_n)
=q_n r_a(\{a\}).
\]

The second replacement differs only when the same joint-Never event reaches
the row, and therefore has exact gain

\[
q_n\bigl(r_b(\{a,b\})-r_b(\{a\})\bigr).
\]

A common exact cap--Nash prefix multiplies both event masses and both payoff
differences by its joint Continue product (c_n).  Exact debt scaling and
global minimality give

\[
\frac{D_*}{D(\widehat\rho_n)}\le c_n\le1,
\]

so (c_n\to1).  The displayed (q/4) and (q\Gamma/4) floors are therefore
safe.  Each mover's unrestricted cap is unchanged because only that mover's
complete strategy changes.

Finite and diffuse stopping laws do not provide counterexamples: compression
is performed profilewise first, Never is retained explicitly, and the fresh
release date is chosen only after finite support has been obtained.

## 3. Minimum compactification and the exact mismatch

If the singleton targets (X_n) converge to a global minimum, their uniform
moving singleton mass is enough for supplied-family source-faithful
causalization.  No fixed date or independent realizer is needed.

For a general nonempty host (K), the rest of the intended argument is
mathematically sound.  The sure quitter in (K) screens the tail.  If the
target residual tends to zero and the endpoint excess tends to zero, the
literal one-row chord (H_n^s) satisfies

\[
d_i(H_n^s)\le(1-s)d_i(X_n)+s d_i(Y_n).
\]

Global minimality squeezes the summed inequality to equality, hence every
coordinate is affine.  The mover coordinate is positive at the interior
point and zero at the target, giving the strict support inclusion.

But the present source is (K=\{a\}), whereas the existing export states
`Fix a two-player coalition K`.  The candidate says merely “apply the
moving-row pair theorem with (K=\{a\})”; that is not a valid application.

The narrow repair is to prove a theorem with hypotheses

\[
\varnothing\ne K,\qquad q\notin K,
\]

or a singleton-host specialization.  Its proof must include the positive
residual localization: a cap-near response with residual (R>0) has an
actual source-supported first disagreement strictly before the mark.  The
support argument used for a pure pair still works because at least one
member of (K) Quits surely, so all supported source clocks at or after the
mark have the screened Continue value.  This observation indicates the
repair is short, but it is still a theorem that the current packet lacks.

## 4. Copied-prefix and cap audit

Assuming the singleton-host repair, copying the source causalization word
onto the target is correctly typed.  The word need not be cap--Nash for the
target.  It is used only as a common prescribed prefix.  Opponent-deleted
survival tending to one controls all unrestricted deviations, including
Quit inside the word, arbitrarily late stopping, mixtures, and Never.  The
singleton moat selects the tail-cap branch of the prefix maximum at both
minimum limits.

For the mover, opponents are identical at the copied-prefix endpoints, so
the complete caps are exactly equal.  Exact source debt scaling and common-
prefix payoff scaling then give target mover debt (c_nR_n\to0).  The target
family retains its moving coalition mass and can be causalized without
changing the supplied profiles or marks.

## 5. Rank and scope

The numerical ranges in the proposed phase rank are disjoint and correctly
ordered.  The restart is consumed once; later recursive transitions lie only
in the strict support-cardinality lane.  A child of support at most three has
at most two further nonempty strict support drops.

This is a rank on the explicitly defined producer transition system, not on
game time and not on arbitrary outer-atlas returns.  The packet states this
qualification correctly.  It also correctly does not call either late
release an exact Nash--Bellman edge and does not claim a terminal consumer for
the paid, off-minimum, or tangent exits.

## Required disposition

Do not place the current file in `exports/`.  Add and review the
singleton-host/nonempty-host moving-mark theorem, then update the source
correspondence and Lean handoff to name that precise adapter.  No other
mathematical change appears necessary from this review.

## Delta: the minimal singleton-host extension is valid

I separately tried to falsify the missing extension with arbitrary earlier
absorption, mixed prescribed clocks, a diffuse post-tail, and unrestricted
behavioral deviations.  The extension survives.  The exact theorem needed by
the candidate is the following.

Let (K\ne\varnothing), let (q\notin K), and suppose the root at the
actually reached marked date (t) is the pure coalition (K).  Let (X)
prescribe Continue for (q) at (t), and let (Y) change only that action to
sure Quit.  If

\[
\Delta=r_q(K\cup\{q\})-r_q(K)>0,
\qquad L=\Pr_X(\text{reach }t),
\]

then

\[
U_q(Y)-U_q(X)=L\Delta,
\qquad
d_q(X)=L\Delta+d_q(Y).
\tag{D.1}
\]

If (d_q(Y)=R>0), the standard supported pure-time paid-row theorem applied
to (Y) returns a row of gain at least (R/4), and its first disagreement is
strictly before (t).

The last assertion uses only (K\ne\varnothing).  Player (q)'s stopping
law in (Y) has no positive support after (t), because it Quits surely at
(t) whenever that date is reached.  If the selected source clock is already
before (t), the conclusion is immediate.  If the selected source clock is
(t), then every receiving clock strictly after (t), including Never,
Continues while the nonempty host (K) Quits and therefore receives
(r_q(K)), strictly below the source value (r_q(K\cup\{q\})).  A strictly
better receiving clock must consequently stop before (t).  This proves the
strict-earlier localization for a singleton host as well as for a two-player
host.

The rest of the moving-mark proof is cardinality-free.  The one-row chord is
an ordinary independent behavioral profile; prescribed payoff and law are
affine; unrestricted caps are convex; global minimality forces
coordinatewise affine debt in the minimum arm.  Source-faithful causalization
accepts the positive (K\cup\{q\})-mass for any nonempty terminal coalition.
The copied-prefix cap estimate depends only on opponent-deleted survival and
the singleton moat at the limiting minimum points, not on (|K|).

Thus there is no mathematical counterexample to the singleton-host repair.
The gate issue is solely that this general statement was absent from the
candidate and from the exact cited export surface.

## Final delta review of the repaired composite

Candidate hash:

    0a4ed6fb276da2cff64293a99395e65acb710f114fa1b3d0c2e8df8c17000594

**PASS.** The repaired candidate now proves the nonempty-host theorem in full
instead of applying the pair-only export at a singleton host. I rechecked the
new Section 4 against the failure isolated above.

The exact update and debt identities use only a nonempty sure-quitting host:

\[
U_q(Y)-U_q(X)=L\Delta,\qquad
d_q(X)=L\Delta+d_q(Y).
\]

They retain arbitrary earlier absorption and the literal post-mark tail.
In the positive-residual arm, the supported source stopping time belongs to
the target strategy, which Quits surely at the mark. If it is the marked
time, any later receiving clock is screened by the nonempty host and earns
the strict lower value \(r_q(K)\); hence every strict improvement starts
before the mark. This remains valid for a singleton host and for unrestricted
receiving times, including Never.

In the vanishing-residual arm, the law identities, response-chord cap
convexity, global-minimum squeeze, and strict support inclusion do not depend
on \(|K|=2\). The copied-prefix estimate covers unrestricted behavioral
responses through opponent-deleted survival, and the singleton moat selects
the tail cap at both limiting minimum points. The target causalization retains
the exact shifted \(K\cup\{q\}\) atom, so the regenerated source is attached
to the supplied family rather than to a fresh realizer.

I also rechecked the surrounding product restart, two releases, phase ranges,
and nonclaims. The product is tested against \(D_*\) before being used as a
source; deterministic all-Continue prefixing is exact by the singleton moat;
finite compression preserves all four Never atoms; root exactness is claimed
only on the unreleased source; and the rank is restricted to the displayed
one-way producer transition type. The packet still does not claim a temporal
edge across the product restart or a consumer for the paid/off-minimum/tangent
exits.

No mathematical export blocker remains in the repaired composite.
