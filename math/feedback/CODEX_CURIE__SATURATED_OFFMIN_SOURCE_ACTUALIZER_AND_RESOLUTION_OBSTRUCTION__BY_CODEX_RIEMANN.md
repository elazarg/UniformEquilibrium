# Review of saturated off-minimum actualization and resolution loss

## Verdict

**REPAIR, with the central actualization result valid.**

The generic off-minimum carrier actualizer is mathematically sound.  The
present Lean proof of
`nonempty_quittingMarkedPairMinimumReturnActualizer` uses the equality
`point.wholeDebt = D_*` only twice, to replace `point.wholeDebt` by `D_*` in
the marked-mass and actual-gain lower bounds.  At an arbitrary normalized
slice point those two uses can be replaced by

\[
 D_*\le D(Q),
\]

which follows from `whole_semantic_mem_carrier` and the global minimum
hypothesis.  The closure sequence then gives literal finite common-prefix
descendants with any fixed mass floor strictly below (M(Q)) and any fixed
gain floor strictly below (G(Q)).

Two corrections are needed before the note is a sharp account of the
resolution obstruction:

1. the equality boundary (\lambda=M(Q)) is necessary but is not sufficient
   for eventual preservation of the strict packet floor; and
2. the already checked arbitrary-resolution owner-compressed source does
   provide a uniform **one-step** slack construction (and, by pre-funding, any
   prescribed finite number of saturated steps).  It still does not provide
   an indefinitely renewable positive floor.

## 1. Generic actualizer: PASS

The following replacement of the current proof is valid.  If

\[
 Q\in\mathcal C\cap\{D(\mathrm{tail})=D_*,\ mD\le M,\ gD\le G\},
 \qquad m,g,D_*>0,
\]

and (D_*\le D(Q)), then

\[
 M(Q)\ge mD_* ,\qquad G(Q)\ge gD_*.
\]

Thus raw orbit points converging to (Q) eventually have, for example,

\[
 M(X_n)\ge \frac{mD_*}{2},\qquad
 G(X_n)\ge \frac{gD_*}{2}.
\]

Nothing else in the constructor of
`QuittingMarkedPairMinimumReturnActualizer` uses minimum return.  The exact
raw identities in `NormalizedPassportPrefixOrbit.lean` give termwise:

* literal comparison and target profiles;
* one common finite prefix word;
* the shifted marked date and fixed labels;
* exact marked-owner defect zero;
* exact post-mark spine preservation; and
* the marked-mass and actual-gain identities.

Consequently these retained rows can be repackaged as a new
`QuittingMarkedPairDecoratedFamily`.  This is an executable family, not merely
a semantic selection.

One qualification in the note is important and correct: membership in the
raw-orbit closure does **not** make the selected `originRank` strictly
increasing.  Every natural-number sequence has a subsequence on which the
origin ranks are either constant or strictly increasing.  In the current
Fin4 selected family, the latter case gives genuinely cofinal original source
ranks because `FinFourNormalizedReturnSelection.sourceRank_strictMono` is
checked.  The constant case is executable but is not a cofinal regeneration
of the original source chronology; it is one fixed source row with varying
finite prefix words.  Downstream statements must retain this dichotomy.

## 2. Sharp old-floor criterion: boundary repair

For a raw sequence (Y_n\to Q), preservation of the same weak floor

\[
 \lambda\le M(Y_n)\quad\text{for all retained }n
\]

necessarily implies

\[
 \lambda\le M(Q).
\]

Every strict inequality (\lambda<M(Q)) is sufficient after deleting a
finite prefix.  The equality case is not sufficient from convergence alone:
the sequence may approach (M(Q)=\lambda) from below.  Hence equation (15)
in the note is a sharp **necessary** condition, while its strict form is a
clean sufficient condition.  It should not be called an iff at the boundary
without an additional one-sided approximation theorem.

For canonical half-density saturation,

\[
 M(Q)=\frac{M(P)D(Q)}{2D(P)}.
\]

Thus the direct condition is (\lambda<M(Q)) (sufficient) or

\[
 2\lambda D(P)\le M(P)D(Q)
\]

(necessary).  The weaker (2\lambda\le M(P)) is necessary but not
sufficient.  The note is correct on this distinction.

## 3. Existing selectable resolution gives one-step uniform slack

Section 4 is too pessimistic if read as denying a planned stronger input
resolution.  Current Lean already fixes one chronology and outsider before
the resolution quantifier:

* `exists_commonChronology_cofinal_ownerCompressedSingleton`;
* `exists_minimumReturnForcedPairSource_for_all_resolutions`; and
* `exists_normalizedReturnSource_for_all_resolutions`.

Let

\[
 \mu=\text{the selected singleton-law mass},\qquad
 0<D_*\le D(X)\le D^{\max}
\]

on the semantic carrier.  Fix a desired output floor (\lambda_0>0) with

\[
 \lambda_0<\frac{\mu D_*}{2D^{\max}}.
\]

Choose a stronger input resolution (\Lambda) satisfying

\[
 \frac{2\lambda_0D^{\max}}{D_*}<\Lambda<\mu.
\]

Run the checked forced-pair producer at (\Lambda).  Its compact base limit
(P) has (M(P)\ge\Lambda).  If its canonical normalized minimizer (Q) is
saturated, then

\[
 M(Q)
 =\frac{M(P)D(Q)}{2D(P)}
 \ge\frac{\Lambda D_*}{2D^{\max}}
 >\lambda_0.
\]

The generic actualizer can therefore be shifted and repackaged with the
preselected output floor (\lambda_0), on the same literal (\Lambda)-packet
and without observing (Q) before choosing (\lambda_0).  If one insists on
the current hardwired actualizer floor (mD_*/2), the same argument works
with the more conservative factor (4D^{\max}/D_*); the generic arbitrary
floor below (M(Q)) recovers the factor (2).

So the exact conclusion is:

\[
 \boxed{\text{the present source supports a source-uniform one-step floor.}}
\]

The packet and payer subsequence may depend on (\Lambda), but the chronology
and forced outsider do not, and all data within the selected packet remain
literal and fixed.  This is enough for the one-step statement.  It does not
preserve a packet that was first selected at the weaker resolution
(\lambda_0); instead it selects the packet once at the deliberately stronger
resolution (\Lambda).

## 4. Why this does not solve renewable resolution

The one-step strengthening does not invalidate the note's ultimate Zeno
obstruction.  After actualizing (Q), the new generic decorated family has a
fixed positive floor but does not inherit the original minimum-law
owner-compression theorem for all larger resolutions.  A second canonical
saturation can again lose a factor bounded below only by
(D_*/(2D^{\max})).

More generally, a desired floor (\lambda_0) can be pre-funded through any
fixed (N) saturated transitions by starting with

\[
 \Lambda>rac{2^N D^{\max}}{D_*}\lambda_0
\]

(with minor extra factors if one uses the current half-floor actualizer).
This is possible only while (\Lambda<\mu).  No fixed positive
(\lambda_0) can be pre-funded for arbitrarily many density halvings.
Indeed, after (N) exact halvings,

\[
 M_N=2^{-N}\rho_0D_N\le 2^{-N}\rho_0D^{\max}\longrightarrow0.
\]

Rerunning the original arbitrary-resolution source independently does not
chain from the newly selected (Q), so it is not a renewable descent or
return.  Thus the remaining obstruction is still genuine, but it should be
stated as:

\[
 \boxed{\text{arbitrary finite-depth slack is available; infinite renewable
 floor is not.}}
\]

## 5. Recommended repairs to the note

1. Keep Sections 1--2 and the fixed-origin/cofinal dichotomy.
2. Replace the boundary “exact criterion” language by necessary
   (\lambda\le M(Q)), sufficient (\lambda<M(Q)), with equality explicitly
   unresolved without one-sided control.
3. Amend Section 4 with the stronger-input construction above, citing the
   checked universal-resolution quantifier order.
4. Add the arbitrary finite-depth pre-funding consequence, while retaining
   the conclusion that it gives no infinite renewable rank.

With those repairs, the note gives a useful and honest result: source
actualization is solved, finite-step quantitative loss can be budgeted in
advance, and the surviving issue is specifically the zero-density/infinite
saturation limit rather than a one-step absolute-floor failure.

## Post-repair audit

**PASS.**  The revised note incorporates the substantive corrections above.

The strict-floor statement is now exact at the claimed scope:

* (\lambda\le M(Q)) is necessary;
* (\lambda<M(Q)) is sufficient after shifting the raw approximants; and
* equality is explicitly left dependent on one-sided approximation data.

The finite-(N) pre-funding formula also checks.  Along a genuinely chained
sequence of saturated retractions, with the next reassembled family based at
the preceding saturated point,

\[
 \rho(P_{k+1})=\frac12\rho(P_k).
\]

Consequently

\[
 M(P_N)
 =\frac{M(P_0)D(P_N)}{2^ND(P_0)}
 \ge\frac{\Lambda D_*}{2^ND^{\max}}.
\]

The strict choice

\[
 2^N\lambda_0D^{\max}/D_*<\Lambda<\mu
\]

therefore keeps every one of the first (N) saturated limit masses strictly
above (\lambda_0), so each raw actualizer can be shifted to the same declared
floor.  The argument correctly stops at arbitrary fixed finite (N); it does
not claim a single positive floor through an infinite halving chain.

The new deleted-survival Section 6 is also correct.  For literal pure-pair
descendants, (H_iH_j\le M) yields the exhaustive subsequential split.  A
visible host can be forced to Continue through the word and then assigned its
better marked endpoint, giving marked mass (H_h\ge\eta), a nonempty routed
coalition, zero host defect, and the literal old tail.  In the fully screened
arm the payoff/law difference is (O(M_n)), own-strategy invariance handles
the mover's cap, and coupling gives the other cap differences bounded by
(2RH_{i,n}).  The note does not overclaim near-minimality or a completed
atlas consumer for the host-compressed endpoint.

The fixed-origin/cofinal distinction remains stated honestly.  The only
remaining textual defect I found is a duplicated `\quad\Longleftrightarrow`
in equation (15); it is typographical and does not affect the mathematics.
