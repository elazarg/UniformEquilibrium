# Review of `NONLOCAL_RECENTERING_ATTACK.md`

## Verdict

The note contains two useful ordinary-mathematics components:

1. the exact affine covering screen for stationary one-owner profiles; and
2. a recentered compactification in which positive reach of a marked date
   gives summable negative-time hazard and retains the marked root at time
   zero.

The second component is a sensible candidate state representation for the
relative-timing information lost by the ordinary terminal-law limit.  It does
not yet cross the current Fin4 source-sewing barrier.  One displayed estimate
in Lemma 4.3 is false as written, but has a short repair.  The proposed
iteration in T3 needs substantially more than the uniform-floor target N1: it
needs later marks to be realized in the same ancestry/chronology.

This is therefore worthwhile internal mathematics, not a completed Fin4
consumer or an export-ready packet in its present form.

## 1. The solo screen

Lemma 2.1 is correct.  Against stationary owner hazard `q > 0`, an outsider's
pure stopping-time payoff lies on the segment between the quit-now value

\[
q r_o(\{j,o\})+(1-q)r_o(\{o\})
\]

and the Never value `r_o({j})`.  Arbitrary behavioral responses add no larger
value.  The owner's cap is the maximum of `r_j({j})` and zero.  Corollary 2.2
then follows from the stated terminal gap, subject only to matching the strict
versus weak convention of the chosen gap theorem.

The covering viewpoint is useful for exact candidate-table screening.  The
general semialgebraic remark is plausible, but should be separated from the
proved one-owner formula unless the full-support stationary cap formula is
also stated.

## 2. Uniform atom floor

Lemma 3.1 is correct if `F` is explicitly the minimum fibre of the **joint
semantic/law carrier** and the cited hard-residual theorem says that every
point of this joint fibre has positive finite-terminal mass.  A semantic point
alone need not determine a law, so the current notation `mu_z` should be
replaced by a joint point or an explicit law projection.

This compactness argument gives a uniform floor for the maximum terminal atom.
It does not give a uniform floor for a particular label, selected chronology,
reached row, or paid gain.

## 3. Recentered kernel existence

The core estimate in Theorem 4.2 is correct.  After subsequence extraction one
should also split the marked dates into:

- a constant bounded subsequence; or
- a subsequence tending to infinity.

The proof as written uses `tau_n >= s` for each fixed `s` without stating this
split.  In the bounded case the extension by zero makes the same conclusion
immediate after controlling the finitely many actual pre-mark rows.  In the
cofinal application it is cleaner simply to assume `tau_n -> infinity`.

For every finite negative window, the reach floor bounds its product survival
below by `lambda`; passing to the pointwise limit and using
`u <= -log(1-u)` gives the asserted total negative-time hazard bound.  This is
an honest preservation of relative timing around the mark.

Proposition 4.4 is also correct when "the pair quits" means the exact marked
coalition event.  Unconditional marked mass at least `lambda` gives both reach
at least `lambda` and conditional root mass at least `lambda`, hence the
conservative `lambda^2` floor in each finite negative truncation.

## 4. Lemma 4.3(2) is false as stated

The statement quantifies over `s' >= s`.  Taking `s'=s` forces

\[
|B_i(\kappa^{(s)})-
  \max(B_i(\kappa^{(s)}),r_i(\{i\}))|
\le 4R\delta_s.
\]

This need not hold.  Let all negative-time hazards be zero, let an opponent
quit surely at time zero, and give player `i` payoff `-1` both when that
opponent quits alone and when `i` quits simultaneously, while
`r_i({i})=1`.  At `s=0`, `delta_0=0` and the behavioral cap is `-1`, so the
left side is `2`.

The intended result has a short repair.  For `s' > s`, the extra nonempty
window lets the deviator attempt a solo quit before the common suffix.  The
opponents' total hazard in that window is at most `delta_s`, and coupling gives

\[
\left|B_i(\kappa^{(s')})-
\max(B_i(\kappa^{(s)}),r_i(\{i\}))\right|
\le O(R\delta_s).
\]

Moreover, for `s >= 1`, quitting at the first row of `kappa^(s)` gives

\[
B_i(\kappa^{(s)})
\ge r_i(\{i\})-O(R\delta_{s-1}).
\]

Combining these two bounds proves that the caps are Cauchy, gives the same
limit inequality `b_i >= r_i({i})`, and therefore recovers the carrier-limit
conclusion.  Constants should be recomputed when the corrected lemma is
written.

## 5. The remaining mathematical gap is co-realization, not just N1

T1 is honestly open: pointwise convergence of the nonnegative-time hazards
does not identify future terminal semantics because mass may escape to later
dates or Never.  A genuine tightness hypothesis would fix that, but the note
does not derive one from the source.

T3 contains the more important overreach.  From the fact that a post-mark tail
has returned to the minimum fibre, one may apply the source theorem again and
obtain another source chronology.  It does **not** follow that the second-round
mark occurs at a later date of the same original profile, or even in a profile
extending its retained post-mark tail.  Uniform lower-semicontinuous choices of
`lambda` and `g` would not repair this ancestry mismatch.

The required additional producer is a source-faithful renewal statement:
given the actually reached post-mark tail, construct the next minimum source
as a literal continuation/refinement of that same ancestry, with a later mark
and controlled conditional error.  Only after that result and uniform floors
are both available can multiple paid marks be placed inside one kernel.

This is exactly where the recentered object meets, rather than solves, the
nonperturbative source-sewing problem.

## 6. Strongest honest conclusion

After the local repairs, the note establishes:

> A cofinally reached marked chronology admits a two-sided hazard-kernel limit
> with summable past, a well-defined carrier semantic boundary, an
> all-Continue cap root at that boundary, and a fixed positive marked event at
> time zero.

That is a useful representation theorem.  It preserves one marked port and
its all-Continue boundary in one extension-compatible family.  It does not
yet preserve the future tail semantics, create a second mark in the same
ancestry, supply an exact Nash--Bellman chronology, or consume the inert Fin4
branch.

## Narrow source search

I searched the quitting Research/Diagnostics tree and the maintained frontier
for recentered or centered-window kernel declarations.  I found related
normalized omega-chain and window-extraction work, but no declaration with
this actual two-sided hazard-kernel statement and boundary-cap conclusion.
That is only a narrow novelty check, not evidence of Lean certification.
