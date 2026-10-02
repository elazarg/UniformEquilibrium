# Adversarial review of the proposed Fin4 tail-escape consumer

Reviewer: `ATLAS_FALSIFIER`

## Verdict

**FAIL** for the claimed tail-escape consumer.

The exact maximal-cap-prefix debt telescope is valid for an actual escaped
tail.  The finite pure-coalition graph dispatch is also valid for an actual
profile carrying a marked atom.  The proposal cannot compose them: in
`TailEscapeSubsequence`, the positive nonsingleton atom occurs at the marked
row of the near-minimum **source profile**, while the escaped semantic tail is
the continuation strictly after that row.  The escaped tail does not carry
the source atom.  Sections 1--3 begin by assigning both data to one profile
`tau`, which is not furnished by the checked structure.

Even if that mismatch were added as a new hypothesis, the spending arm proves
only return of the scalar total debt toward \(D_*\), not payoff near-return or
punishment-floor admissibility.  The stall siblings preserve a literal root
word but not its cap--Nash proofs after the marked root is changed.  Finally,
declaring the unresolved singleton/monodromy output to have a smaller natural
number is not a well-founded atlas descent unless a downstream consumer is
proved not to regenerate the raw tail-escape node.

## Declarations and structures checked

- `TailEscapeSubsequence`, `SelectedRows`, `prefixedProfile`, `shiftedStage`,
  `tailPair`, `selectedStageMass`, and `selectedTailExcess` in
  `Research/Quitting/NonsingletonMinimumLawLinearTransfer.lean`;
- `quittingTerminalSemanticDebtSum_prefix_eq_continueMass_mul_of_capNash` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetExcursionReturn.lean`;
- `capNashPrefix_tailEscape_exact_account` and
  `capNashReturnSelection_iff_tailEscape_prefix_nearMinimum` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticStrictTailEscapeReturn.lean`;
- `capNashTailEscapeReturnSelection_retains_causalSuffixAtom` in
  `Research/Quitting/CausalTailEscapeReturnGate.lean`;
- the definition of
  `QuittingPositiveCumulativeAdmissiblePayoffNearReturnFamily` in
  `UniformEquilibrium/Quitting/Projective/CumulativeChargeNearReturn.lean`.

## 1. Exactification and debt scaling: valid in isolation

Let \(\tau_0\) be any actual profile.  If \(q_k\) is exact cap--Nash against
the actual cap of \(\tau_k\), and

\[
 \tau_{k+1}=q_k\triangleright\tau_k,
 \qquad s_k=\Pr_{q_k}(\mathbf C),
\]

then the checked coordinatewise scaling theorem gives

\[
 D(\tau_{k+1})=s_kD(\tau_k).
\]

If one fixed terminal event really lies in \(\tau_0\) after all inserted
roots, its mass also scales by \(s_k\).  Under those two hypotheses the
mass/debt ratio and the telescoping account

\[
 \sum_{k<K}D(\tau_k)(1-s_k)=D(\tau_0)-D(\tau_K)
\]

are correct.  Maximum absorption is not needed for these identities, though
it gives a canonical selector.  Positive global minimum debt ensures every
selected root has positive joint survival.

Thus Section 1 is a sound generic lemma for a profile carrying both the debt
and the later event.  It is not a lemma about the current
`TailEscapeSubsequence` entrance.

## 2. The source atom is on the wrong side of the escaped tail

For selected row \(n\), the checked definitions are

\[
 \operatorname{source}_n
 =\operatorname{prefixedProfile}(n),
\]

\[
 t_n=\operatorname{shiftedStage}(n),
\]

and

\[
 \operatorname{tail}_n
 =\operatorname{quittingAllContinueProfileSpine}
    (\operatorname{source}_n,t_n+1).
\]

The mass field is

\[
 \Pr_{\operatorname{source}_n}
   (S\text{ terminates at }t_n)>\lambda,
\]

whereas the escape field is

\[
 D(\operatorname{tail}_n)-D_*\ge h.
\]

The terminal event at \(t_n\) is not an event of
\(\operatorname{tail}_n\), whose time zero is the old time \(t_n+1\).
Consequently there is no actual profile \(\tau\) supplied by
`TailEscapeSubsequence` satisfying simultaneously

\[
 D(\tau)\ge D_*+h,
 \qquad
 \Pr_\tau(S\text{ at its marked date})>\lambda.
\]

This invalidates the opening premise of Section 1 and hence equations
(2)--(4) as an application to `E`.

There are two natural attempted repairs, and neither gives the stated proof.

1. Prefix the exact cap roots before the escaped tail.  Then their debt
   scaling is valid, but the old source atom is absent.
2. Insert the exactified tail back after the old marked row.  Then the old
   stage atom is preserved at the source row, rather than multiplied by the
   cap-root survival.  The semantic debt of the whole source is not the debt
   of the exactified tail and does not satisfy equation (1).

A two-stage regression makes the separation literal.  Let a source profile
absorb in a fixed coalition at date zero with probability one, and prescribe
an arbitrary high-debt continuation after the counterfactual all-Continue
outcome.  The source atom has mass one, while the shifted tail is precisely
the arbitrary continuation.  Exact cap-prefixing that continuation changes
its debt but has no probabilistic relation to the already-absorbed source
atom.  This is exactly the semantic arrangement encoded by the selected
marked row and `tailPair`.

The existing one-step return gate does not contradict this audit.  It accepts
an atom already lying in the supplied `continuation` and prefixes a root in
front of that same continuation.  `TailEscapeSubsequence` instead supplies
the atom one row before its escaped continuation.

## 3. The spending arm has no payoff return

Suppose, counterfactually, that one profile did carry both data.  Equations
(1)--(5) would show that a finite exact cap stack spends at least \(h/2\) of
total semantic debt while ending at a point with

\[
 D(\tau_K)\le D_*+\eta.
\]

This does not produce a
`QuittingPositiveCumulativeAdmissiblePayoffNearReturnFamily`.  That structure
requires, for every endpoint tolerance, exact punishment-floor-admissible
states and a charged path whose **prescribed payoff vectors** at its two ends
are coordinatewise close.  Closeness of the scalar debt sums to the same
minimum value implies neither

\[
 U(\tau_K)\approx U(\tau_0)
\]

nor closeness to the prescribed payoff of any selected minimum state.
Different points of a minimum-debt fiber may have separated payoff vectors.

The proposal supplies no fixed source payoff, no subsequence making the two
endpoint payoff vectors coalesce, and no theorem converting scalar debt
return plus a suffix atom into payoff return.  It also does not construct the
punishment-floor state annotations required by the cumulative-charge
relation.  Exact cap--Nash roots against displayed caps provide the debt
scaling identity; they do not by themselves fill these payoff and floor
fields.

Thus the sentence "applying the existing causal return/near-return compiler"
invokes a producer which is not present among the cited declarations.  The
checked `capNashReturnSelection_iff_tailEscape_prefix_nearMinimum` concludes
only the total-debt inequality displayed in its name.

## 4. The quantitative stall is a valid reference family

For a genuine exactification orbit, if its limiting debt stays uniformly
above \(D_*\), then

\[
 a_k\to0.
\]

Finite terminal windows of arbitrarily small-absorption exact roots can be
selected, and any event genuinely lying in the common suffix retains the
ratio-derived mass floor.  This is a useful generic stall reference family.

Again, the current tail-escape atom is not such an event.  More importantly,
the exactness belongs only to the reference orbit.

## 5. Pure siblings destroy the exact-prefix certificate

Let an exact reference profile have the literal form

\[
 q_{N-1}\triangleright\cdots\triangleright q_0
   \triangleright X,
\]

where each \(q_k\) is cap--Nash against the cap of its actual suffix.  If a
root inside \(X\) is replaced to form a pure sibling \(X'\), then the caps of
the suffixes below every copied \(q_k\) may change.  Therefore one retains the
literal word

\[
 q_{N-1},\ldots,q_0,
\]

but not the assertions that its roots are cap--Nash for \(X'\).  This is the
same source/target distinction already encountered in minimum-singleton clock
compression.

Consequently the singleton and monodromy siblings in Section 3 do not carry:

- an exact cap--Nash prefix stack for their own suffixes;
- the reference lower bound \(D\ge D_*+\eta_0\); or
- the old low-tail inequality.

They do retain the literal past, marked reach, marked stage mass, and
post-date tail, provided those data are first supplied on a common reference
profile.  The one-date payoff identity and mover-cap invariance are exact.
This is a horizontal actual-data adapter, not a vertical stall chronology.

## 6. The finite pure endpoint dispatch itself

Given an actual profile with a positive marked nonsingleton atom, the pure
sibling construction and equations (8)--(10) are valid.  A nonsingleton sink
is an exact terminal Nash profile against arbitrary behavioral deviations.
If a singleton is first reached, the strict finite path has a positive
table-dependent minimum gain and lossless marked mass.  If a nonsingleton
cycle is reached, its length is at most eight and the existing Fin4
nonsingleton cube classifier applies.

This dispatch is already horizontal.  It does not use the escaped-tail debt
or maximal exactification.  Its singleton output is the same weak
concentrated-singleton node whose consumer remains open; its monodromy output
still needs the source-matched vertical repair/chronology theorem.

## 7. The proposed rank is not well founded by declaration

Assigning numerical labels

\[
 \operatorname{rank}(\text{tail escape})=2,
 \qquad
 \operatorname{rank}(\text{stall singleton/monodromy})=1
\]

does not prove well-founded descent.  A rank-1 atlas state must come with an
existing consumer which cannot return a raw tail-escape state of rank 2, or
with a structural invariant proving that return impossible.  Neither is
provided.  Storing the reference stall family next to the horizontal sibling
does not make its exact roots valid for the sibling, and no checked consumer
uses the proposed sum passport.

The assertion "there is no constructor back" is therefore a choice of API,
not a mathematical theorem.  Re-running the known singleton or monodromy
dispatch can expose another tail escape unless an additional invariant rules
that out.

## Salvageable results

The proposal contains three worthwhile but separate lemmas:

1. the generic mass/debt ratio and telescope for a cap-exactification orbit
   when the marked event is actually in its suffix;
2. the spending/stall scalar dichotomy for that reference orbit; and
3. the pure nonsingleton endpoint sink/singleton/cycle dispatch at one actual
   marked row.

None currently consumes `TailEscapeSubsequence`.  A valid repair needs at
least one genuinely new bridge:

- an internal-suffix debt account that embeds cap exactification after the
  causal marked row and returns the **whole source payoff**;
- a theorem extracting a new positive event from the escaped tail itself,
  rather than reusing the pre-tail atom; or
- a proof that the paired reference-stall/horizontal-sibling object has a
  downstream consumer which preserves exactness or strictly decreases an
  independently defined structural rank.

## Unresolved objections

1. The source atom and escaped debt belong to different actual profiles.
2. Scalar debt return is not prescribed-payoff near-return.
3. Punishment-floor admissibility of the proposed exact path is not supplied.
4. Pure sibling updates invalidate the copied cap--Nash prefix proofs.
5. The sibling outputs do not retain the reference escape or low-tail bounds.
6. The proposed natural-number rank has no theorem preventing regeneration
   of the raw tail-escape node.
