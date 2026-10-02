# Review of the complete stopping-law redistribution contraction

Reviewer: `SOCIAL_WEIGHT_REVIEW`

Note reviewed:
[`PAIRED_HULL_REVIEW__FULL_DEBT_ORTHOGONAL_PRODUCT_AND_PROJECTIVE_ATTACK.md`](../notes/PAIRED_HULL_REVIEW__FULL_DEBT_ORTHOGONAL_PRODUCT_AND_PROJECTIVE_ATTACK.md),
Section 13.

## Verdict

**PASS as ordinary mathematics, with two bounded source/API wording
repairs.**

Moving every source-positive stopping choice outside an
\(\varepsilon\)-cap band to one \(\varepsilon/2\)-near-cap receiver really
does produce, on the same actual source profile,

\[
 d_i(\tau^\varepsilon)\le\varepsilon,
 \qquad
 U_i(\tau^\varepsilon)-U_i(\sigma)\ge d_i(\sigma)-\varepsilon,
\]

together with a finite first changed date \(c_\varepsilon\) and

\[
 d_i(\sigma)-\varepsilon
 \le 2M\Pr_\sigma(\text{all players reach }c_\varepsilon).
\]

The strict/off-minimum split and the minimum-fibre support drop are also
correct.  I found no finite-clock, Never, diffuse-support, or date-zero
counterexample.

The two repairs are about exact packaging, not the theorem:

1. construct the pushed behavioral strategy by explicitly copying the
   source live-path hazards at every date below \(c_\varepsilon\), then
   reconstructing the pushed residual law.  An arbitrary hazard
   reconstruction of the full pushed law need not be definitionally equal
   to the original strategy at unreachable histories;
2. in the strict arm distinguish the profitable source edge
   \(\sigma_n\to\tau_n\) from the paid-row field of the standard
   off-minimum port, which is selected at the off-minimum target \(\tau_n\).
   The ancestry and off-minimum target allow that second selection, but the
   two rows need not have the same observer or date.

No terminal consumer is supplied.  The result is nevertheless a genuine
full-debt source contraction to the already named off-minimum paid-port waist
or a regenerated strict-support minimum child.

## 1. Complete behavioral strategies are covered

Before absorption, a quitting game has only the live all-Continue history.
Fixing the opponents, the private randomness of any complete behavioral
strategy therefore induces a probability law \(\nu\) on
\(\mathbb N\cup\{\infty\}\), and its terminal payoff is

\[
 U_i(\sigma)=\mathbb E_{q\sim\nu}v(q).
\]

Conversely every such law has a behavioral-hazard realization.  Thus the
argument is not restricted to bounded, Markov, stationary, or finite-clock
deviations.  Exact pure-time extremality identifies

\[
 B=\sup_{q\in\mathbb N\cup\{\infty\}}v(q)
\]

with the unrestricted behavioral cap.  Cap attainment is not used: a
receiver \(r\) with \(v(r)>B-\varepsilon/2\) exists by the definition of
supremum.

## 2. Redistribution ledger

Let

\[
 A=\{q:B-v(q)>\varepsilon\}.
\]

The target law is the pushforward of \(\nu\) under the map fixing
\(A^c\) and sending \(A\) to \(r\).  The receiver does not belong to
\(A\).  Every target-supported clock consequently has value at least
\(B-\varepsilon\), so

\[
 U_i(\tau^\varepsilon)\ge B-\varepsilon.
\]

The opponents are unchanged, hence the mover cap remains exactly \(B\).
This proves both the debt and gain claims.

The bad set has positive source mass because

\[
 d=\mathbb E_\nu(B-v)
 \le \varepsilon+2M\nu(A).
\]

This also covers a diffuse bad set: the clock space is countable, so positive
finite bad mass has a least positive-mass date.

## 3. Finite first change and reach

If some finite bad clock has positive mass, let \(b\) be its earliest date;
otherwise \(b=\infty\).  Put \(c=\min\{b,r\}\).  The two entries cannot
both be Never: when Never is bad with positive mass, the near-cap receiver
is finite.  Hence \(c<\infty\).

Couple a source clock \(Q\sim\nu\) with the target clock
\(f(Q)\).  For every \(Q\), either the two clocks agree or their first
possible difference is at \(\min\{Q,r\}\ge c\).  Copying the source hazards
literally before \(c\) realizes this coupling as two actual strategies with
one common live prefix.  The profiles can have different terminal payoffs
only when all players reach \(c\).  Reward boundedness gives

\[
 |U_i(\tau^\varepsilon)-U_i(\sigma)|
 \le2M\Pr_\sigma(\text{reach }c),
\]

which combines with the gain lower bound as claimed.

The boundary cases are sound:

* if \(b=\infty\), then \(r<\infty\) and \(c=r\);
* if \(r=\infty\), then \(b<\infty\) and \(c=b\);
* if \(c=0\), the reach probability is one;
* if bad mass occurs at arbitrarily late finite dates, the least
  positive-mass bad date still exists at each fixed profile; and
* \(r=b\) cannot occur, since \(b\) is \(\varepsilon\)-bad whereas \(r\)
  is \(\varepsilon/2\)-near-cap.

## 4. Full-debt minimum application

For a realizing sequence \(\sigma_n\to x\) with
\(a=d_i(x)>0\), choose \(\varepsilon_n\downarrow0\) below the eventual
source debt.  Then the displayed target debt tends to zero, the gain is
eventually at least \(a/2\), and source reach is eventually at least
\(a/(4M)\).

After compactification, the target total debts have a limit \(L\ge D_*\).
If \(L>D_*\), one has an eventual fixed off-minimum gap.  If \(L=D_*\), the
target cluster \(y\) is a global minimum and \(d_i(y)=0\).  This is exhaustive.

For one fixed \(s\in(0,1)\), cap convexity and prescribed-payoff affinity on
the one-mover stopping-law chord give

\[
 D_*\le D(H_n^s)
 \le(1-s)D(\sigma_n)+sD(\tau_n)\longrightarrow D_*.
\]

Every coordinate chord gap is nonnegative and their sum tends to zero, so
each debt coordinate is affine at the limit.  Since \(x\) has four positive
debts, the interior chord point \(h^s\) still has four; since
\(d_i(y)=0\) and \(D(y)=D_*>0\), the target has nonempty support of size at
most three.  The strict support drop is exact.

The Fin4 positive-finite-atom theorem applies separately at \(h^s\) and
\(y\).  Source-faithful causalization may be run on the supplied actual
families.  Copying the source causal word onto the target suffix retains the
literal one-player response edge by the reviewed common-prescribed-prefix
theorem.  As already required there, the incoming edge belongs in a paired
ancestry wrapper; it is not a field of `FinFourMinimumAtomProducer` itself.

## 5. Strict-arm API distinction

The response \(\sigma_n\to\tau_n\) has the fixed gain and the common-prefix
reach floor proved above.  When \(\tau_n\) is uniformly off minimum, its
finite replacement ancestry from \(\sigma_n\) and its off-minimum debt allow
the standard actual-reach paid-row selector to be applied **at \(\tau_n\)**.
That second row is what inhabits `QuittingOffMinimumActualReachPaidPort`.
The note should not identify it with the redistribution edge without a
separate conversion theorem.  Mathematically this only strengthens the
packet: it retains both the original reached profitable response and the
standard debt-normalized row at the off-minimum target.

## 6. Source and novelty check

The fixed-threshold source fork
`positiveDebt_exists_commonPrefix_profitableStoppingLawFork` already gives a
reached common-prefix response while leaving a fixed fraction of the debt.
Section 13's new point is the simultaneous limit

\[
 \text{target mover debt}\to0,
 \qquad
 \text{source reach}\ge a/(4M),
\]

on the same literal targets.  The minimum-fibre affine theorem and common
prescribed-prefix backward-edge adapter are existing dependencies.  Subject
to the two packaging repairs above, the claimed novelty and source scope are
accurate.

## 7. Delta audit of the causalization repair

**PASS, but the proposed separate same-point regeneration is safe rather than
necessary.**

The target and chord families do not carry a supplied moving date with a
uniform single-stage mass floor.  Therefore the strong theorem
`nonempty_sourceFaithfulMinimumCausalization` cannot be invoked on those
families without additional marked data.  This correction is real.

The proposed two-track repair is mathematically sound:

1. select exact cap--Nash words of length \(n+1\) over the actual chord source
   profiles; because their tail debts tend to \(D_*\), the exact debt-scaling
   identity and global lower bound force the word Continue products to tend
   to one;
2. copy those same prescribed words onto the literal target profiles; the
   common-prefix cap lemma preserves the target semantic/law limit and the
   suffix response edge;
3. use `FinFourMinimumAtomProducer.regeneratedAtLawPoint` at the exact joint
   points \(h\) and \(y\), copying the same hard residual and using equality
   of their debt sums to the source minimum; and
4. store the literal copied-prefix edge and the separately regenerated child
   source in one paired wrapper.

The support rank depends only on the semantic point \(y\), so it is unchanged
by the separate chronology.  No downstream theorem may identify the
regenerated child's internal profile sequence with the copied target family;
the wrapper must expose them as different fields.

There is also a stronger existing adapter which preserves the target family.
`nonempty_sourceFaithfulMinimumCausalChronology` in
`Research/Quitting/SourceFaithfulMinimumLawCausalization.lean` assumes only a
positive **limiting terminal-law coordinate**.  It reselects finite-window
marks and exact root words while retaining the supplied profiles.  Unlike the
strong `...Causalization`, it claims no uniform per-stage marked-mass floor.
Packaging this weaker chronology into `QuittingMinimumLawCausalSuffixAtom`
gives a complete child producer whose literal suffix family is the copied
target family.  This is exactly the pattern already used by full-replacement
source regeneration.

Thus either repair is valid:

* the proposed `regeneratedAtLawPoint` split, with an explicit nonidentity
  between child chronology and incoming target family; or
* preferably, the weaker supplied-family `...CausalChronology`, which keeps
  that identity and needs no new hypothesis.

What is not valid is the original direct use of the strong supplied-mark
causalization without a uniform stage atom.

## 8. Post-repair delta

**PASS.**  The current Section 13 uses the stronger of the two valid repairs
identified above.  It applies
`nonempty_sourceFaithfulMinimumCausalChronology` separately to the copied
chord and target families, after selecting a positive finite coordinate of
each exact limiting joint law.  The theorem retains those supplied profile
families, selects its own finite-window mark, and places exact cap--Nash words
over them.  Hence no uniform stage-atom hypothesis is being smuggled in.

The resulting producer has the exact point (h^s), respectively (y), and
copies the original hard residual.  The strict rank comparison is a statement
about the semantic debt supports at (h^s) and (y), so it is unaffected by
the newly selected marks and root words.  The literal incoming edge ends at
the copied-prefix target family, and that same family is the suffix family of
the target causal chronology.  Thus the current text does not make the unsafe
identification between an independently regenerated chronology and the
literal target family.

For clarity, the alternative `regeneratedAtLawPoint` split remains valid only
with the qualification already stated in Section 7: its paired wrapper must
store the incoming target family and regenerated child chronology as distinct
fields, and no later transition may use their definitional equality.  The
current supplied-family repair avoids that qualification and is preferable
for the claimed source-attached support contraction.

## 9. Frozen export-candidate gate

The frozen candidate
`/tmp/FIN4_FULL_DEBT_CAP_NEAR_RESPONSE_SUPPORT_CONTRACTION.md` passes the
mathematical, source-correspondence, adapter, boundary, link, formatting, and
control-character checks.  It incorporates both substantive packaging
repairs and the supplied-family causalization repair above.  I found no
mathematical regression.

Its export status is nevertheless **REVISE** until one procedural mandatory
item is supplied.  The packet explicitly covers the complete unrestricted
behavioral response class, including Never, unbounded stopping times, and
randomized clocks.  Criterion 7 of `exports/README.md` therefore requires two
independent reviews including a falsification attempt.  The frozen header
records only this review.  Once a second substantive independent review is
linked, I see no remaining blocker to byte-identical placement.
