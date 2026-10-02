# Independent falsification review of the full-debt cap-near contraction

Reviewer: `CODEX_DESCENDANT`

Candidate reviewed:
`/tmp/FIN4_FULL_DEBT_CAP_NEAR_RESPONSE_SUPPORT_CONTRACTION.md`

## Verdict

**PASS.**  I found no mathematical, probability-mode, unrestricted-response,
source-coherence, or conjecture-boundary blocker.  The packet is a genuine
contraction of the supplied full-debt Fin4 minimum source to either the
already named off-minimum actual-reach paid-port waist or a complete minimum
source with positive-debt support at most three.  It does not consume either
output, and the packet states that limitation accurately.

I independently tried to falsify the construction with finite clocks, bad
mass only at Never, infinitely many bad finite clocks, a Never receiver,
prefix deviations before the selected cut, a sure quitter inside the copied
word, and cap maximizers that switch between prefix and suffix.  None breaks
the stated result.

## 1. Unrestricted stopping-law representation and redistribution

Against fixed opponents, an arbitrary behavioral strategy of the mover is
equivalent on the unique live history to a probability law \(\nu\) on
\(\mathbb N\cup\{\infty\}\).  Conversely, its conditional hazards realize
that law.  This equivalence remains valid against arbitrary one-player
counterfactuals by another player: until absorption there is only the public
all-Continue history.  Thus the proof is not restricted to finite-support,
stationary, bounded-memory, or preselected pure-time deviations.

For \(B=\sup_qv(q)\), the gap \(B-v(q)\) lies in \([0,2M]\).  Moving all
source mass on

\[
 \mathcal A_\varepsilon=\{q:B-v(q)>\varepsilon\}
\]

to one \(\varepsilon/2\)-near maximizer \(r\) gives, exactly,

\[
 U_i(\tau)\ge B-\varepsilon,\qquad
 d_i(\tau)\le\varepsilon,\qquad
 U_i(\tau)-U_i(\sigma)\ge d_i(\sigma)-\varepsilon.
\]

The mover cap is unchanged because the opponents are unchanged.  No cap
attainment is assumed.  The estimate

\[
 d_i(\sigma)\le
 \varepsilon+2M\nu(\mathcal A_\varepsilon)
\]

also proves that the moved set has positive source mass when
\(0<\varepsilon<d_i(\sigma)\).

The word “support” in the proof is correctly read as positive PMF mass (or
almost-sure support), not topological support at the limit point Never.  The
argument itself is pointwise on the mass-bearing clocks and is unaffected by
the possible discontinuity of pure-time value at Never.

## 2. Finite cut and live-prefix reach

If a finite bad clock has positive mass, the set of such dates has a least
member \(b\).  Otherwise all bad mass is at Never and \(b=\infty\).  With
\(c=\min\{b,r\}\), one has \(c<\infty\): a bad Never clock cannot also be the
near-cap receiver.  The pushed and original laws agree strictly before
\(c\), hence their live hazards may be realized literally equal there.

Under the coupling \(Q\mapsto f(Q)\), the terminal outcomes can differ only
if every player reaches \(c\).  Therefore

\[
 d_i(\sigma)-\varepsilon
 \le 2M\Pr_\sigma(\text{joint reach of }c).
\]

The boundary cases check exactly:

- bad mass only at Never gives finite receiver \(r=c\);
- receiver Never forces a finite bad clock and \(c=b\);
- infinitely many finite bad dates still have a least positive-mass bad date
  at each fixed source;
- \(c=0\) gives reach one; and
- a countable clock law cannot have positive diffuse mass with every clock
  atom zero.

Only equality on the unique live history is claimed.  The packet correctly
does not claim equality of arbitrary unreachable descriptions.

## 3. Compact split and minimum chord

Along a full-debt realizing family, fixing any player \(i\) with limiting
debt \(a>0\) and taking \(\varepsilon_n\downarrow0\) gives a common
subsequence with gain at least \(a/2\), joint source reach at least
\(a/(4M)\), and target mover debt tending to zero.

If the limiting target debt sum is strictly above \(D_*\), eventual strict
off-minimality and literal one-replacement ancestry are exactly the inputs of
the private supplied-ancestry constructor underlying
`QuittingOffMinimumActualReachPaidPort`.  The port's selected paid row is a
new row at the target; the candidate does not conflate it with the
redistribution edge.

In the minimum arm, mixing only the mover's complete stopping law is an
ordinary private behavioral randomization, not a public mixture of profiles.
Prescribed payoff and terminal law are affine.  Every nonmover cap is a
supremum of affine response payoffs and hence convex; the mover cap is
constant.  Thus each coordinate debt obeys the stated chord inequality.
Global minimality forces equality of the summed limit, and the four
nonnegative coordinate slacks must separately vanish.  Full debt at the
source chord endpoint then gives support four at \(h^s\), while
\(d_i(y)=0\) and \(D(y)=D_*>0\) give nonempty support of size at most three at
the target.

## 4. Copied exact prefixes and complete caps

Arbitrarily long exact cap--Nash words exist recursively over each actual
chord suffix.  Exact debt scaling and the global lower bound give

\[
 D_*\le q_nD(H_n^s),
\]

so \(q_n\to1\).  Copying the same word to the target suffix preserves the
literal one-player update.  The suffix gain is multiplied by \(q_n\), and a
short algebraic use of equal mover caps at the two suffixes gives exactly

\[
 d_i(W_n\star\tau_n)=q_nd_i(\tau_n)\longrightarrow0.
\]

I specifically checked the complete-cap estimate against a deviator who
stops inside the prefix.  Conditional on all opponents surviving the word,
such a response is either singleton cash-out inside the word or a genuine
suffix response.  Every discrepancy is confined to opponent absorption in
the word, of probability at most \(1-h_{k,n}\), and so costs at most
\(2M(1-h_{k,n})\).  Since joint survival tends to one, every deleted-player
opponent survival does too.  The positive-minimum singleton margin makes the
tail cap the eventual maximum.  This proves convergence of the complete
semantic/law packets of both copied families, not merely their prescribed
payoffs.

## 5. Source regeneration and rank scope

The hard-residual positive-finite-atom theorem applies separately to the two
exact minimum joint-law limits.  The packet then uses
`nonempty_sourceFaithfulMinimumCausalChronology`, not the stronger fixed-mark
causalization.  That theorem retains the supplied copied profile family and
reselects only finite windows, dates, and exact root words.  Packaging it as
in `CanonicalPairFullReplacementSourceRegeneration.lean` therefore produces
complete same-residual `FinFourMinimumAtomProducer` objects without replacing
the response target by an unrelated realizer.

The rank claim is also stated at its valid strength: one phase change enters
a source of support at most three, after which at most two further nonempty
strict-support descents can occur inside the existing renewable tangent
trace.  It is not claimed to be a global rank across arbitrary atlas returns.

## 6. Novelty, consumer, and Lean handoff

The fixed-threshold common-prefix fork does not make the target debt vanish.
The new result simultaneously retains fixed source reach and drives one
target debt coordinate to zero, which is the strict new contraction.

The actual-data adapter, the two downstream waists, the exact missing public
constructor in the strict arm, and the ordinary-mathematics common-prefix cap
lemma are all named.  The suggested Lean surface does not assume the desired
support contraction as a structure field; it exposes the stopping-law map,
cut, reach inequality, chord, copied prefix, and regenerated sources from
which the contraction is proved.

No unresolved objection remains.  Once this review is linked as the second
independent falsification review, the candidate satisfies criterion 7 of
`exports/README.md` for its unrestricted behavioral-strategy claim.
