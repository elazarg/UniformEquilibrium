# Adversarial audit of reverse S.3 null-tail elimination and hardness padding

Reviewer: `CODEX_SPINOZA`

Reviewed note:
`notes/CODEX_NEGATIVE_CERTIFICATE__AKRS_REVERSE_S3_NULL_TAIL_AND_HARDNESS.md`

Reviewed SHA256:
`65e8358f8d2a81dc15278515d388ecedf5b1f1aa6caad36dc3f529f97b62ee71`

## Verdict

**PASS.**  I found no mathematical, quantifier, behavioral-strategy, or
source-correspondence defect in the corrected candidate.  In particular, the
null-tail alternative is now correctly inclusive, the arbitrary-Never
one-dummy table is exact, and the one-player cardinal shift is stated only as
a universal-across-cardinalities equivalence.

This verdict covers the ordinary mathematics in the exact reviewed hash.  It
does not prove reverse S.3, does not assign a Lean seal to the new null-tail or
dummy-source arguments, and does not turn the cardinal shift into a
same-cardinality theorem.

## 1. Null-tail lemma and quantifiers

The null-tail proof is correct.  From initial absorption and one restarted
tail with positive survival, a zero Continue-product factor occurs before the
restart, while every factor from the restart onward is positive.  Hence there
is a last zero factor `L`.  If

\[
 P_*=a_{L+1,\infty}>0,
\]

then for `n>L`,

\[
 a_{n,\infty}=
 {P_*\over\prod_{t=L+1}^{n-1}c(q_t)}\longrightarrow1.
\]

The inequalities
`a_{n,infinity} <= c(q_n) <= 1` and
`q_n^j <= 1-c(q_n)` therefore give `q_n^j -> 0` for every player.  The finite
terminal mass of the restarted tail is exactly `1-a_{n,infinity}`, so the
displayed finite coordinate bound gives `gamma_n^i -> z^i`.  The Quit endpoint
is a finite polynomial in the opponents' row probabilities and converges to
the own-singleton reward.  Passing to the limit in the global upper
row-perfectness inequality proves

\[
 r^i(\{i\})\le z^i+\varepsilon.
\]

No used-action lower inequality or every-tail hypothesis is silently used.

The alternative has the correct quantifiers.  If non-every-tail witnesses
exist along errors tending to zero, the lemma gives
`r^i({i}) <= z^i` for every player.  Against all-Continue opponents, an
arbitrary behavioral stopping law yields a convex combination of this
singleton payoff and the Never payoff, so all Continue is exact terminal
Nash.  If such witnesses do not occur arbitrarily near zero, one positive
threshold excludes every non-every-tail witness below it.  S.3 supplies a
witness at each sufficiently small error, and every such witness is then
every-tail terminating.  The two arms may coexist, as the candidate now says.

## 2. Exact arbitrary-Never dummy padding

At the stationary row where the dummy quits surely and all old players
Continue, every restarted tail absorbs in its first row.  Each old player has

\[
 C_i=V_i=H_i,
 \qquad Q_i=r^i(\{i\})\le H_i.
\]

The dummy has `Q_d=-P`.  Its unused Continue endpoint is also `-P`, because
all old players Continue in the current row and the next prescribed row again
makes the dummy quit surely.  Thus `Q_d=C_d=V_d=-P`.  Both the no-profitable-
action clauses and the lower clauses for used actions hold at error zero.

The arbitrary-Never adapter to the checked zero-Never padding is exact.  For
old player `i`, normalize every original terminal reward to `r^i(S)-z^i`.
The canonical checked upper and lower endpoints become `H_i-z^i` and
`L_i-z^i`, so the coordinate width remains `W_i=H_i-L_i`.  Specializing the
fresh type to `PUnit` makes the checked factor

\[
 {P\over P+|J|W}
\]

equal to `P/(P+W)`.  Adding `z^i` back to every old-player outcome, including
Never, recovers exactly the displayed arbitrary-Never padded table and
preserves every old unilateral gain.

## 3. Unrestricted behavioral retraction

The coupling covers arbitrary live-history behavioral sequences.  On the
dummy-only terminal event, counterfactually continuing the old random actions
produces either an original terminal payoff or `z^i`, hence a value in
`[L_i,H_i]`; outside that event, the padded and projected old outcomes agree.
This proves

\[
 U_i^G(\sigma)\le U_i^{\widehat G}(\widehat\sigma)
 \le U_i^G(\sigma)+\alpha W_i.
\]

After an arbitrary old-player behavioral deviation, the dummy-only event may
have a different probability, but only the one-sided comparison

\[
 U_i^G(\tau_i,\sigma^{-i})
 \le U_i^{\widehat G}(\widehat\tau_i,\widehat\sigma^{-i})
\]

is used.  The dummy's prescribed payoff is exactly `-P alpha`, while its
deviation to Never pays zero, so `P alpha` is bounded by padded
exploitability.  Combining the inequalities gives

\[
 E_G(\sigma)\le(1+W/P)E_{\widehat G}(\widehat\sigma),
\]

equivalently the claimed factor lower bound.  No finite-clock, stationary,
attainment, or restricted-controller assumption enters this step.

## 4. Cardinal shift and negative transport

An arbitrary nonempty `n`-player game is sent to an `(n+1)`-player game with
the exact stationary every-tail S.3 witness above.  Reverse S.3 at cardinality
`n+1`, followed by projection at padded error
`eta * P/(P+W)`, gives an `eta`-approximate terminal equilibrium of the old
`n`-player game.  The zero-player case is separately vacuous.  Therefore the
displayed equivalence is correct only, and correctly stated, after
quantification over every finite cardinality.  The pointwise factor also
transports any old all-profile exploitability floor to the padded table.

The small-error journal S.3 quantifier and the project's all-positive-error
type are correctly related by monotonicity, as checked by
`hasSmallAbsorbingSequentiallyPerfectProfiles_iff_table`.

## 5. Source and scope audit

I checked the source-facing claims against:

- `Literature/AshkenaziGolanKrasikovRainerAndSolan2024.lean`;
- `UniformEquilibrium/Quitting/Terminal/PassivePlayerPadding.lean`;
- `PassivePlayerPaddingCanonical.lean`;
- `PassivePlayerPaddingRetraction.lean`;
- `PassivePlayerPaddingExploitabilityRetraction.lean`; and
- `PassivePlayerPaddingCorollaries.lean`.

The Literature file defines S.3 with initial absorption, records the reverse
direction of the printed Theorem 3.4 with `sorry`, and states that the 24 May
2025 publisher update changed only an affiliation.  The candidate accurately
reports that status and no longer invokes an unsupported erratum.  It also
correctly labels the exact dummy-sure-Quit S.3 source and the null-tail lemma
as ordinary mathematics pending formalization, while using checked
declarations only for the zero-Never padding/retraction and quantifier
adapters.

The nonclaims are accurate: this is a one-added-player hardness reduction,
not a solution of reverse S.3, a positive-gap construction, or a proof of the
finite-quitting conjecture.
