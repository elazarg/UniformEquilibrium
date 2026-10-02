# Independent audit of `AKRS_REVERSE.md`

Reviewer: `CODEX_SNELL`

Date: 2026-09-03

## Verdict

**PASS after one wording correction.**  The null-tail lemma and the
one-added-player quantitative hardness reduction are mathematically valid
under the definitions in
`questions/AKRS_THEOREM_3_4_REVERSE_S3_NULL_TAIL_GAP.md`.  Equations
(18)--(21) genuinely cover arbitrary behavioral profiles and deviations.
The stationary padded row is exactly row-perfect, including the unused pure
Continue endpoint of the dummy.  Equations (22)--(24) have the stated
one-player cardinality shift.

The phrase “exactly one” in Corollary 2 is not justified and is generally
false: the two displayed conclusions can hold simultaneously.  Replace it by
“at least one” (or simply “either”).  This does not affect the null-tail
disjunction or any later reduction.

I did not infer reverse S.3 and do not classify it as proved or false.  The
audited result is only that its universal theorem schema is at least as hard
as general approximate-equilibrium existence, together with the valid
null-tail cleanup.

## 1. Null-tail lemma

The proof of Lemma 1 is correct.

If `a_(m,infinity)>0` while `a_(0,infinity)=0`, then the finite prefix through
`m` contains a zero factor.  Since every factor from `m` onward is positive,
there is a last zero `L<m`, and

\[
 P=\prod_{t=L+1}^{\infty}c(q_t)>0.
\]

For `n>L`, dividing the fixed positive product `P` by its finite prefix gives
`a_(n,infinity)->1`.  The bound `a_(n,infinity)<=c(q_n)` then gives
`c(q_n)->1`, and `q_n^j<=1-c(q_n)` gives every coordinate `q_n^j->0`.
The restarted-tail terminal mass is exactly `1-a_(n,infinity)`, so (11)
follows with the displayed finite reward bound.  The finite opponent row then
converges to all Continue, proving (12).  Passing to the limit in the first
row-perfectness inequality proves (8).

The subsequent logical conclusion is a disjunction, not an exclusive
dichotomy.  If non-every-tail witnesses occur at errors tending to zero,
Lemma 1 makes all Continue an exact equilibrium.  Otherwise there is a small
error threshold below which every available initially absorbing row-perfect
witness is every-tail terminating.  But a game may have both an all-Continue
equilibrium and every-tail witnesses, so “exactly one” must be weakened.

## 2. Exact padded row, including the unused endpoint

At the stationary row (15), every old player Continues and the dummy `d`
Quits surely.  The restarted-tail payoffs are `H_i` for old players and `-P`
for `d`.

For an old player `i`, pure Continue produces the dummy-only coalition and
has value `H_i`; pure Quit produces `{i,d}`, whose old-player projection is
`{i}`, and has value `r^i({i})<=H_i`.  Since Continue is prescribed,
`V_i=C_i=H_i`; all four conditions in (5) hold at error zero.

For the dummy, pure Quit has value `-P`.  Crucially, the unused pure Continue
endpoint also has value `-P`, not zero: all old players Continue in the
current row, after which the prescribed restarted tail makes the dummy Quit
surely in its first row.  Thus `Q_d=C_d=V_d=-P`.  The no-profitable-pure-action
condition in (5) does test this unused Continue endpoint, and it passes
exactly.  Every restarted tail terminates immediately.  Proposition 3 is
therefore correct.

## 3. Arbitrary behavioral coupling in (18)--(21)

The coupling is valid for arbitrary behavioral profiles as defined in the
self-contained question.  Each strategy is a sequence of live-date Quit
probabilities, so the old players' random actions can be sampled
counterfactually after a dummy-only padded termination and used to define the
projected play.

Outside a dummy-only first terminal coalition, the first old quitting
coalition and every old player's reward agree pathwise in the two games.  On
a dummy-only padded terminal, the padded old payoff is `H_i`, while the
counterfactually continued projected payoff is one of the old terminal
rewards or `z^i`, hence lies in `[L_i,H_i]`.  This proves both sides of (18).

For an arbitrary deviation `tau_i`, the probability of dummy-only
termination need not equal the prescribed `alpha`; this causes no problem.
The same pathwise comparison gives only the one-sided inequality (19), which
is exactly what the proof uses.  The prescribed dummy payoff is `-P alpha`,
and its deviation to Continue forever gives exactly zero, so
`P alpha<=E_hat`.  Combining these facts proves (20).  Since `P>0`, `W>=0`,
and exploitability is nonnegative, rearrangement gives (21) with the correct
factor `P/(P+W)`.

This agrees with the checked canonical-padding direction in
`UniformEquilibrium/Quitting/Terminal/PassivePlayerPaddingExploitabilityRetraction.lean`,
notably
`retractionFactor_mul_quittingTerminalExploitability_project_le`; the present
audit, however, relies on the self-contained coupling above rather than
assigning a Lean seal to the note's arbitrary-`z` formulation.

## 4. Quantifiers and cardinality in (22)--(24)

For every nonempty `n`-player game, the construction produces an
`(n+1)`-player game with one stationary exact every-tail S.3 witness.  A
theorem R-S.3 for **all `(n+1)`-player games** therefore gives arbitrarily
small padded exploitability; (20) retracts it to arbitrary prescribed error
in the original `n`-player game.  The zero-player case is vacuous and should
be handled separately if (22) is stated for all natural `n`.

The universal equivalence (23) is correct only because its quantifier ranges
over every finite cardinality.  At fixed cardinality there is a real shift:
R-S.3 for Fin4 directly yields general approximate-equilibrium existence for
Fin3, not for Fin4.  Likewise (24) transports an `n`-player positive
exploitability floor to an `(n+1)`-player S.3 game, scaled by
`P/(P+W)`; it is not a same-cardinality transport.

Subject to this explicit reading, (22)--(24) are correct.  In particular, if
an original game has `E_G(sigma)>=gamma` for every behavioral profile, (21)
applies pointwise to every padded behavioral profile and proves (24).  This
does not construct a counterexample; it says that any future general
counterexample would lift to an exact-every-tail-S.3 counterexample after one
player is added.

## 5. Required correction and scope

Required textual correction:

```text
Corollary 2: “exactly one of the following holds”
           -> “at least one of the following holds”.
```

Recommended cardinality reminder near (23): the equivalence is universal
over all finite player sets; no fixed-cardinality equivalence is claimed.

With that correction, the claimed null-tail lemma and hardness reduction
pass this independent falsification audit.  They do not prove the reverse
S.3 implication itself.

## 6. Delta audit of the assembled candidate

Candidate:
`notes/CODEX_NEGATIVE_CERTIFICATE__AKRS_REVERSE_S3_NULL_TAIL_AND_HARDNESS.md`

SHA-256:
`65e8358f8d2a81dc15278515d388ecedf5b1f1aa6caad36dc3f529f97b62ee71`

**PASS.**  The candidate applies every correction required above and does
not strengthen the mathematical conclusion.  In particular:

- the null-tail alternative now says “at least one” and explicitly allows
  both arms;
- the exact statement and proof preserve the one-player cardinal shift and
  expressly deny a same-cardinality equivalence;
- the one-dummy stationary row checks the unused Continue endpoint as
  `C_d=-P`, so its row perfection is exact;
- the retraction proof still couples arbitrary live-date behavioral laws,
  continues old randomizations counterfactually after dummy-only absorption,
  allows the dummy-only probability to change under an old-player deviation,
  and uses only the required one-sided deviating-payoff inequality; and
- the source correspondence now states the zero-Never normalization,
  `J=PUnit` specialization, small-error adapter, and current Literature
  status accurately.  It cites the tracked publisher update only for the
  affiliation change and makes no claim of a mathematical erratum.

The candidate adds presentation, boundary tests, adapters, and a Lean
handoff, but no new reverse-S.3, counterexample, or same-cardinality claim.
The arbitrary-`z` padding and dummy-sure-Quit producer remain correctly
labelled ordinary mathematics pending formalization; the named existing Lean
declarations are used only at their checked scopes.  This hash is therefore
covered by my original PASS-with-correction review.
