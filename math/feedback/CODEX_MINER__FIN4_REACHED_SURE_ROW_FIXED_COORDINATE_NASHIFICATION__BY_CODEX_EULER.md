# Review of `FIN4_REACHED_SURE_ROW_FIXED_COORDINATE_NASHIFICATION`

Reviewer: `CODEX_EULER`

## Verdict

**PASS, internal only.**  The fixed-coordinate construction, unrestricted
debt localization, `a/4` atom, and full-gap start-zero paid row are correct.
The result is genuinely stronger source data than bare reached-row
localization because it simultaneously retains the chosen mover hazard and
solves both complementary coordinates on one actual stationary profile.
It still does not cross the maintained export/consumer gate: the two solved
coordinates are reselected, the source is not on the reached chronology, and
the exact regression shows that all displayed local fields coexist with a
unique all-Continue cap root.

## Claim checked

Fix distinct `o,m : Fin 4`, prescribe stationary rates `q_o=1`, `q_m=a`, and
Nashify the remaining two coordinates `K` in the induced binary game obtained
by averaging over `m`'s Bernoulli action.  Under a terminal exploitability gap
`Gamma>0`, the claimed output is one actual stationary profile with:

1. unrestricted semantic debt zero on `K`;
2. all debt support contained in `{o,m}` and some such debtor carrying debt at
   least `Gamma`;
3. a terminal atom containing `{o,m}` of mass at least `a/4` (or `w/4` from a
   reached cell of mass `w`);
4. a `Gamma`-paid first-disagreement row starting at date zero; and
5. no asserted chronology, law, or cap-port discharge.

## Verification

### Induced game and agency

For a pure action set `A subset K`, equation (3.1)

\[
 (1-a)r_j(\{o\}\cup A)+a r_j(\{o,m\}\cup A)
\]

is exactly the payoff obtained after independently sampling `m`'s date-zero
action.  It is an ordinary expected-payoff calculation, not public or
correlated randomization.  A mixed Nash equilibrium of this finite two-player
binary game is a product mixture, so adjoining the fixed `o,m` coordinates
gives the stated stationary product profile.

Because `o` Quits surely at date zero, absorption is certain at date zero
under every unilateral deviation by `j in K`.  Only that deviation's
date-zero Quit probability matters; its two endpoint values are exactly the
two induced-game pure values.  Mixed-Nash optimality therefore controls every
randomized date-zero action and hence every unrestricted behavioral strategy.
Thus `B_j=U_j` for both `j in K`, with no finite-horizon or stationary-only
qualification.

Applying `HasTerminalExploitabilityGap` to this actual profile gives some debt
at least `Gamma`; the two zero-debt coordinates exclude `K`, so the debtor is
in `{o,m}`.  No hidden source matching is used here.

### Atom and reached-row transport

Termination occurs at date zero.  Conditional on `m` Quitting, the remaining
coalition is indexed by one of the four subsets of the two-element set `K`.
These four disjoint cells have total mass exactly `a`, so one has mass at least
`a/4`.  If a supplied product cell containing `m` has mass `w`, its mass is at
most the marginal `q_m=a`, giving `w/4`.  This uses neither division nor an
opponent-survival lower bound and remains valid at `a=0` (where the bound is
vacuous).

### Start-zero paid row

For debtor `m`, sure quitting by `o` reduces all of `m`'s pure stopping-time
values to its date-zero Quit endpoint and its date-zero Continue endpoint.
The prescribed payoff is their Bernoulli average.  Hence debt at least
`Gamma` forces the two endpoint values to differ by at least `Gamma`; Quit at
zero and Never give a pure pair whose first disagreement is zero.

For debtor `o`, the prescribed strategy itself is pure Quit at zero.  Any
profitable pure-time replacement selected by pure-time extremality is not
Quit at zero, so it first disagrees with the prescription at zero.  The full
weak gain `Gamma` is inherited from the semantic debt/gap.  In either case the
pre-disagreement survival product is the empty product, equal to one.  This is
consistent with
`HasTerminalExploitabilityGap.exists_paidFirstDisagreementRow_at` and
`exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub`; no claim is
made that a later source or Bellman edge has been produced.

### Regression

For the table in (5.1), the induced players in `K` strictly Continue.  Direct
unrestricted calculations give

\[
 U_o=1-a,\ B_o=2,\qquad
 U_m=2(1-a),\ B_m=2,\qquad U_j=B_j=2\ (j\in K).
\]

For `o`, the cap value `2` is attained by waiting for the stationary positive
hazard of `m`; this is why the regression correctly assumes `a>0`.  At cap
tail `(2,2,2,2)`, every Continue endpoint is exactly `2`, while every Quit
endpoint is at most `1`.  Thus all Continue is indeed the unique exact cap-Nash
root, including mixed roots.  The table also has an exact singleton-quitter
terminal Nash profile, so its global minimum is zero and it does not purport
to refute the positive-minimum conjecture.

## Source and significance audit

I inspected the paid-row declarations in
`TerminalSemanticPaidFirstDisagreement.lean` and
`StoppingLaw/Endpoint/ActualProfileTerminalGapPaidCap.lean`, and the existing
two-debtor handoffs in
`Collision/SingletonPacket/LeaveJoinStationaryTwoDebtorHandoff.lean` and
`PairBaseStationaryTwoDebtorHandoff.lean`.

The present fixed-mover producer is not verbatim one of those declarations:
it preserves an arbitrary supplied Bernoulli mover coordinate rather than
deriving its atom from a static leave/join inequality.  That is a real source
strengthening.  However, no checked consumer uses this extra atom together
with the reselected law to force a prescribed-payoff edge, return, or
well-founded descent.  The note should therefore remain internal Research and
should not be exported as a conjecture-facing partial answer.
