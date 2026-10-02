# Whole-packet gate: actual-profile terminal-gap paid-cap trichotomy

Reviewer: `CODEX_RAMSEY`

Date: 2026-08-25

Repository head checked: `a277602c`

Verdict: **ACCEPT**

This is an independent whole-packet audit of
[`ACTUAL_PROFILE_TERMINAL_GAP_PAID_CAP_TRICHOTOMY.md`](../formalized/ACTUAL_PROFILE_TERMINAL_GAP_PAID_CAP_TRICHOTOMY.md)
against every item in [`exports/README.md`](../exports/README.md).  Because the
new extraction is universal over literal behavioral profiles and uses
unrestricted behavioral deviations, I also treated this audit as the second
independent falsification required for an unrestricted-strategy statement.
I found no mathematical, source, adapter, consumer, or scope objection.

The packet should add this gate file to its `Independent mathematical review`
list before external handoff.  That is review bookkeeping, not a mathematical
repair.

## 1. Exact statement and quantifiers

The player type is finite with the standard decidable equality inherited by
the quitting-game API.  The reward table, positive number `gamma`, global
minimum pair, carrier membership, global lower-bound proof, and positive
minimum debt are all explicitly quantified.  The conclusion is correctly
universal in the literal behavioral profile `sigma` and existential in the
observer and two pure stopping times.

The displayed `minimum_mem` hypothesis is stronger than the fields needed to
construct `QuittingPaidCapLiftedSource`; it is harmless and matches the stated
meaning of a supplied global carrier minimum.  The source record itself uses
`minimum_le` and `minimum_pos`, exactly as the proof says.

The prose says the selected port lies in an exhaustive pairwise-disjoint
alternative.  Although the short code display shows the disjunction, the
proof invokes `QuittingPaidCapLiftedSource.exactTrichotomy`, whose return also
contains all three pairwise-disjointness clauses.  There is no logical loss.

## 2. Product-PMF strict-average extraction

At a fixed `sigma`, the definition of `HasTerminalExploitabilityGap` gives an
actual player `j` and unrestricted behavioral replacement `tau` satisfying

```text
U_j(sigma[j<-tau])-U_j(sigma) >= gamma.                (1)
```

The two uses of
`quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime` are exact:
one uses the stopping law of `tau`, and the other uses the stopping law of the
prescribed strategy `sigma(j)`.  Both expectations evaluate the same bounded
function

```text
V(q)=U_j(sigma[j<-pureTime(q)]),  q : Option Nat.      (2)
```

Taking the product PMF therefore gives the exact expected difference in the
packet.  The strict-average argument is sound even for countably supported
laws.  If every positive-mass product atom had difference below `gamma`, the
deficit would be nonnegative on the whole support and strictly positive on at
least one positive-mass atom.  Its expectation would be strictly positive,
contradicting (1).  No uniform atomwise margin, maximum attainment, or finite
cutoff is used.

The conclusion retains the full weak constant `gamma`, not `gamma-eta`.
Since `gamma>0`, the selected pure times differ.  Each can independently be
date zero, a later finite time, or `none` (Never).

## 3. Paid-row decoder and source construction

The hypotheses of
`exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub` match exactly:
positive gain and a weak pure-time payoff difference on the literal receiving
profile `sigma`.  The decoder does not require the prescribed strategy itself
to equal the selected source atom.  The packet states this distinction.

The returned row, supplied minimum, minimum lower bound, and positive minimum
debt fill every field of `QuittingPaidCapLiftedSource` with
`source.profile=sigma` and `source.gain=gamma`.  Then
`nonempty_summablePort` and `exactTrichotomy` apply without a floor,
stationarity, finite-support, or best-response-attainment hypothesis.

Thus the actual-data provenance is literal: no semantic carrier point is
re-realized as another profile and no observer is preselected.

## 4. Quantitative branch and minimum-fiber boundary

The packet uses the current checked formula with the correct source/minimum
roles:

```text
D_sigma-D_infinity >= D_* rho/(2R),                   (3)
```

where `R=quittingRewardBound reward`.  It does not repeat the earlier invalid
off-minimum replacement of `D_sigma` by `D_*`.  In a positive displacement
branch the checked structure also proves `R>0`, so the denominator is legal.

If `D_sigma=D_*`, (3) contradicts global minimality of the port limit.  The
charged branch contains a uniform-equilibrium payoff and contradicts the
same positive terminal-gap witness by the checked exploitability theorem.
Hence only the inert branch remains on the minimum fiber, as claimed.

## 5. Probability and unrestricted-deviation audit

- Complete behavioral strategies are represented only through their exact
  stopping-law PMFs on `Option Nat`.
- The expectation identity is against fixed opponents and is valid for every
  unrestricted behavioral replacement.
- Randomized and diffuse finite-time laws are included; no public randomizer
  or stationarity is assumed.
- `none` is literal Never on both laws.
- The paid-row decoder records the actual first temporal disagreement and
  does not replace an infinite law by a finite horizon.

This fully matches the packet's probability, information, and agency section.

## 6. Boundary and falsification tests

I checked the following exact boundaries.

1. For two point masses the product argument reduces to their literal value
   difference, including equality at `gamma`.
2. A sequence of pure values increasing to a supremum shows why selecting a
   near-maximizing atom from the profitable law alone can lose an error; the
   product-law proof avoids that invalid step.
3. If either law is concentrated at Never, the same proof and decoder remain
   typed.
4. At `gamma=0`, the selected atoms may coincide and no positive paid-row
   record follows, so the strict hypothesis is necessary.
5. A positive paid row and an inert all-Continue cap selector are compatible:
   the former compares prescribed-profile pure times, while the latter is
   Nash against the cap annotation.  The packet makes no surcharge
   identification.

No counterexample was found.

## 7. Source, novelty, adapter, and consumer

The cited declarations and files are current at the checked head:

- `HasTerminalExploitabilityGap` and its no-uniform-payoff consequence;
- the exact behavioral stopping-law expectation identity;
- the paid first-disagreement decoder;
- `QuittingPaidCapLiftedSource.nonempty_summablePort`; and
- `QuittingPaidCapLiftedSource.exactTrichotomy`.

A narrow search of `UniformEquilibrium/` found uses of the expectation
identity and several specialized paid-row producers, but no checked theorem
performing this full-gap two-law extraction at an arbitrary literal profile.
The result is therefore not a weakened restatement.

The packet makes a strict named change to
`questions/PAID_ADMISSIBLE_PAYOFF_NEAR_RETURN.md`: every actual endpoint now
enters the checked paid-cap trichotomy, eliminating separate paid-row source
production for the Fin5 deletion alternatives.  The charged arm has the
checked cumulative near-return consumer, the displacement arm has (3), and
the inert arm is honestly retained as the remaining obstruction.

## 8. Lean handoff and nonclaims

The proposed handoff is narrow and noncircular: first prove a bounded
product-PMF strict-average lemma and the paid-row extraction, then wrap the
already checked source/port/trichotomy declarations.  It does not propose a
structure field that assumes the result.

All important nonclaims are present: no prescribed-payoff floor Bellman edge,
no restart, no well-founded iteration, no inert-stall elimination, no role
alignment, and no proof of the conjecture.

Accordingly the packet passes the mathematical and export-quality gate.
