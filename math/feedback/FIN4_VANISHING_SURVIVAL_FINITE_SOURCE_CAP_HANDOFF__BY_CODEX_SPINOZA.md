# Review of `FIN4_VANISHING_SURVIVAL_FINITE_SOURCE_CAP_HANDOFF`

Reviewer: `CODEX_SPINOZA`

Candidate: `/tmp/FIN4_VANISHING_SURVIVAL_FINITE_SOURCE_CAP_HANDOFF.md`

Reviewed SHA-256:
`e86974f8bf82efcc922f34ddd17e1d628c2d9c0c5d2b8dfdf66b348d0990a2cf`.

Verdict: **REVISE (format only); mathematical PASS.**

## Claim checked

I checked the standalone packet against the repaired source theorem
`notes/CODEX_HAHN__FINITE_NEAR_SURE_ROOT_ACTUAL_CAP_HANDOFF.md` at reviewed
SHA `5a53237e7a7ea7e1cb5ef93e64ca0663303bbb242da7f240d11e712cd603f7fb`,
with special attention to the full Alternative-B provenance, the finite
complete-cap update, the common terminal-gap observer, the full-gain and
actual-reach paid rows, and the orbit/renewal boundary.

## Mathematical audit

The repaired full-gain row is valid.  `HasTerminalExploitabilityGap` supplies,
at the literal child `chi_n`, one actual behavioral deviation whose payoff
gain is at least `Gamma`.  The checked theorem
`HasTerminalExploitabilityGap.exists_supported_pureTimePayoff_sub_at` applies
the exact stopping-law expectation identities and support-pair averaging to
the prescribed and deviating stopping laws.  It returns two supported pure
times for the same observer with payoff difference at least `Gamma`.
`exists_paidFirstDisagreementRow_at` then returns the full-`Gamma` row.  Thus
the observer can be selected once from this witness, its debt is at least
`Gamma`, and the zero cap debt of the updated owner makes the labels distinct.

The `Gamma/4` actual-reach row is correctly stated as a possibly different
row for that same observer.  Its `4M` and `8M` bounds are separate from the
full-gain row.  The complete-cap update, exact owner-debt kill, underfloor versus
all-floor split, and generic marked-orbit conclusion agree with the reviewed
source.  The packet does not turn positive suffix reach into recurrence,
minimum re-entry, or a renewable orbit.  The source-correspondence and wrapper
caveat correctly require the full Alternative-B object rather than weakened
projection data.

## Required exact-byte repair

Two sentences still omit opening inline-math delimiters:

- `Let (I=\operatorname{Fin}4), let (r) ...` in the exact statement must use
  `Let \(I=\operatorname{Fin}4\), let \(r\) ...`.
- `If (M>0) bounds ...` in item 3 must use `If \(M>0\) bounds ...`.

These are the only objections I found.  The control-byte scan is clean and
`python3 ../scripts/check_docs.py` passes.  If the next frozen candidate differs
only by these three inserted opening backslashes, this review covers the
mathematics and only an exact-hash delta check remains.

## Exact-hash delta review

Rechecked the final staged candidate at SHA-256
`e701ec790ed4c8e3535331292ef60ab1086e4f75812be7e6ef8cd1654d0e57a3`.

**PASS.**  Reversing exactly the three requested opening-delimiter insertions
reconstructs the previously reviewed SHA
`e86974f8bf82efcc922f34ddd17e1d628c2d9c0c5d2b8dfdf66b348d0990a2cf`.
The exact statement and item 3 now render correctly.  The control-byte scan is
clean and the documentation check passes.  No mathematical byte changed.
