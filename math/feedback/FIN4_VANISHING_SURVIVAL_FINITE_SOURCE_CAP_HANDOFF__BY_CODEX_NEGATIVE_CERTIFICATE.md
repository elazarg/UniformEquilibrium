# Review of `FIN4_VANISHING_SURVIVAL_FINITE_SOURCE_CAP_HANDOFF`

Reviewer: `CODEX_NEGATIVE_CERTIFICATE`

Reviewed staged file:
`/tmp/FIN4_VANISHING_SURVIVAL_FINITE_SOURCE_CAP_HANDOFF.md`

Reviewed SHA-256:
`89ab7a812da14c80bf14512804dbca66d24fea905e5276d35dab3b1f62a7942e`

## Verdict

**FAIL at this exact hash for one proof sentence; the theorem and all other
composition steps remain PASS.** The paid-row proof presently appeals to a
pure-time response which “can approximate the cap closely enough to retain
the full weak inequality at scale \(\Gamma\).” That inference is false when
the complete cap debt is exactly \(\Gamma\) and its supremum is not attained:
cap approximation yields only a gap arbitrarily close to \(\Gamma\), not a
weak gap at least \(\Gamma\).

The exact repair is already identified elsewhere in the same paragraph and
in the Lean handoff. Select the actual behavioral deviation supplied by the
terminal exploitability witness at \(\chi_n\); its payoff gain is weakly at
least \(\Gamma\). Write that deviation payoff and the prescribed payoff as
expectations of the same pure-time payoff function under their two stopping
laws. The support-pair averaging argument then gives source and receiving
atoms with difference weakly at least the difference of those expectations,
hence at least \(\Gamma\). Apply
`exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub` to this pair.
This retains the same observer \(j_n\) and needs no cap attainment or cap
approximation for \(j_n\).

Replace only the two sentences beginning “Choose the behavioral witness” and
ending “at scale \(\Gamma\)” by that exact argument. The following sentence
about repeating the expectation proof is then redundant or may remain as a
summary. A delta-only recheck will suffice.

## Remaining exact-hash audit

Subject to that correction, I verified:

- the full Alternative-B boundary, stationary-tail cap attainment, and
  literal finite ancestry;
- unchanged unrestricted cap under own-strategy replacement, exact owner
  gain, and exact killed owner debt;
- selection of a distinct debtor \(j_n\ne k\);
- the separate actual-reach row of gain \(\Gamma/4\), with the exact \(4M\)
  and \(8M\) inequalities and source-support field;
- the all-player floor versus a displayed underfloor player distinct from
  \(k\);
- the generic marked exact orbit at the literal child, arbitrary-orbit
  absorption summability, semantic-port convergence, and positive orbit-wise
  suffix reach;
- the absence of any uniform-in-\(n\) reach bound, return, renewal, or uniform-
  payoff claim; and
- the \(4M\alpha_n\) approximate singleton-base calculation.

All mandatory export headings are present. The control-byte scan is clean,
and all five relative links resolve from the intended `exports/` location.
The paid-row Lean handoff correctly warns that the existing convenience
declaration existentially chooses its observer and requests a wrapper which
retains the terminal behavioral witness, supported pure-time pair, and both
rows for the same label.

## Delta review of the repaired candidate

Rechecked exact SHA-256
`e86974f8bf82efcc922f34ddd17e1d628c2d9c0c5d2b8dfdf66b348d0990a2cf`.

**PASS.** The repaired paragraph now selects the actual behavioral deviation
returned by terminal exploitability, writes both behavioral payoffs as
expectations under their stopping-time laws, and applies support-pair
averaging to retain the full weak \(\Gamma\) inequality for the same
observer. It explicitly disclaims cap approximation and cap attainment for
that observer. This is exactly the required repair.

The surrounding theorem, source provenance, separate \(\Gamma/4\) actual-
reach row, floor-safe marked-orbit consequence, and nonclaims are unchanged
in mathematical content. The control scan remains clean. I have no remaining
objection to promotion at this hash.
