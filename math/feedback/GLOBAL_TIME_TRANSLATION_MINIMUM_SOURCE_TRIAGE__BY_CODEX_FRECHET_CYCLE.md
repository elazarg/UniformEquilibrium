# Global time-translation variation: source triage

Identity: CODEX_FRECHET_CYCLE.

Status: bounded lookup and operation check stopped at an existing implication.
No new theorem, counterexample, table restriction, or producer is claimed.
The potential-anchor line remains retired.

## Question tested

For a finite quitting game with terminal rewards bounded by M, Never payoff
zero, and independent unrestricted behavioral strategies, write U_i for
prescribed payoff, B_i for the complete behavioral response cap, and
D = sum_i (B_i - U_i). Let D_* be the infimum over all actual product laws.

Could common calendar-translation symmetry of an actual near-minimizer
produce an independently mixed competitor below D_*? Unlike a response-arrow
construction, every proposed comparison here is an actual product of complete
stopping laws. No correlated lottery is installed in play.

The starting idea was the time-gauge discussion in
`../ideas/CONTINUATION_GAME_STATE/NEXT_QUESTIONS.md`, checked against
`../notes/CODEX_RELATIVE__JENSEN_ROW_ATOM_AND_REDUCED_TIME_GAUGE.md`.
The preceding escape-tail lead was discarded: its global changed-tail
functional already has the exact comparison recorded in
`../notes/CODEX_FRECHET_CYCLE__REACHED_ENTRANCE_GLOBAL_TAIL_PUNISHMENT_TEST.md`,
Section 7.

## Exact operation and its stopping point

Let T_k shift every finite stopping time forward k dates and fix Never.
For k > 0, common translation preserves every prescribed payoff, but its
full cap is max(s_i, B_i), where s_i is the own singleton reward. Thus even
common translation preserves the complete semantic pair only when B_i >= s_i
for every i. I granted this favorable condition in the test.

Choose finitely many shifts and independent private weights pi_i. At vertex
a, player i uses T_(a_i) of its original law. Let sigma^a be the resulting
product profile and sigma_bar the product of the privately mixed laws. Put
w(a) = product_i pi_i(a_i) and

    kappa_i = sum_a w(a) B_i(sigma^a) - B_i(sigma_bar) >= 0.

Exact product expansion and full pure-time response extremality give

    D(sigma_bar) - D_*
      = sum_a w(a) [D(sigma^a) - D_*] - sum_i kappa_i.

This is exactly the existing cap-Jensen identity. The diagonal vertices
(all players choosing the same shift) inherit the original debt. Independent
mixing also uses the off-diagonal vertices, which have different relative
clock orders and need not inherit that debt. Global minimality gives only
D(sigma^a) >= D_* at those vertices. It does not give the upper estimate on
their weighted excess needed to beat the nonnegative kappa sum.

Consequently this operation supplies no improved selection inequality from
the currently stated hypotheses. This is not a proof that every global
translation competitor fails: it identifies the exact missing comparison,
which is already the known rectangular-hull excess problem. I did not add a
local regression, assume the cross vertices are minimizing, or interpret an
unattained carrier point as a playable law.

## Evidence and scope

Named source read through the relevant declarations:

- `quittingRootSequenceTerminalSemanticPairAt_silentPrefix_zero` and
  `quittingTerminalPayoff_rootSequence_silentPrefix_eq` in
  `UniformEquilibrium/Diagnostics/Quitting/SilentPrefixTerminalSemantics.lean`.
  They give the payoff-preserving, cap-maximizing effect of one silent row;
  iteration gives the translation statement above.
- Theorem 2.1 and Section 4 of
  `../notes/CODEX_DESCENDANT__MULTICOORDINATE_CAP_JENSEN_ACTIVE_FACE.md`
  give the exact rectangular identity and global-minimum excess inequality.
  Its finite-portfolio extension to arbitrary complete laws is already
  recorded in the earlier owned note cited above. No cap attainment is used.

The Lean declaration was inspected at HEAD
`88709a1034da3738fcb35ca10fc2cea45bad808d`; no fresh build was performed.
The Jensen result is ordinary mathematical evidence here, not a newly checked
Lean declaration. No new unused global mechanism cleared this bounded lookup.
This check is finished; no export or broader impossibility claim follows.
