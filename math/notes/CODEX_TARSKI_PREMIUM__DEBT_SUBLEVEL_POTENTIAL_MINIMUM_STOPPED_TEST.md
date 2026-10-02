# Debt-sublevel potential minimum: stopped global test

Author: CODEX_TARSKI_PREMIUM.

Status: resumed bounded test COMPLETE and stopped. The cap-Nash comparison
does not renew the actual outside source: it reproduces the existing
positive-MAX-minimum all-Continue condition, including its open auxiliary
annotation interval. The exact two-potential accounting is recorded below.
Ordinary mathematics, not independently reviewed or Lean-checked; no new
consumer, table restriction, or export is claimed. The reviewed actual
outside-source note is unchanged.

## Exact invariant-set test

Use the same bounded quitting table and universal exact-root potential H
as in
[the reviewed actual outside-source note](../notes/CODEX_TARSKI_PREMIUM__ACTUAL_OUTSIDE_POTENTIAL_MINIMUM_AND_FULL_CAP_CONTRACTION.md).
Let Z be the compact closure of ACTUAL terminal semantic pairs (u,b),
where u is prescribed payoff and b is the vector of complete behavioral
caps. Thus b−u is coordinatewise nonnegative. Prefix invariance of this
carrier is the named production result in
`Quitting/Root/TerminalSemanticPair.lean`; a general point of Z is not
silently declared an actually attained CAP pair.

Fix e≥0 such that the compact sublevel

    Z_e={(u,b)∈Z : max_i(b_i−u_i)≤e}

is nonempty. Minimize H(u) over Z_e, choosing (u,b). If q is ANY exact
root Nash against the prescribed coordinate u, the checked positive-part
debt splice weakly decreases each debt. The prefixed semantic pair is
therefore still in Z_e. Minimality yields

    H(F(q,u))≥H(u),

whereas universal drift gives the reverse difference at least a(q).
Hence every such root has a(q)=0. Finite root Nash existence then gives

    u_i≥s_i for every i,
    EVERY exact payoff-Nash root at u is all Continue.

Thus simply imposing an invariant global regret budget on the H
minimization does not renew the root-active outside source. It selects
a root-inert payoff instead. No strict singleton interior, actual cap
attainment, or good finite-calendar cap representative follows here.

## 2. Same-table source and the exact cap-Nash comparison

On resumption fix one actual Fin4 reward table with |r_i(S)|≤M, Never zero,
and positive global full regret

    m=inf_(actual p) E(p)>0.

The infimum equals the minimum over the compact semantic carrier Z;
an element of that carrier is not declared an attained actual strategy.
The same-table no-UE theorem supplies all-player punishment normality,
and some s_i>0 because otherwise all Never is already exact. The current
polynomial characterization therefore supplies ONE polynomial H and a
positive robust tolerance on K=[−M−2,M+2]^4. In particular its exact-edge
inequality applies at both u and b. This does not replace the table by a
worst table or move to a restricted minimum.

For a root q put c=∏_i(1−q_i), a=1−c and α_i=∏_(j≠i)(1−q_j).
Write A_i for the absorbed Continue contribution, Q_i for the Quit
endpoint, and d_i=b_i−u_i≥0. For the literal prefix pair (u',b'),

    u'=F(q,u),              b'_i=max(Q_i,A_i+α_i b_i).       (1)

If q is exact root Nash at b, then

    b'=F(q,b),       u'=b'−c d,       d'=c d.               (2)

These are exact complete-response statements, including all late deadlines
and Never; no maximizing response is needed. They also extend continuously
to Z and preserve Z_e. Both b and b' belong to [−M,M]^4, so the SAME
universal H genuinely gives

    H(b)−H(b')≥a.                                         (3)

It does NOT give H(u)−H(u')≥a for this cap-Nash root.

Define the signed annotation gap V(u,b)=H(b)−H(u). Equations (2)–(3) yield
the exact accounted inequality

    V(u',b')−V(u,b)≤−a−[H(u')−H(u)].                     (4)

At the H(u)-minimizer from the first section, every finite cap-Nash stack
stays in Z_e. If its successive pairs are (u_k,b_k), telescoping gives

    V(u_N,b_N)≤V(u_0,b_0)−Σ_(k<N)a_k,                    (5)

because H(u_N)≥H(u_0). This is a bounded charge account, not a producer of
any positive charge or an invariant H-minimizing payoff after each step.

## 3. Actual global minimality stops every cap-Nash move

At ANY pair in Z with E=m, (2) gives E'=cm. Since the prefixed pair is in Z,
globality requires m≤cm. As m>0 and c≤1, c=1, hence q is all Continue.
This already proves

    EVERY cap-Nash root at EVERY global MAX minimum is all Continue.  (6)

Thus adding H does not supply a new root to this source. For a cap-Nash
stack from E_0≤e, the same identity gives the already familiar budget

    m Σ_(k<N)a_k≤E_0−E_N≤e−m.                            (7)

This is a MAX statement proved directly by E_(k+1)=c_k E_k and E_k≥m;
the analogous checked SUM chronology theorem is not silently substituted
for it. In particular no fixed positive absorption can survive taking
actual source exploitability down to m.

There is no untested cap/payoff interpolation escape either. For 0≤t≤1,
let v_t=u+t d and take ANY exact Nash root at v_t. Put
G_i(t)=Q_i−A_i−α_i v_(t,i). From the same full-cap formula,

    d'_i=[α_i(1−t)d_i−max(0,G_i(t))]_+ + c t d_i
         ≤[(1−t)α_i+t c]d_i.                             (8)

For 0<t≤1 and a>0, the right factor is at most 1−t a<1. At E=m this
contradicts the global minimum. Thus every such root is all Continue.
This is already contained in the checked MAX auxiliary plateau theorem:
write v_t=b−h with h_i=(1−t)d_i<m. No new interval theorem is claimed.
At t=0, the H(u)-minimization in the first section supplies the missing
endpoint's all-Continue conclusion. Positive gap, same table, full caps,
and the same H have all been retained; nevertheless the proposed family
produces no nonzero root.

## 4. Exact source comparison and decision

Declarations inspected on resumption:

- `quittingTerminalSemanticCarrier_isCompact`,
  `quittingTerminalSemanticPrefix_mem_carrier`, and
  `quittingTerminalSemanticDebt_prefix_eq_blockAct`,
  `Quitting/Root/TerminalSemanticPair.lean`.
- `quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash`
  and `quittingTerminalSemanticPrefix_envelope_eq_rootSuccessorPayoff_of_capNash`,
  `Quitting/Root/CapNashRootStack.lean`.
- `minimumTerminalSemantic_exploitabilityAuxiliaryNash_eq_allContinue`
  and `minimumTerminalSemantic_exploitabilitySingletonMargin`,
  `Diagnostics/Quitting/TerminalSemanticPlateauDynamicCostate.lean`:
  these are MAX declarations, distinct from the SUM budget files.
- `capNashStack_absorptionBudget_of_nearMinimum`,
  `Diagnostics/Quitting/TerminalCapNashChronology.lean`: explicitly a SUM
  statement; inspected for overlap, not used to infer (7).
- `quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential`,
  `Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`,
  and the literal all-root residual/regret definition in neighboring
  `RobustChargedRelation.lean`.
- `nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff`,
  `Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`,
  and `exists_uniformEquilibriumPayoff_of_zeroSolo`,
  `Quitting/Punishment/ZeroSoloDisjunct.lean`: same-table premises only.

These paths are relative to `UniformEquilibrium/`. The earlier
[same-table polynomial/actual-minimum seam](../notes/CODEX_NOETHER_SUPPORT__SAME_TABLE_POLYNOMIAL_WORD_AND_ACTUAL_MINIMUM_SEAM.md)
already records why a crossing word's annotation cannot simply be matched
to a global-minimum payoff. The
[all-Continue boundary fixed-point note](../ideas/CONTINUATION_GAME_STATE/ALL_CONTINUE_BOUNDARY_FIXED_POINT.md)
already shows that remembering the response graph does not remove the
inert transition. No arbitrary solved-profile counterexample is needed
for the present stop: (6) is forced by the genuine global source itself.

Decision: retire the cap-Nash versus payoff-Nash renewal test. Its exact
full-response accounts are valid, but the universal potential adds only
(4)–(5) to a family already forced to be inert at the positive minimum.
The actual outside-source fiber-separation result remains the proved
boundary; no contradiction or new raw restriction has been obtained.
