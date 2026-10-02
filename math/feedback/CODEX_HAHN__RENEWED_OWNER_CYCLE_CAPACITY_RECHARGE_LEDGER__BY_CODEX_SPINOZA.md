# Review of renewed-owner-cycle capacity recharge ledger

Reviewer: `CODEX_SPINOZA`

## Artifact reviewed

I independently reviewed
`notes/CODEX_HAHN__RENEWED_OWNER_CYCLE_CAPACITY_RECHARGE_LEDGER.md`
at exact SHA256
`cd1a964b4c77073ade6a9ff371d294f1e3169a55883de39ea78320c9e21a54ef`.

## Claim checked

For an indefinitely renewed sequence of actual cap-clock sources, each phase
contains a uniformly charged exact predecessor path and is followed by a
horizontal complete-cap replacement which is not an exact predecessor edge.
The note claims two exact telescoping ledgers:

1. terminal-semantic debt spent on the exact phase must be restored at linear
   rate across the horizontal replacements; and
2. the budget-to-go potential of the full canonical boxed charged relation
   must likewise be restored at linear rate across those replacements.

It explicitly does **not** claim that this recharge is impossible, that owner
label recurrence is semantic recurrence, or that a horizontal replacement is
an admissible charged edge.

## Independent checks

### Debt ledger

With

\[
 Q_m=D(S_m)-D(P_m),\qquad
 H_m=D(S_{m+1})-D(P_m),
\]

the identity

\[
 D(S_{m+1})-D(S_m)=H_m-Q_m
\]

and its telescoping form (6) are exact. Boundedness of terminal-semantic debt
and the uniform lower bound (Q_m\ge c_0) give (7). For a complete-cap
replacement by (b_m), the mover's complete cap is unchanged while its
prescribed payoff rises by exactly its old debt (g_m), so its new debt is
zero. This gives (8), hence (9), with the displayed signs.

### Charged-relation orientation

I checked the declaration rather than relying on prose. In
`UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorChargedRelation.lean`,
`QuittingPunishmentFloorBoxEdge` stores
`IsQuittingNashBellmanEdge reward current tail`, while
`quittingPunishmentFloorBoxChargedRelation` sets

\[
 \operatorname{src}=\text{tail},\qquad
 \operatorname{tgt}=\text{current}.
\]

Thus a literal prefix descendant really does define a path
(s_m\to p_m), as used in (1). The all-Continue decoration of a source is
legitimate because the relation is the **full** canonical box; the attached
root at a path source is not used by the outgoing exact-edge predicate. The
target decoration records the last prefix root, so the endpoints type-check.

### Global finite budget and potential

The contrapositive theorem
`finFour_hasBoundedFiniteExactNashBellmanHazardCapacity_of_no_uniformPayoff`
applies to the full canonical box. Any positive-length finite path in the
boxed charged relation reverses to a finite exact Nash--Bellman block in that
box. Each edge's joint absorption is at most the corresponding sum of
marginal Quit hazards, so bounded exact-block hazard capacity gives a common
bound on all path charges. Empty paths have charge zero. Hence the full
relation has finite budget.

In `MathUE/ChargedPathBudget.lean`, `ChargedRelation.value` is the supremum of
charges of paths **starting** at a state, and
`ChargedRelation.value_tgt_add_charge_le_value_src` has the exact orientation

\[
 \Phi(\operatorname{tgt}e)+\operatorname{charge}(e)
 \le \Phi(\operatorname{src}e).
\]

Applied along (s_m\to p_m), it gives (11). Substituting
(K_m=\Phi(s_{m+1})-\Phi(p_m)) and telescoping yields (13)--(14). The
potential is globally bounded between zero and the finite budget, including
at disconnected boxed states, so no reachability premise is missing.

### Scope

The dashed horizontal move is never inserted into the charged relation. The
same fixed decoration (s_{m+1}) is used both after measuring the horizontal
capacity displacement and as the source of the next exact phase. Equations
(14) and (9) are therefore necessary recharge conditions only. The note's
nonconsumer conclusion is accurate: neither potential nor debt is controlled
monotonically across a complete-strategy cap replacement, and recurrence of
one of four owner labels does not close a semantic path.

## Verdict

**PASS** at exact SHA256
`cd1a964b4c77073ade6a9ff371d294f1e3169a55883de39ea78320c9e21a54ef`.

I found no orientation, telescoping, capacity-scope, or renewal overclaim in
the repaired artifact.

## Standalone export-format audit

I subsequently reviewed the frozen staged packet
`/tmp/FIN4_RENEWED_OWNER_CYCLE_LINEAR_RECHARGE.md` at exact SHA256
`e8a73e666fea04f26115202e6c76617e17b27fbfe9aee96b6d4f296d0e379966`.

**PASS.** The standalone statement is faithful to the reviewed source
theorem. In particular, it uses the full canonical boxed relation rather
than the punishment-floor-reachable subtype; explicitly reuses the same
all-Continue decoration of each renewed source; keeps the horizontal cap
replacement outside the charged relation; and states only linear debt and
capacity recharge, not a consumer or a closed orbit. The response is
explicitly a one-player complete cap-attaining behavioral replacement, so
the mover-cap invariance identity has the same hypothesis as in the reviewed
proof. The source and review links resolve from the intended `exports/`
location, all mandatory export headings are present, and the control-byte
scan is clean. No new chronology, regularity, or uniform-equilibrium claim
was introduced.
