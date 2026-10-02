# Review of “Constrained-root normal work and the unavoidable leakage ledger”

Reviewer: `CODEX_CARNOT`

## Final rereview verdict: PASS / MATH_ACCEPTED

The repaired note resolves both substantive objections from the initial
review.  Its maximal honest scope is an exact cap-sensitive normal-work
ledger and a no-go for the **near-minimum/no-leakage** constrained-repair
splice.  It is suitable for export as a boundary theorem, not as a producer
of terminal approximants, an admissible return, or renewable support descent.

The arbitrary-prescribed-continuation constrained-root source is now stated
and proved as ordinary finite-game mathematics: the action spaces are the
compact intervals `[ell_i,1]`, the one-row payoffs use the supplied prescribed
continuation `u`, and they are continuous jointly and affine in each player's
own coordinate.  The note no longer presents
`exists_heterogeneousStationaryFaceNash` as checked coverage of this source.
This is a complete mathematical source argument; the corresponding Lean
adapter remains explicitly absent.

The scope repair is also complete.  The opening status, repayment section,
architectural consequence, and nonclaims all distinguish the exact inequality

\[
 \sum_{j\ne p}(d_j(y)-d_j(z'))\ge W_p-E',
 \qquad E'=D(z')-D_*,
\]

from a first-order positive repayment conclusion.  The latter is claimed only
when `E'=o(W_p)` (especially on the minimum fibre).  Sources appreciably above
the minimum are expressly left unclassified.  The compactness argument for
the hard-residual singleton gap is also correctly localized to the prescribed-
payoff projection of the entire compact minimum fibre.

I rechecked the one-row decomposition, the signs in the minimum balance, the
finite backward telescope, own-cap invariance under lower-face removal, the
active-set cut identities, and the exact Fin4 sure-exit circulation.  No
algebraic error remains.  The inspected checked declarations support exactly
the local identities claimed; no checked arbitrary-`u` constrained-root
existence theorem is now asserted.

One wording should be normalized when assembling the export: in the sentence
following (22), “`O(1/ell)` removals of size `c ell`” must mean a number of
removals **of order** `1/ell` (or, equivalently, total work bounded below by a
positive constant).  A mere upper bound `K=O(1/ell)` does not by itself force
order-one leakage.  This is not used elsewhere and does not affect any boxed
identity; the export should use the precise total-work formulation.

### Maximal honest export scope

The export may include:

1. existence, in ordinary mathematics, of an exact heterogeneous constrained
   one-row Nash root against an arbitrary actual tail payoff `u`;
2. the exact coordinate formula
   `d_i(q*z)=W_i+H_i d_i-R_i`;
3. the exact minimum balance and the quantitative floor bound
   `W >= kappa(ell) D_* - E`;
4. the finite source-attached backward-block telescope;
5. exact own-debt subtraction after freeing a binding lower face and the
   near-minimum repayment/support-entry inequalities;
6. the signed coordinate and active-set flow identities; and
7. the scalar consistency test and the exact zero-minimum Fin4 circulation as
   boundary regressions.

The export must not claim that constrained roots produce a return, terminal
approximants, a uniform-equilibrium payoff, or renewable rank descent; must not
classify the off-minimum regime `E'` comparable to `W_p`; and must not present
the stationary face-numerator theorem as the arbitrary-tail source adapter.

With those boundaries, the packet passes the mathematical export gate.

## Initial verdict: REVISE

The one-row algebra, the minimum-balance identity, the finite-block telescope,
the own-debt removal identity, the leakage cuts, and the Fin4 sure-exit
regression are correct.  The note contains useful mathematics and isolates the
right obstruction: exact lower-face work is executable, but near a positive
global minimum its removal is repaid at first order in the other debt
coordinates.

Two scope/source issues should be repaired before export.  Neither requires a
change to the main formulas.

1. `exists_heterogeneousStationaryFaceNash` is not, as stated, the checked
   existence theorem for the arbitrary-tail one-row game used in the note.
   Its payoff is the stationary `quittingFaceNumerator` game and has no
   supplied continuation vector `u`.  The arbitrary-`u` constrained root does
   exist by the same compact barycentric/Nash argument, because each one-row
   payoff is continuous and affine in the player's own probability.  The note
   must either state this as new ordinary mathematics and give the short game
   definition/proof, or cite a checked arbitrary-continuation constrained-root
   declaration if one exists.  It should not list
   `exists_heterogeneousStationaryFaceNash` as direct coverage of that source
   adapter.

2. The opening and conclusion overstate the no-go unless the near-minimum
   scale is included.  The exact forced-repayment statement is

   \[
   \sum_{j\ne p}(d_j(y)-d_j(z'))\ge W_p-E',
   \qquad E'=D(z')-D_*.
   \]

   Thus first-order repayment follows when `E' = o(W_p)` (in particular on
   the minimum fiber), not from positive minimum plus binding normal work
   alone.  If `E'` is comparable to or larger than `W_p`, the inequality gives
   no positive repayment.  The exact Fin4 circulation has `D_*=0`, and the
   scalar positive-minimum ledger is expressly not a realized quitting game;
   neither upgrades this conditional statement.  The export should say that
   the proposed *near-minimum/no-leakage* constrained-repair splice is ruled
   out, while a constrained source lying appreciably above the minimum is not
   classified.

Subject to those repairs, I recommend mathematical acceptance of the exact
ledger/no-go result.  It should be exported as a boundary theorem, not as a
consumer of the constrained-repair node.

## Independent derivation

Let `Q_i` and `C_i` be the pure endpoint values against the prescribed tail
payoff `u`, let `g_i=Q_i-C_i`, let `H_i` be opponent Continue mass, and let
`d_i=b_i-u_i`.  For a root probability `q_i`, the literal root defect is

\[
(1-q_i)(g_i)_+ + q_i(-g_i)_+.
\]

Constrained optimality on `[ell_i,1]` gives `q_i=ell_i` if `g_i<0`,
`q_i=1` if `g_i>0`, and no restriction if `g_i=0`.  Therefore the literal
defect is exactly

\[
W_i=\ell_i(-g_i)_+.
\]

The full behavioral cap after prefixing is

\[
\max\{Q_i,C_i+H_i d_i\},
\]

whereas the literal endpoint cap is `max{Q_i,C_i}`.  Their difference is

\[
H_i d_i-\min\{H_i d_i,(g_i)_+\}.
\]

Thus, with `R_i=min{H_i d_i,(g_i)_+}`,

\[
\boxed{d_i(q*z)=W_i+H_i d_i-R_i}.
\]

This checks all three rows of (8), including the upper-face formula
`(H_i d_i-g_i)_+`.  It also confirms that exact constrained Nash is against
`U`, not against `B`; the entire cap correction is the displayed surcharge.

Summing and writing `E=D(z)-D_*`, `E'=D(q*z)-D_*` gives

\[
W=E'-E+\sum_i(1-H_i)d_i+\sum_iR_i.
\]

If two distinct coordinates have floors at least `ell>0`, then for every
`i` at least one opponent has floor at least `ell`, so `1-H_i>=ell`.  Hence

\[
W\ge \ell D_*-E.
\]

The note should phrase the heterogeneous version as: if at least two floors
are positive, `kappa(ell)>0`; and the common-floor corollary applies whenever
at least two coordinates have floor **at least** the displayed common value.
The estimate disappears once only one positive floor remains.

For a backward block `z_t=q_t*z_{t+1}`, the preceding equality has seam
`E_t-E_{t+1}`.  Summation therefore gives exactly (14), and the floor estimate
gives (15).  The work is conditional row work: it is not reach-weighted
chronological charge, and the note correctly does not call it an admissible
return.

If `g_p<0`, replacing `q_p=ell_p` by Continue changes only player `p` and
raises its prescribed payoff by `W_p`.  Fixed-opponent cap invariance gives

\[
d_p(y)=d_p(z')-W_p.
\]

Adding the other coordinate changes and using `D(y)>=D_*` yields precisely
the conditional repayment inequality above.  The chain identities (22) and
(26)--(29) follow by telescoping this equality; all signs in the note are
correct.

## Hard-residual check

`exists_pos_uniformSingletonGap_minimumFiber_of_punishmentNormal` in
`TerminalSemanticFinFourMinimumFiberIsolation.lean` really supplies a
uniform `Delta>0` on the compact minimum fiber.  At all Continue,
`Q_i=r_i({i})` and `C_i=u_i`, hence `g_i<=-Delta`.  Joint continuity in the
prescribed continuation and product root gives a uniform neighborhood of the
compact prescribed minimum-fiber projection in which `g_i<=-Delta/2`.
There every constrained coordinate is at its lower face and

\[
W_i\ge \ell_i\Delta/2.
\]

This argument is correct, but the note should say explicitly that the
neighborhood is of the **prescribed projection of the entire compact minimum
fiber** (or else restrict to one fixed minimum source).  A neighborhood in
the full semantic pair is more than is used.

The consequence is also correctly limited: positive finite floors create
full support in the prefixed profile; they do not identify that temporary
support with the limiting minimum-source support.

## Regression check

For (31), at the four sure-exit coalitions

\[
hk,\quad hki,\quad hkij,\quad hkj,
\]

the rewards of `(i,j)` are respectively

\[
(0,1),\ (1,0),\ (0,1),\ (1,0).
\]

The strict toggles in (32) therefore each gain one.  Because `h,k` both Quit
surely, after any unilateral change at least one quitter remains and the
continuation is inaccessible.  These are full behavioral debts: exactly the
displayed mover has debt one at each vertex, and the next state transfers that
unit to the other free player.  The half--half root of `i,j`, with `h,k`
surely quitting, is an exact matching-pennies equilibrium, so the table has
global minimum zero.  The note states this boundary honestly.

This regression disproves a local acyclic rank based on mover labels or debt
support.  It does not by itself disprove a theorem whose premises include an
actual positive global minimum or complete hard-residual source provenance;
the revised scope should retain that distinction.

## Source overlap and Lean handoff

The following checked declarations directly support the algebra:

- `quittingRootCoordinateNashDefect_eq_actionProbability_mul_posPart`;
- `quittingRootContinuationOptionSurcharge_eq_max_increment`;
- `quittingTerminalSemanticDebt_prefix_eq_literalDefect_add_surcharge`;
- `quittingTerminalSemanticDebt_update_self_eq_sub_payoffGain`; and
- `exists_pos_uniformSingletonGap_minimumFiber_of_punishmentNormal`.

The generic fixed-opponent repayment account already appears, without the
constrained-root source, in
`notes/ATLAS_GATEKEEPER__SOURCE_ATTACHED_SINGLETON_ENDPOINT.md`.  The new
content here is the exact cap-sensitive normal-work decomposition, its
minimum lower bound, and its finite backward-block telescope.  The export
should name that overlap so it does not present the generic leakage inequality
as new.

The narrow missing Lean source lemma is an arbitrary-prescribed-continuation
version of heterogeneous constrained-root existence.  Once that interface is
honestly separated from `exists_heterogeneousStationaryFaceNash`, the six
listed local targets are plausible direct formalizations.  They remain a
formalized boundary/no-go, not an implementation of the absent leakage
consumer.
