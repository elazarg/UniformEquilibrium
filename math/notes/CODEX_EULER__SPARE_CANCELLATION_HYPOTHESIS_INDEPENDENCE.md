# Exact rational independence tests for same-profile spare cancellation

**Author:** CODEX_EULER  
**Date:** 2026-08-25  
**Status:** proved ordinary mathematics; internal sharpness note, not Lean-checked and not proposed for export.

## 1. Question

The conditional verifier in
[`CHATGPT_EXTERNAL__SAME_PROFILE_SPARE_PLAYER_CANCELLATION.md`](CHATGPT_EXTERNAL__SAME_PROFILE_SPARE_PLAYER_CANCELLATION.md)
uses two hypotheses not supplied by the checked four-player pair-base
interfaces:

1. the two free coordinates remain complementary when a fifth spare player
   is inserted surely; and
2. the scalar spare-debt budget

   \[
   q_*\kappa\le D_0. \tag{1.1}
   \]

This note gives two complete rational five-player tables.  The first satisfies
all four numbered hypotheses of the verifier except (1.1).  The second
satisfies source localization, base cancellation, endpoint floors, and
(1.1), but violates exactly one free endpoint-complementarity condition and
recreates debt at the cancellation point.

Thus neither missing condition follows from the other local hypotheses.  The
examples do not claim that the displayed source is a positive global
minimum, nor that an arbitrary five-player extension preserves an ambient
terminal-gap witness.

## 2. Common notation and an exact punishment-floor certificate

Let

\[
I=\{0,1,2,3,4\},\qquad
B=\{0,1\},\quad F=\{2,3\},\quad s=4.
\]

At the source root take

\[
p_0=p_1=1,\qquad p_2=p_3=p_4=0. \tag{2.1}
\]

Thus the source terminal coalition is deterministically `B`.  In the family
`sigma^q`, only the spare probability changes from zero to `q`; at `q=1` the
terminal coalition is deterministically `B union {4}`.  Repeat the displayed
root after all Continue, or use any fixed behavioral continuation: it is
unreached because both base players quit surely.

Each reward table below uses the convention

\[
r_i(S)=-20 \tag{2.2}
\]

for every nonempty coalition/coordinate pair not explicitly overridden.
All rewards are rational and bounded in absolute value by `20`.

The following pure opponent rows bound every behavioral punishment value by
`-20`:

\[
h(0)=2,\quad h(1)=2,\quad h(2)=3,
\quad h(3)=2,\quad h(4)=2. \tag{2.3}
\]

For every `i`, neither `r_i({h(i)})` nor `r_i({i,h(i)})` is overridden in
either example.  If opponent `h(i)` quits surely and all other opponents
continue, player `i` obtains `-20` whether it quits immediately or continues;
later behavior is irrelevant.  Hence the unrestricted cap against that
opponent profile is `-20`, and

\[
\chi_i\le -20. \tag{2.4}
\]

This is exactly the pure-row bound
`quittingPunishmentValue_le_pureRowCap` from
`UniformEquilibrium/Quitting/Punishment/ContinueFloor.lean`.  Every endpoint
payoff below is at least `-20`, so the full endpoint punishment-floor
hypothesis is verified, not assumed.

## 3. Example A: all complementarity holds but `(SC)` fails

In addition to the default (2.2), define the following coordinatewise
overrides.  Here `B4` abbreviates `B union {4}`.

### Base coordinates

\[
\begin{array}{c|rrrr}
 & \{1\} & B & \{1,4\} & B4\\ \hline
r_0 & 1 & 0 & -1 & 0
\end{array}
\]

and symmetrically

\[
\begin{array}{c|rrrr}
 & \{0\} & B & \{0,4\} & B4\\ \hline
r_1 & 1 & 0 & -1 & 0.
\end{array}
\]

### Free coordinates

For each `f in {2,3}`, set

\[
r_f(B)=r_f(B\cup\{f\})
=r_f(B4)=r_f(B4\cup\{f\})=0. \tag{3.1}
\]

### Spare coordinate

Set

\[
r_4(B)=0,\qquad r_4(B4)=-10. \tag{3.2}
\]

### Exact calculation

For each base player,

\[
\Delta_b^0=0-1=-1,\qquad
\Delta_b^1=0-(-1)=1. \tag{3.3}
\]

Thus

\[
a_0=a_1=1,\quad D_0=2,\quad
\lambda_0=\lambda_1=2,\quad
\tau_0=\tau_1=\frac12,\quad q_*=\frac12. \tag{3.4}
\]

For both free players, (3.1) gives

\[
\Delta_f^0=\Delta_f^1=0,
\qquad \Phi_0(\Delta_f^0)=\Phi_0(\Delta_f^1)=0. \tag{3.5}
\]

For the spare,

\[
\Delta_4=r_4(B4)-r_4(B)=-10,qquad \kappa=10. \tag{3.6}
\]

At `q=0` the prescribed payoff vector is identically zero.  At `q=1` it is
zero in the four old coordinates and `-10` in coordinate `4`.  Therefore
(2.4) proves both endpoint floor inequalities.

Every hypothesis of the verifier other than `(SC)` now holds, but

\[
q_*\kappa=\frac12\cdot 10=5>D_0=2. \tag{3.7}
\]

At the base-cancellation point the old four debts vanish and the spare debt
is exactly `5`; the total debt has increased from `2` to `5`.  This is an
exact fixed-bound counterexample to any attempt to derive `(SC)` from source
debt, old-player endpoint complementarity, base sign crossing, and endpoint
punishment floors.

## 4. Example B: `(SC)` holds but one free endpoint recreates debt

Keep all base-coordinate overrides from Example A.  Keep player `3`'s four
free-coordinate overrides equal to zero.  For player `2`, set

\[
r_2(B)=r_2(B\cup\{2\})=r_2(B4)=0,
\qquad r_2(B4\cup\{2\})=2. \tag{4.1}
\]

For the spare set

\[
r_4(B)=0,\qquad r_4(B4)=-2. \tag{4.2}
\]

The source calculations are unchanged:

\[
a_0=a_1=1,\quad D_0=2,\quad q_*=\frac12. \tag{4.3}
\]

and both free players have zero source debt.  The spare satisfies

\[
\Delta_4=-2,\quad\kappa=2,\quad
q_*\kappa=1\le D_0. \tag{4.4}
\]

All endpoint payoffs are zero except the spare payoff `-2` at `q=1`, so (2.4)
again verifies every punishment floor.

Player `3` remains complementary at both endpoints.  Player `2`, however,
has prescribed probability `p_2=0` and

\[
\Delta_2^0=0,\qquad \Delta_2^1=2,\qquad
\Phi_0(\Delta_2^1)=2>0. \tag{4.5}
\]

At `q_*=1/2`, affine insertion gives

\[
\Delta_2(q_*)=1,\qquad d_2(q_*)=\Phi_0(1)=1. \tag{4.6}
\]

Both base debts are zero, while

\[
d_4(q_*)=q_*\kappa=1. \tag{4.7}
\]

Thus the target debt vector is supported on `{2,4}` and has total debt `2`.
The scalar budget holds—even with equality of source and target total debt—
but cancellation does not solve the free coordinates and does not reduce
support cardinality.  Endpoint complementarity is therefore genuinely
independent of `(SC)` and of all endpoint floor inequalities.

## 5. Strongest valid independence statement

There exist rational five-player quitting reward tables with reward bound
`20` and deterministic two-sure-quitter source roots such that:

1. source positive debt is exactly the two-player base;
2. both base endpoint gaps cross from `-1` to `+1` and hence
   `q_*=1/2`;
3. all five prescribed payoff coordinates dominate their unrestricted
   behavioral punishment values at both spare endpoints; and
4. either
   - both free coordinates are complementary at both endpoints but
     `q_* kappa>D_0`, or
   - `q_* kappa<=D_0` but a free endpoint is noncomplementary and carries
     positive debt at `q_*`.

The two extra hypotheses in the spare-cancellation verifier are therefore
logically independent even inside a uniformly bounded, deterministic-root
class.  No tail conditioning, stationary-only deviation restriction, or
approximation is involved.

## 6. Relation to checked pair-base sources and exact remaining producer

I inspected the following nearby declarations:

- `nonempty_finFourPairBaseStationaryDebtLocalization` in
  `PairBaseStationaryDebtLocalization.lean`;
- `nonempty_finFourPairBaseStationaryTwoDebtorHandoff` in
  `PairBaseStationaryTwoDebtorHandoff.lean`;
- `QuittingTerminalExploitabilityWitness.nonempty_finFour_pairBasePaidResetEndpointBoundary`
  in `PairBasePaidResetEndpointEdge.lean`; and
- `capNash_isZeroNash_at_prescribed_iff_surcharge_eq_liveDebt` in
  `PairBasePaidResetEndpointSeam.lean`.

The first two solve the two free coordinates at the **original four-player
source**.  None constrains rewards on coalitions containing a newly added
fifth player.  Those new coordinate rows freely determine the endpoint gaps
and the spare premium, as the two tables above make explicit.  The endpoint
edge/seam declarations likewise do not compare that premium with the source
debt.

Accordingly, a useful producer must add genuinely coupled fifth-player data:
it must co-realize both free endpoint-complementarity equations and

\[
\kappa\max_{b\in B}
  \frac{a_b}{a_b+\Delta_b^1}
\le a_{b_0}+a_{b_1}. \tag{6.1}
\]

Global minimum does not provide (6.1).  Once the other cancellation
hypotheses hold, comparison with the actual `q_*` profile gives instead

\[
D_0\le q_*\kappa, \tag{6.2}
\]

the reverse inequality.  Hence the minimum-fiber support drop requires an
additional equality-producing mechanism, not merely the existing minimum
comparison.

## 7. Concrete next check

The sharp remaining question is whether an actual five-player extension
arising from a maintained terminal-gap/collision construction imposes a
balance identity linking the spare premium to the two base cancellation
gaps.  Arbitrary coordinatewise extension does not.  Any proposed producer
should therefore identify the exact source-native law or Bellman equation
which rules out Examples A and B; label incidence alone cannot do so.
