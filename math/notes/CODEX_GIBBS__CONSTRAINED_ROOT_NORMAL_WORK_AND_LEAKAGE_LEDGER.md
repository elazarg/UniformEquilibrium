# Constrained-root normal work and the unavoidable leakage ledger

Author: `CODEX_GIBBS`

## Current status

This note proves an exact ordinary-mathematics ledger for source-attached
heterogeneously constrained quitting roots.  It uses the full behavioral cap
of the retained tail.  It also proves a positive-minimum-compatible no-go for
the proposed **near-minimum/no-leakage splice**: removing binding lower-face
trembles cannot, from the normal-cone data alone, give the `O(ell^2)` leakage
or no-new-entry estimates needed by that support-rank iteration.  At a
minimum, and more generally when the prefixed excess is `o(normal work)`, a
paid own-debt drain must be repaid at first order in the other debt
coordinates.  A constrained source lying appreciably above the minimum is
not classified here.

The result is not a terminal approximation, a uniform-equilibrium payoff, or
an admissible return.  It narrows the constrained-repair route to an explicit
cross-coordinate compensation consumer.

## Question and source attachment

Let `I` be finite and let `r` be a bounded quitting reward table.  Let

\[
 z=(u,b)
\]

be the terminal semantic pair of one actual behavioral tail `tau`, and put

\[
 d_i=b_i-u_i,
 \qquad D=\sum_i d_i.
\]

All `b_i` are unrestricted behavioral caps, including Never, unbounded
stopping dates, and randomized or history-dependent stopping rules.

Fix heterogeneous lower bounds

\[
 0\le \ell_i<1.
\]

Choose a product root `q` which is an exact Nash point of the one-row game
against the **prescribed continuation payoff** `u`, with player `i` restricted
to the interval `[ell_i,1]`.  Prefix it literally to `tau`; no carrier
realizer is reselected.

The existence assertion here is ordinary finite-game mathematics, not an
application of the repository's stationary face-numerator theorem.  For each
player take the compact interval `[ell_i,1]` as its mixed-action space and
define its payoff at a product point to be the quitting root payoff with
all-Continue outcome `u_i`.  This payoff is continuous in the product and
affine in the player's own coordinate.  The standard compact
convex-game Nash theorem therefore supplies `q`.  Equivalently, one may regard
each interval point as the mixed action in a finite two-action game whose
terminal continuation payoff is `u`.  A checked arbitrary-`u` adapter for
this elementary source theorem is not currently named in the repository.

For player `i`, write

\[
 Q_i=\text{pure-Quit endpoint payoff},\qquad
 C_i=\text{pure-Continue endpoint payoff},
\]

both computed against `u`, and put

\[
 g_i:=Q_i-C_i,
 \qquad
 H_i:=\Pr_q(\text{all opponents of }i\text{ Continue}).
\tag{1}
\]

The constrained optimality condition is

\[
 xg_i\le q_i g_i
 \qquad(\ell_i\le x\le1).
\tag{2}
\]

Define the lower-face normal work

\[
 W_i:=\ell_i(-g_i)_+,
 \qquad W:=\sum_iW_i.
\tag{3}
\]

This definition does not need a separate indicator for the lower face.  If
`g_i<0`, (2) forces `q_i=ell_i`; if `g_i>0`, it forces `q_i=1`; and if
`g_i=0`, both sides of (3) vanish.

## 1. Exact cap-sensitive coordinate ledger

Let `z'=q*z` be the semantic pair of the literal prefixed profile.  Define

\[
 R_i:=\min\{H_i d_i,(g_i)_+\}.
\tag{4}
\]

Then the prefixed full behavioral debt is exactly

\[
 \boxed{
 d_i(z')=W_i+H_i d_i-R_i.}
\tag{5}
\]

### Proof

The exact action-probability formula for the root defect against `u` is

\[
 \delta_i^u
 =(1-q_i)(g_i)_++q_i(-g_i)_+.
\]

Using (2) in the three sign cases gives

\[
 \delta_i^u=W_i.
\tag{6}
\]

The full behavioral debt is not merely this literal defect.  The exact
literal-defect/surcharge decomposition gives

\[
 d_i(z')=\delta_i^u+S_i,
\]

where the continuation-option surcharge is

\[
\begin{aligned}
 S_i
 &=\max\{Q_i,C_i+H_id_i\}-\max\{Q_i,C_i\}\\
 &=\max\{g_i,H_id_i\}-\max\{g_i,0\}\\
 &=H_id_i-\min\{H_id_i,(g_i)_+\}.
\end{aligned}
\tag{7}
\]

Equations (6)--(7) prove (5).  In particular:

\[
\begin{array}{c|c}
 \text{constrained face}&d_i(z')\\ \hline
 q_i=\ell_i,\ g_i\le0&\ell_i(-g_i)+H_id_i,\\
 \ell_i<q_i<1,\ g_i=0&H_id_i,\\
 q_i=1,\ g_i\ge0&(H_id_i-g_i)_+.
\end{array}
\tag{8}
\]

Thus binding normal work and inherited tail debt are distinct exact terms.
This is the constrained-root analogue of the retained-cap timing ledger: a
calculation using only `u` and discarding `b` is invalid.

## 2. Exact minimum balance

Let

\[
 D_*:=\inf\{D(x):x\text{ is an actual terminal semantic pair}\}>0,
\]

and write

\[
 E:=D-D_*,\qquad E':=D(z')-D_*.
\]

Summing (5) gives the exact identity

\[
 \boxed{
 W
 =E'-E
  +\sum_i(1-H_i)d_i
  +\sum_iR_i.}
\tag{9}
\]

Both `E` and `E'` are nonnegative for actual profiles.  Consequently

\[
 \boxed{
 W\ge
 \sum_i(1-H_i)d_i+\sum_iR_i-E.}
\tag{10}
\]

For heterogeneous floors define

\[
 \kappa(\ell):=
 \min_i\max_{j\ne i}\ell_j.
\tag{11}
\]

If at least two players have positive lower floor, then
`kappa(ell)>0`.  Since

\[
 1-H_i\ge\max_{j\ne i}q_j
          \ge\max_{j\ne i}\ell_j
          \ge\kappa(\ell),
\]

(10) yields

\[
 \boxed{
 W\ge\kappa(\ell)D_*-E.}
\tag{12}
\]

For a common floor `ell` on at least two players this is

\[
 W\ge\ell D_*-E.
\tag{13}
\]

Hence, on tails with `E=o(ell)`, a nontrivial constrained repair cannot have
total lower-face normal work `o(ell)`.  This is stronger than the qualitative
observation that zero normal work would make the root an unconstrained
`u`-Nash root and hence, in the maintained near-minimum tube, all Continue.

Equation (9) also identifies exactly what normal work pays for:

1. the new prefix excess `E'` relative to the tail excess `E`;
2. the inherited-debt contraction `sum_i (1-H_i)d_i`; and
3. the upper-face cap shield `sum_i R_i`.

It is not automatically a source-debt decrease.

### Hard-residual singleton separation: all small clocks bind

The Fin4 hard residual does add one useful local sign, but not a leakage
orientation.  On the minimum fiber it supplies a uniform `Delta>0` with

\[
 u_i-r_i(\{i\})\ge\Delta
 \qquad(i\in\operatorname{Fin}4).
\tag{13a}
\]

At the all-Continue root, `Q_i=r_i({i})` and `C_i=u_i`, so `g_i<=-Delta`.
The endpoint values are continuous in the product root and the prescribed
continuation payoff.  Compactness of the prescribed-payoff projection of the
entire minimum fibre and finiteness of the player set therefore give one
uniform neighborhood of that projection and one root radius in which

\[
 g_i\le-\frac\Delta2
 \qquad\text{for every }i.
\tag{13b}
\]

In that tube, constrained optimality forces

\[
 q_i=\ell_i
\]

for every constrained coordinate, while a genuinely free coordinate has
`q_i=0`.  Hence

\[
 \boxed{W_i\ge\ell_i\frac\Delta2.}
\tag{13c}
\]

In particular, if all four lower floors are positive, the constrained prefix
has **full positive debt support**, even if the incoming minimum tail does
not: (8) gives `d_i(z')>=W_i>0` for every player.  The hard-residual sign thus
makes the normal work completely explicit, but also shows that finite-floor
support is artificial.  A support drop obtained by later freeing a floor need
not be a drop of the limiting minimum-source support.

Punishment normality is what produces (13a) in the maintained source.  It
does not put a sign on the other players' cap changes after one floor is
removed; equations (18)--(22) remain the exact boundary.

## 3. Finite backward blocks telescope, but only conditionally

Fix the actual tail `tau` and construct a finite block backwards.  At row
`t`, choose an exact heterogeneous constrained Nash root against the literal
prescribed payoff of the already constructed suffix.  Let

\[
 z_t=q_t*z_{t+1},
 \]

and define `W_t`, `H_(t,i)`, `R_(t,i)`, and
`E_t=D(z_t)-D_*` as above.  Applying (9) at every row and summing gives

\[
 \boxed{
 \sum_{t<H}W_t
 =E_0-E_H
  +\sum_{t<H}\sum_i(1-H_{t,i})d_i(z_{t+1})
  +\sum_{t<H}\sum_iR_{t,i}.}
\tag{14}
\]

This is the sharp normal-work ledger for the proposed finite/backward
constrained repair.  The construction is source-attached: every `z_t` is the
semantic pair of the literal word `q_t*...*q_(H-1)*tau`.

If at every row at least two coordinates have common lower floor `ell`, then

\[
 \sum_{t<H}W_t
 \ge H\ell D_*+E_0-E_H.
\tag{15}
\]

Since terminal debts are uniformly bounded by the reward bound, choosing
`H=C/ell` with `C` large enough to dominate the bounded seam `E_H-E_0`
forces an order-one amount of *conditional row normal work*.  Equation (15)
is not yet an admissible return: the work can
rotate between players, earlier rows attenuate later response plans, and the
initial prescribed payoff/full law need not equal the retained tail's.  It is
nevertheless an exact finite ledger, not a compact-limit diagnostic.

## 4. A binding lower face is an exact own-debt drain

Suppose `g_p<0`, hence `q_p=ell_p`.  Let `q^-` be obtained by changing only
player `p` to pure Continue and let

\[
 y=q^-*z.
\]

Then

\[
 U_p(y)-U_p(z')
 =\ell_p(C_p-Q_p)=W_p.
\tag{16}
\]

The two profiles differ only in player `p`'s complete prescribed strategy,
so their unrestricted `p`-caps agree.  Therefore

\[
 \boxed{d_p(y)=d_p(z')-W_p.}
\tag{17}
\]

This is an executable all-behavior debt drain.  It does not control any
other cap.

## 5. Positive minimum forces first-order cross-coordinate repayment

The missing leakage estimate has an exact opposite-side constraint.  From
(17),

\[
 \boxed{
 \sum_{j\ne p}\bigl(d_j(y)-d_j(z')\bigr)
 =D(y)-D(z')+W_p.}
\tag{18}
\]

Since `D(y)>=D_*`,

\[
 \boxed{
 \sum_{j\ne p}\bigl(d_j(y)-d_j(z')\bigr)
 \ge W_p-E'.}
\tag{19}
\]

Thus if the constrained source `z'` itself is within `o(W_p)` of the minimum,
the other coordinates must receive first-order aggregate debt.  In
particular, if `z'` is on the minimum fiber, they receive at least `W_p`.

There is a sharp unique-debtor corollary.  If `p` is the only debtor at
`z'`, then all other initial debts vanish, and (19) becomes

\[
 \sum_{j\ne p}d_j(y)\ge W_p-E'.
\tag{20}
\]

Whenever `W_p>E'`, some genuinely new debtor satisfies

\[
 \boxed{
 d_j(y)\ge\frac{W_p-E'}{|I|-1}.}
\tag{21}
\]

So a first-order lower-face drain at a near-minimum unique-debtor source does
not give support descent.  It forces support entry.

For a chain of actual removals `x_m -> x_(m+1)` with movers `p_m` and gains
`w_m`, let

\[
 L_m^+:=\sum_{j\ne p_m}
   \bigl(d_j(x_{m+1})-d_j(x_m)\bigr)_+.
\]

Telescoping (18) and using `D(x_K)>=D_*` gives

\[
 \boxed{
 \sum_{m<K}L_m^+
 \ge\sum_{m<K}w_m-\bigl(D(x_0)-D_*\bigr).}
\tag{22}
\]

Consequently a chain of order `1/ell` removals of size at least `c ell`, with
the excess at each removal negligible relative to that removal's work (in
particular for minimum-fibre sources), necessarily creates order-one positive
cross-coordinate leakage.
The hoped-for `O(ell^2)` per-step total/no-entry estimates do not follow from
normal-cone exactness; they would be a substantial additional cancellation
theorem.

## 6. Why the normal work may be artificial support

If `d_p=0` in the retained tail and `p` lies on a binding lower face, (8)
gives

\[
 d_p(z')=W_p.
\tag{23}
\]

The constrained root has manufactured exactly the debt later removed by
freeing `p`.  This is compatible with a positive global minimum because the
prefixed profile may lie above the minimum fiber.  Therefore the lower-face
work selected by (12) need not be attached to an active debtor of the incoming
minimum source.

The following exact scalar ledger illustrates the obstruction without
claiming an actual positive-gap reward table.  Take a hypothetical minimum
tail debt vector

\[
 (D_*,0,0,0)
\]

and a common-floor root whose active coordinate is interior with `g_1=0`,
while each of the other three coordinates is lower-binding with
`g_j=-D_*`.  Formula (8) gives

\[
 D(z')=D_*\bigl((1-\ell)^3+3\ell\bigr)
       =D_*\bigl(1+3\ell^2-\ell^3\bigr).
\tag{24}
\]

After deleting one, two, and three spectator trembles, the same ledger gives

\[
 D_*\bigl((1-\ell)^2+2\ell\bigr)=D_*(1+\ell^2),
 \qquad
 D_*\bigl((1-\ell)+\ell\bigr)=D_*,
 \qquad D_*.
\tag{25}
\]

Every displayed debt respects global minimality.  Each spectator removal has
a first-order own gain `ell D_*`, but that gain is compensated by a
first-order rise in the inherited active debt; total changes are only second
order.  The temporary support drops are not drops of the limiting minimum
source support, because all spectator debts vanish with `ell`.

Equations (24)--(25) are a consistency test for the exact ledger, not a
construction of a quitting-game counterexample.  They show that even perfect
`O(ell^2)` total-debt motion does not imply renewable minimum-support descent.

## 7. Coordinate-flow and active-set cuts

The leakage can be organized as a finite directed flow, but the resulting
graph need not be acyclic.

Let

\[
 x_0\longrightarrow x_1\longrightarrow\cdots\longrightarrow x_K
\]

be any finite chain of actual profiles in which step `m` changes only player
`p_m` and gives that player prescribed-payoff gain `w_m>=0`.  Put

\[
 c_{m,j}:=d_j(x_{m+1})-d_j(x_m)
 \qquad(j\ne p_m),
\]

and `E_m=D(x_m)-D_*`.  Fixed-opponent cap invariance gives the exact row
balance

\[
 \boxed{
 \sum_{j\ne p_m}c_{m,j}
 =w_m+E_{m+1}-E_m.}
\tag{26}
\]

For every player `j`, the coordinate balance is

\[
 \boxed{
 d_j(x_K)-d_j(x_0)
 =-\sum_{m:p_m=j}w_m
  +\sum_{m:p_m\ne j}c_{m,j}.}
\tag{27}
\]

More generally, for every set of labels `A`,

\[
\boxed{
 D_A(x_K)-D_A(x_0)
 =-\sum_{m:p_m\in A}w_m
  +\sum_m\sum_{\substack{j\in A\\j\ne p_m}}c_{m,j},}
\tag{28}
\]

where `D_A=sum_(j in A)d_j`.  Equation (28) is the exact active-set cut
identity.  It is stronger than a support-cardinality account because it
retains signed amounts.

If the chain closes in debt vector, (27) becomes

\[
 \boxed{
 \sum_{m:p_m=j}w_m
 =\sum_{m:p_m\ne j}c_{m,j}}
 \qquad(j\in I).
\tag{29}
\]

Thus a closed positive-work circulation is perfectly compatible with every
minimum inequality: each player's outgoing own-debt work is replenished by
signed cap leakage from the other movers.

### Following the leakage recipient

Suppose one tries to choose the next free/constrained player from a positive
recipient of the preceding removal.  At a near-minimum step with
`w_m>E_m`, (19) guarantees at least one such recipient.  There are then three
possibilities.

1. The recipient is not eligible for the next lower-face removal.  The
   constrained architecture has failed to regenerate its operation.
2. An eligible recipient is followed only finitely many times.  The last
   positive debt remains without a supplied drain; no support drop has been
   proved.
3. Eligible recipients can be followed indefinitely.  Since `I` is finite,
   a mover label repeats and the aggregate positive-leakage graph contains a
   directed label cycle.

The third case is not an exact semantic return—the profiles on two visits to
one label can differ—but it is already enough to refute a purported
well-founded rank based only on mover/recipient labels or active-support
cardinality.  To turn it into progress one needs a chart, law, or cap state
which also decreases around the cycle.

### Smallest abstract circulation

The two-state debt ledger

\[
 (a,0)\xrightarrow[	ext{mover }1]{a}(0,a)
 \xrightarrow[	ext{mover }2]{a}(a,0)
\tag{30}
\]

has constant total debt `a>0`, exact own-debt subtraction, and exact
cross-coordinate repayment.  If these two states are declared to be the
available abstract semantic states, their minimum is positive.  Thus positive
minimality plus the fixed-opponent identity alone does not forbid the
circulation.  This is an abstract ledger model, not a quitting game.

### Exact Fin4 quitting-table circulation

There is also an exact quitting-table realization of the local flow.  Take
players `h,k,i,j`.  Give `h` and `k` payoff zero on every nonempty coalition,
and, for every nonempty coalition `S`, set

\[
 r_i(S)=\mathbf 1_{\{\mathbf 1_{i\in S}\ne\mathbf 1_{j\in S}\}},
 \qquad
 r_j(S)=\mathbf 1_{\{\mathbf 1_{i\in S}=\mathbf 1_{j\in S}\}}.
\tag{31}
\]

At the pure sure-exit roots

\[
 hk,\quad hki,\quad hkij,\quad hkj
\]

the strict cycle is

\[
 hk\xrightarrow{i}hki\xrightarrow{j}hkij
   \xrightarrow{i}hkj\xrightarrow{j}hk.
\tag{32}
\]

Every edge gain is one.  At each vertex exactly the displayed mover has debt
one, its move annihilates that debt, and the next player's debt becomes one.
Total debt and the complete debt support cardinality remain one around the
cycle.  Because `{h,k}` contains two sure quitters, every unilateral
deviation is screened from the continuation; these are full behavioral
terminal debts, not stationary defects.

The half--half mixed root of the two free labels is an exact equilibrium, so
this table has global minimum zero.  It is not a counterexample to Fin4.  It
is the smallest directly relevant exact quitting-table regression showing
that the cut identities permit paid debt circulation.  A positive-minimum
proof must use source provenance beyond the local normal work and minimum
inequality.

### Hard-residual signs do not orient these cuts locally

The maintained punishment and singleton-separation data constrain minimum
tail payoffs and deviations which can reach that tail.  They do not occur in
(26)--(29).  In the sure-exit regression (31)--(32), the second permanent
quitter screens the tail completely after every unilateral update, so no
singleton-floor or punishment value can assign a sign to the free-player
leakage edges.

This does not prove that the complete hard residual realizes the regression;
it does prove that importing punishment normality as an unarticulated sign
argument is invalid.  A useful hard-residual theorem must explicitly attach
the source singleton gap to the constrained mover/recipient flow—e.g. by
forcing work onto an incoming active debtor or by producing a fixed-observer
response seam.

## 8. Consequence for the proposed architecture

The normal-cone repair does solve one issue completely:

\[
 \text{positive constrained clock}
 \quad\leadsto\quad
 \text{interior complementarity, pure Quit, or exact normal work}.
\]

Near a positive minimum with at least two trembled players, the total normal
work is quantitatively nonzero by (12), and finite backward blocks satisfy
the exact telescope (14).

What it does **not** solve is orientation in the near-minimum regime where
the exact repayment bound is first order.  A valid consumer must add at
least one of:

1. an active-owner selection proving a fixed fraction of `W` lies on a debt
   coordinate of the incoming minimum source;
2. a source-faithful fixed-observer response chart turning the telescoped work
   into an executable return seam;
3. a compensation localization proving that the repayment in (19) remains
   within already-active coordinates and eventually exhausts one of them; or
4. a new finite rank on the cross-coordinate compensation graph, together
   with regeneration of the full source packet.

Without one of these fields, the proposed branch

\[
 \text{binding normal work}\Longrightarrow
 \text{renewable support descent}
\]

is false as an inference from the available data.  The normal work is exact
and executable, but global minimality forces the cap leakage which the
iteration was trying to neglect.

## Sources inspected

Checked declarations and files used to validate the interface:

- `heterogeneousFaceNumerator_update_self` and
  `stationaryGain_rootOfHazard_eq_faceNumerator` in
  `UniformEquilibrium/Quitting/Stationary/HeterogeneousConstrainedFaceNash.lean`;
- `quittingRootCoordinateNashDefect_eq_actionProbability_mul_posPart` in
  `UniformEquilibrium/Quitting/Root/NashDefect.lean`;
- `quittingTerminalSemanticDebt_prefix_eq_literalDefect_add_surcharge`,
  `quittingRootContinuationOptionSurcharge_eq_max_increment`, and
  `quittingTerminalSemanticDebt_prefix_eq_capDefect_add_continueMass_mul`,
  together with
  `quittingTerminalSemanticDebt_update_self_eq_sub_payoffGain`, in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticOwnStrategyTransport.lean`;
- `quittingContinuationBestResponseValue_update_self` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauTightness.lean`;
- `terminalSemantic_absorptionDebt_le_excess_add_capDefect` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetReprojectionWindow.lean`;
- `exists_pos_uniformSingletonGap_minimumFiber_of_punishmentNormal` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumFiberIsolation.lean`;
- the reviewed constrained-repair proposal in
  `notes/CODEX_ROOT__NORMAL_CONE_CONSTRAINED_REPAIR_BOUNDARY.md`;
- the retained-cap warning and exact timing ledger in
  `notes/CODEX_PASCAL__ZERO_TAIL_TIMING_NASH_RETAINED_CAP_LEDGER.md`; and
- the source-faithful response-menu transport in
  `exports/SOURCE_FAITHFUL_MINIMUM_ENDPOINT_CAUSALIZATION_AND_RESPONSE_MENU_TRANSPORT.md`.

The generic fixed-opponent repayment identity overlaps the account in
`notes/ATLAS_GATEKEEPER__SOURCE_ATTACHED_SINGLETON_ENDPOINT.md`.  The new
content here is the constrained-root normal-work decomposition, its
positive-minimum lower bound, and the finite backward-block telescope.  The
arbitrary-prescribed-continuation constrained-root existence argument above
is ordinary mathematics; the stationary face-numerator existence theorem is
not cited as its checked source.

## Lean-facing targets

The local statements are finite max/algebra consequences of existing checked
identities:

```text
constrainedRootCoordinateNashDefect_eq_normalWork
constrainedRoot_terminalDebt_eq_normalWork_add_inherited_sub_shield
nearMinimum_totalNormalWork_ge_floor_mul_minimum_sub_excess
lowerFaceRemoval_otherDebtChange_sum_eq
lowerFaceRemoval_exists_supportEntry_of_uniqueDebtor
finiteConstrainedBlock_normalWork_telescope
```

The first five are local and should be formalizable without introducing a new
strategy-class theorem.  The finite-block statement needs only literal
backward prefix construction and repeated use of the one-row identity.
An implementation will first need the elementary arbitrary-`u` heterogeneous
constrained-root existence adapter described above.

## Nonclaims

- No positive-minimum reward table is constructed.
- No best response is assumed attained.
- Conditional row work is not called prescribed-payoff return charge.
- The temporary support of a constrained prefix is not identified with the
  support of its minimum-tail limit.
- No `O(ell^2)` leakage estimate, no-new-entry theorem, terminal
  approximation, admissible return, or uniform-equilibrium payoff is claimed.
