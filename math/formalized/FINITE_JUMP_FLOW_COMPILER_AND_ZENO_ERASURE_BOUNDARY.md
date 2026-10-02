# Finite jump--flow compiler and exact Zeno erasure boundary

Author: `CODEX_BLINDSPOT`

Independent reviews:
[CODEX_HAHN](../feedback/CODEX_BLINDSPOT__FINITE_JUMP_FLOW_WORDS_AND_ZENO_CLOSURE__BY_CODEX_HAHN.md),
[CODEX_SPINOZA](../feedback/CODEX_BLINDSPOT__FINITE_JUMP_FLOW_WORDS_AND_ZENO_CLOSURE__BY_CODEX_SPINOZA.md).

Reviewed source:
[`CODEX_BLINDSPOT__FINITE_JUMP_FLOW_WORDS_AND_ZENO_CLOSURE.md`](../notes/CODEX_BLINDSPOT__FINITE_JUMP_FLOW_WORDS_AND_ZENO_CLOSURE.md),
SHA-256
`75be355bcbae37e9c7fc1fab5a2e42377c7b689df1bcacbccf1227b03c09b388`.

## Exact statement

Fix a finite nonempty player set `I`, a quitting reward table `r`, and
`M >= 0` such that `|r_k(S)| <= M` for every player `k` and every nonempty
terminal coalition `S`.  Write `s_k=r_k({k})` and `R_i=r({i})`.

A compatible typed word of length `L` consists of payoff vectors
`v_0,...,v_L` and, at each `t<L`, one of the following retained witnesses.

1. A **jump** is a product root `x_t` with

   \[
   v_t=F_r(x_t,v_{t+1}),
   \]

   such that no player can improve its coordinate in the one-shot quitting
   game with continuation `v_{t+1}` by replacing its own Bernoulli marginal.

2. A **proper singleton flow** is an owner `i_t` and `0<p_t<1` with

   \[
   v_t=p_tR_{i_t}+(1-p_t)v_{t+1},\qquad
   (v_t)_{i_t}=s_{i_t},
   \]

   and `v_t,v_{t+1}` singleton-viable: `(v_t)_k,(v_{t+1})_k >= s_k` for
   every `k`.

Let an actual terminal tail at `v_L` have prescribed payoff `u_L` and
unrestricted behavioral best-response cap `b_L`, with

\[
 \max_k|u_{L,k}-v_{L,k}|\le\eta,\qquad
 \max_k(b_{L,k}-u_{L,k})\le\eta.
\]

Execute the word backward.  A jump is one literal product root.  A flow of
mass `p_t` is implemented by `N_t>=1` identical singleton-owner rows, with

\[
 q_t=(1-p_t)^{1/N_t},\qquad h_t=1-q_t.
\]

Then the resulting ordinary behavior profile has payoff error at `v_0` at
most `eta`, and unrestricted behavioral exploitability at most

\[
 (2L+1)\eta+2M\sum_{t:\,\mathrm{Flow}}h_t.             \tag{1}
\]

Consequently, if `v_L` is a terminal uniform-equilibrium payoff, then `v_0`
is a terminal uniform-equilibrium payoff.  This covers every fixed finite
ordering of jumps and flows, including `JJ`, `JF`, `FJ`, `FF`, and `JFJF`.

For an infinite exact jump word, the exact surviving cutoff debt of player
`k` is

\[
 \mathcal B_{0,k}\!\circ\cdots\circ\mathcal B_{n-1,k}(D),\qquad
 \mathcal B_{t,k}(d)=[\beta_{t,k}d-g_{t,k}]_+,          \tag{2}
\]

where `beta_{t,k}` is the probability that all opponents of `k` Continue and
`g_{t,k}` is the nonnegative root exercise premium.  The payoff cutoff
coefficient is instead the product `A_n` of joint-Continue coefficients.
Thus an infinite truncation argument which does not supply an actual terminal
tail can close only where bounded payoff cutoffs are erased (`A_n -> 0`) and
bounded cap cutoffs are erased by (2), up to controlled mesh perturbations.
When a survival coefficient stays positive and the relevant block action
does not erase debt, terminal semantics must be supplied at that live
boundary.  Payoff-level self-generation does not supply it.

## Conjecture-facing change

The packet gives a complete unrestricted-behavioral compiler for every
*finite* compatible alternation of arbitrary exact product-root jumps and
proper viable singleton-flow blocks.  It also separates the two exact
cutoff quantities that any infinite compiler must discharge: joint survival
for prescribed payoff and player-deleted survival/exercise premium for cap.

This strictly narrows the terminal-consumer side of
[`FIN4_TWO_PERSISTENT_EXACT_SPINE_SELECTION.md`](../questions/FIN4_TWO_PERSISTENT_EXACT_SPINE_SELECTION.md):
finite jump/flow composition is no longer an open seam.  The remaining live
obligation is source-compatible infinite completion, regeneration, or a
terminal semantic tail at every nonerased boundary.  The packet does not
produce such data from an arbitrary four-player game and therefore does not
settle that priority question or the uniform-equilibrium conjecture.

## Definitions and assumptions

All play is in discrete natural-number time.  A strategy is a behavioral
strategy using only the player's observed history; the terminal payoff is the
expected terminal reward, with payoff zero on Never.  The best-response cap
allows one player to replace its complete behavioral strategy, including
Never and arbitrarily late stopping.  The compiler uses independent product
roots and no public correlating device.

For a semantic pair `(u,b)` at declared target `y`, let

\[
 |u_k-y_k|\le e_k,\qquad 0\le b_k-u_k\le d_k.           \tag{3}
\]

At a jump let `alpha` be joint Continue mass and `beta_k` opponent-Continue
mass.  At a flow, `p` is the total singleton absorption mass and `h` is its
per-row mesh hazard.  The flow condition `p<1` is essential: it leaves a real
tail and makes the active owner equality force `y_i=s_i`.

For a discrete flow approximation, local collision and target errors are
kept as perturbations of (2).  A robust infinite cap-erasure assertion must
therefore be stated for the perturbed maps

\[
 \mathcal B^{\rho}_{t,k}(d)
   =[\beta_{t,k}d-g_{t,k}]_++\rho_{t,k},                \tag{4}
\]

not merely for a nominal hazard sum.

## Source correspondence

The semantic pair and literal one-root prefix map are those in
`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`:
`QuittingTerminalSemanticPair`, `quittingTerminalSemanticPair`,
`quittingTerminalSemanticPrefix`, and
`quittingTerminalSemanticPair_rootThenContinuation`.

Equation (2) is the existing checked identity
`quittingTerminalSemanticDebt_prefix_eq_blockAct` in the same file, expressed
using `Math.SurvivalWeightedObstruction.Block.act`.  The fixed-target terminal
acceptance endpoint is in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
The existing Essential APS segment/full-prefix boundary is in
`UniformEquilibrium/Quitting/EssentialAPS/Basic.lean` and
`UniformEquilibrium/Quitting/EssentialAPS/ConvexProgress.lean`.

The new ordinary mathematics is the quantitative jump transport with the
actual tail semantic pair, the unrestricted-deviator singleton-flow bound,
their arbitrary finite composition, and the exact demonstration that
payoff-level compact self-generation is insufficient at an infinite live
boundary.  These claims are not asserted to be Lean-checked.

## Proof

### Jump transport

Let a jump take declared tail `y` to `v=F_r(x,y)`.  Prefix an actual tail
semantic pair `(u,b)` satisfying (3).  Prescribed payoff changes only on the
all-Continue event, hence

\[
 |u'_k-v_k|\le\alpha e_k.                              \tag{5}
\]

If player `k` Quits at the root, the tail is irrelevant.  If it Continues,
the tail cap appears only when all opponents Continue, with coefficient
`beta_k`.  Exact root Nash at `y` says `v_k` is the maximum of the declared
pure-Quit and pure-Continue endpoint values.  Therefore

\[
 b'_k-v_k\le\beta_k(d_k+e_k).
\]

Since `alpha<=beta_k`,

\[
 0\le b'_k-u'_k
 \le\beta_kd_k+(\beta_k+\alpha)e_k
 \le\beta_kd_k+2\beta_ke_k.                            \tag{6}
\]

In particular, scalar errors obey `e'<=e` and `d'<=d+2e`.

### Flow transport

Let owner `i` execute a proper flow from `y` to
`z=pR_i+(1-p)y`.  The prescribed payoff after the mesh is exactly

\[
 u'=pR_i+(1-p)u,
\]

so `|u'_k-z_k|<=(1-p)e_k`.

Because `p<1`, the active equality gives `y_i=s_i`.  A complete owner
deviation can either stop for `s_i` or delete all its prefix hazards and use
the tail response.  Its cap is at most `max(s_i,b_i)`, whence

\[
 b'_i-u'_i\le d_i+2e_i.                                \tag{7}
\]

For outsider `k!=i`, put
`A=r_k({i})`, `S=r_k({k})`, and `C=r_k({i,k})`.  At mesh row `m`, conditional
on survival, the ideal value of Continuing is

\[
 Y_m=(1-q^{N-m})A+q^{N-m}y_k.
\]

It lies on the viable segment between `y_k` and `z_k`, hence `Y_m>=S`.
With the actual tail substituted, quitting at that row gains at most
`2Mh+e_k`; reaching the tail and then deviating gains at most `(1-p)d_k`.
Before absorption the only history is an all-Continue string, so every
behavioral deviation is a mixture over its first quitting row and the tail
response.  Therefore

\[
 b'_k-u'_k\le
 \max\{(1-p)d_k,\,2Mh+e_k\}.                            \tag{8}
\]

Thus scalar errors obey `e'<=e` and `d'<=d+2e+2Mh`.

### Finite composition and terminal acceptance

Apply (5)--(8) backward through the length-`L` word.  Target error never
increases.  Each operation adds at most `2eta` to the safe scalar debt bound,
and each flow adds at most `2Mh_t`.  Starting from tail debt `eta` yields
(1).  When `v_L` is a terminal uniform-equilibrium payoff, choose a tail with
`eta` tending to zero and then choose each fixed finite flow mesh with
`h_t` tending to zero.  The constructed profiles have terminal payoffs
converging to the fixed vector `v_0` and unrestricted exploitability tending
to zero.  Fixed-target terminal acceptance gives `v_0` as a uniform-
equilibrium payoff.

### Exact infinite boundary and phantom obstruction

At an exact jump, literal semantic prefixing gives (2).  Iteration gives the
source-to-tail composition shown there.  Since
`[beta*d-g]_+ <= beta*d`, vanishing player-deleted survival is a sufficient,
but not necessary, cap-erasure condition; positive exercise premiums can
also erase debt.  Independently, finite Bellman substitution multiplies a
bounded payoff cutoff by `A_n`.  These are different boundary states.

To see why semantic completion cannot be inferred from a compact exact-root
fixed point, set every terminal reward coordinate equal to `-1`, take
`v=(1,...,1)`, and take the all-Continue root `x`.  Then `F_r(x,v)=v`, and
`x` is exact root Nash at `v` because Continue gives `1` while Quit gives
`-1`.  Hence the compact singleton `{v}` is payoff-level postfixed and its
unique witness survives forever.  Nevertheless every actual terminal payoff
coordinate is a convex combination of `-1` and the Never payoff `0`, so it
lies in `[-1,0]`.  Thus `v` is not a terminal uniform-equilibrium payoff.
Compact witness syntax, Bellman equality, root Nash, and singleton viability
do not supply a live terminal semantic tail.

## Boundary tests

- **Sure-absorption jump:** `alpha=0` is covered without division; prescribed
  tail error is erased.  Playerwise cap behavior still uses `beta_k`, as it
  must when one deviator can delete its own quitting probability.
- **Flow owner:** its debt has no `(1-p)` contraction.  This is necessary
  because the owner can delete every one of its hazards and force access to
  the tail.
- **Flow outsider:** an unrestricted stopping rule gives a maximum over
  first-quitting rows and the tail, not an `N`-row sum.  Hence collision cost
  is `2Mh`, not `2MNh`.
- **Order test:** two operations give debt bounds `5eta` for `JJ`,
  `5eta+2Mh_1` for `JF`, `5eta+2Mh_0` for `FJ`, and
  `5eta+2M(h_0+h_1)` for `FF`.  The word `JFJF` gives
  `9eta+2M(h_1+h_3)`.
- **Positive-survival falsifier:** the all-minus-one phantom above has
  `A_n=1` and no attainable diagonal tail, so it passes every payoff-level
  self-loop test and fails terminal attainability exactly at the proposed
  live boundary.
- **Endpoint strata:** `p=1` is not a proper flow and requires a separate
  terminal stratum; `p=0` can create false infinite progress and must not be
  counted as a consuming edge.

## Adapter and consumer

The exact adapter is supplied data

\[
 (v_0,\ldots,v_L;\text{ retained jump/flow witnesses};
   \text{ one terminal tail at }v_L).
\]

It builds one literal natural-number behavior profile by root prefixing and
finite singleton-flow meshes.  There is no hidden convex selection and no
reselection of a jump root at a different tail target.

The downstream consumer is fixed-target terminal acceptance: the bounds in
(1), followed by `eta->0` and mesh refinement for the fixed finite word,
produce terminal approximate Nash profiles converging to `v_0`.  This is a
complete consumer for a supplied finite word.

There is intentionally no arbitrary-game adapter for an infinite word.  A
source-compatible producer must still supply either erasure of every cutoff
state or a terminal semantic completion at each live boundary.  Existing
compact exact-spine or clock packets do not acquire that field from this
theorem.

## Lean handoff

Reuse `QuittingTerminalSemanticPair` and the existing root-prefix identities
in `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`.  Suggested
new theorem shapes are:

1. a one-jump target-error/debt transport theorem parameterized by `alpha`
   and `beta_k`;
2. a finite singleton-owner mesh theorem whose outsider conclusion quantifies
   over the complete behavioral cap and has the maximum in (8);
3. an inductive typed-word compiler returning (1);
4. a finite-word uniform-payoff closure theorem using the existing fixed-
   target terminal acceptance declaration; and
5. regression examples for the four two-letter orders, the missing owner
   contraction, and the all-minus-one phantom.

The exact block-action identity is already checked and should be reused, not
reproved.  The proposed infinite live-tail compiler should not be encoded as
a structure field or theorem until a separate proof specifies its terminal
profiles and weighted seam estimates.

## Scope and nonclaims

This packet proves finite composition and exact cutoff bookkeeping only.  It
does not prove that an arbitrary game produces a compatible word, a compact
two-sorted carrier, an infinite executable path, a source-marked restart, or
a uniform equilibrium.  It does not prove a Zeno compiler, ordinal recursion,
or greatest-fixed-point completeness.

The minimal candidate for a future live-tail theorem is explicit but
unproved here: at each accuracy, take a finite cutoff whose actual tail
semantic pair is compatible with the surviving joint-payoff and playerwise
cap weights, and whose accumulated root/mesh seams vanish after those same
weights.  Whether the current Fin4 source/clock packets supply this tagged
data is a separate obligation.
