# Strengthening review of minimum-singleton clock compression

Reviewer: STRENGTHENER

## Verdict

The concentration result is correct and closes the concentration arm of
`questions/FIN4_ATLAS_DIFFUSE_MINIMUM_SINGLETON.md`.  It has a sharper and
formally simpler form than the reviewed note states:

1. one may expose at least the **entire** source singleton mass, not merely
   every strict lower bound;
2. more sharply, one may expose the singleton mass divided by the owner's
   conditional finite-stop mass;
3. the exposing date may be chosen as the owner's first positive stopping
   atom after the anchor; and
4. at that date the owner was already pure Continue at every intervening live
   row, so the target is the existing literal **one-date** pure-Quit update.
   No new multi-date splice is required.

The atlas consequence remains asymptotic: if the selected limiting singleton
mass is `mu`, then every fixed `lambda < mu` is attained eventually and
cofinally.  In general one cannot replace this by the limiting floor `mu`
uniformly over the realizing sequence.

One source-provenance warning is essential.  The target literally retains the
old prefix root word, its length, Continue product, and all source-side data,
but changing the suffix can invalidate cap--Nash exactness of that word for
the target.  Exactness remains a certificate of the unmodified source only.

## Sources inspected

- `quittingBehaviorStoppingLaw_some_toReal` and the stopping-law mass
  identities in
  `UniformEquilibrium/Quitting/Paths/BehaviorStoppingLaw.lean`;
- `quittingStageCoalitionMass` and
  `quittingTerminalOutcomeMass_eq_timeDisintegration` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauTimeDisintegration.lean`;
- `quittingStageCoalitionMass_literalRootStack_add_length` and
  `QuittingMinimumLawCausalSuffixAtom` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLawCarrierCausalization.lean`;
- `QuittingNonsingletonMinimumLawTransfer.tendsto_capNashStackContinueProduct_one`
  in `Research/Quitting/NonsingletonMinimumLawLinearTransfer.lean`;
- `quittingLiteralOneDateProfile`,
  `quittingLiteralOneDateOverride_of_ne`, and
  `quittingProfileLiveRoot_literalOneDateProfile_tail_eq` in
  `Research/Quitting/SameStageEndpointMonodromy.lean`; and
- `FinFourAtlasConcentratedSingletonOrigin` and
  `FinFourAtlasConcentratedSingletonEndpoint` in
  `Research/Quitting/FinFourProducerAtlas/SemanticConnections.lean`.

The Continue-product convergence theorem is genuinely cardinality-free: its
statement and proof use joint convergence, minimum provenance, positive
minimum debt, exact source stacks, and prefixed-debt convergence, but not a
nonsingleton hypothesis.

## Sharp anchored theorem

Let `sigma` be an arbitrary behavioral profile in a finite quitting game, fix
a player `j`, and fix an anchor date `a`.  On the unique live history write

\[
 q_i(t)=\Pr(i\text{ Quits at the live row }t),\qquad c_i(t)=1-q_i(t).
\]

For `t >= a`, put

\[
 \alpha_{a,t}=\left(\prod_{r=a}^{t-1}c_j(r)\right)q_j(t)
\]

and

\[
 \beta_{a,t}=
 \left(\prod_{r<a}\prod_i c_i(r)\right)
 \left(\prod_{r=a}^{t}\prod_{i\ne j}c_i(r)\right).
\]

Let

\[
 A_a=\sum_{t\ge a}\alpha_{a,t}\le1,
 \qquad
 m_a=\sum_{t\ge a}
   \Pr_\sigma(Q=\{j\}\text{ at }t).
\]

Then

\[
 \Pr_\sigma(Q=\{j\}\text{ at }t)=\alpha_{a,t}\beta_{a,t},
 \qquad
 m_a=\sum_{t\ge a}\alpha_{a,t}\beta_{a,t}.
\tag{1}
\]

If `m_a > 0`, then `A_a > 0`.  Let `t_0` be the least `t >= a` with
`alpha_{a,t} > 0`.  Define

\[
 \tau=\operatorname{LiteralOneDate}(\sigma,j,t_0,\mathrm{Quit}).
\]

Then:

\[
 \Pr_\tau(Q=\{j\}\text{ at }t_0)=\beta_{a,t_0}
 \ge \frac{m_a}{A_a}\ge m_a.
\tag{2}
\]

In addition:

- `tau` equals `sigma` as a complete profile at every date other than `t_0`;
- every opponent's complete behavioral strategy is unchanged;
- `j` is already pure Continue in `sigma` at every live row
  `a <= r < t_0`;
- all live roots before `t_0` are unchanged; and
- all live roots strictly after `t_0` are literally unchanged.

Thus the compression is a legal unilateral one-date behavioral replacement,
not merely an operation on stopping-law marginals.

### Proof

The factors in (1) are the owner's conditional first-stop mass after the
anchor and the unconditional probability that the source reaches the anchor
and every opponent survives through `t`.  The `alpha` terms telescope, so
their sum is `A_a <= 1`.

The sequence `beta_{a,t}` is nonincreasing in `t`.  Every positive term of
`alpha` has index at least `t_0`; hence

\[
 m_a
 =\sum_{t\ge a}\alpha_{a,t}\beta_{a,t}
 \le \beta_{a,t_0}\sum_{t\ge a}\alpha_{a,t}
 =\beta_{a,t_0}A_a.
\]

This proves (2).  Minimality of `t_0` also forces `q_j(r)=0` for every
`a <= r < t_0`: starting from conditional survival one at `a`, induction
shows that any earlier positive hazard would itself give a positive earlier
`alpha` term.  Consequently the source owner already Continues surely on the
intervening live rows.  Replacing only its row at `t_0` by pure Quit therefore
exposes exactly `beta_{a,t_0}`.  The remaining literal equalities follow from
the definition of `quittingLiteralOneDateProfile` and the checked post-date
live-root theorem.

The unanchored theorem is the special case `a=0`; there `m_0` is the complete
terminal-law mass of `{j}`.

## Quantitative sharpness

The factor `m_a / A_a` is optimal.  In a two-player chronology, let the
opponent survive an initial row with probability `c` and then Never quit, and
let the owner have conditional finite-stop mass `A` concentrated at its first
possible later date.  Then

\[
 m_a=Ac,\qquad \beta_{a,t_0}=c=m_a/A_a.
\]

Taking `A=1` shows that no theorem can guarantee a stage mass strictly larger
than `m_a`.  Therefore the note's sentence that only strict `lambda<m` is
available because a survivor supremum may be unattained is not correct: the
source-level bound `>= m` is attained at the first supported date.  Strictness
reappears only in the atlas limit, where the actual masses may converge to
`mu` from below.

If the owner is uniform on `N` dates and every opponent Never quits, the
original stage masses are `1/N` while the one-date exposed mass is one.  This
retains the intended diffuse-clock boundary test.

## Cofinal minimum-law adapter

Let `source : FinFourMinimumAtomProducer reward bound`, assume
`source.atom.terminal = {j}`, and set

\[
 \mu=\texttt{source.point.2 (some source.atom.terminal)}>0.
\]

Unpack the causal chronology into suffixes `sigma_n` and root words `roots_n`.
Let

\[
 P_n=\operatorname{ContinueProduct}(roots_n),\qquad
 \Sigma_n=\operatorname{LiteralRootStack}(roots_n,\sigma_n).
\]

Joint law convergence and time disintegration give

\[
 m_j(\sigma_n)\longrightarrow\mu,
\]

while the checked source theorem gives `P_n -> 1`.  Exact stage transport
through the literal root word gives

\[
 m_j^{\ge |roots_n|}(\Sigma_n)=P_nm_j(\sigma_n)\longrightarrow\mu.
\tag{3}
\]

Fix any `0 < lambda < mu` and any requested depth.  Choose a sufficiently
large `n` beyond that depth so the left side of (3) exceeds `lambda`.  Apply
the sharp anchored theorem to `Sigma_n` at anchor `|roots_n|`.  The resulting
one-date target has a singleton stage of mass at least the whole quantity in
(3), hence greater than `lambda`.

This gives a stronger source-faithful conclusion than the proposed
`mu^2/8` scale:

\[
 \boxed{\text{for every fixed }0<\lambda<\mu,
 \text{ concentrated singleton targets occur at arbitrarily deep ranks}.}
\]

For a single canonical declaration one may take `lambda=mu/2`.  The old atlas
scale `mu^2/8` is an immediate weaker corollary.

The same construction can be performed on the suffix first and then copied
under the old word.  In that presentation the target is

\[
 \operatorname{LiteralRootStack}
   (roots_n,\operatorname{LiteralOneDate}(\sigma_n,j,t_n,\mathrm{Quit})),
\]

and its marked date is `|roots_n|+t_n`.  This makes the retained word and the
source-side exact-stack certificate especially explicit.

## Exactly what survives the suffix change

The following data survive literally:

- the complete root word before the suffix anchor;
- its length `n+1` and Continue product `P_n`;
- all prefix absorption laws and the probability of reaching the anchor;
- the entire strategies of every opponent of `j`;
- every live root strictly after the compressed date;
- the source-side theorem
  `IsQuittingCapNashRootStack reward (roots_n) (sigma_n)` as provenance; and
- the exact stage-mass transport formula.

The owner's behavioral best-response cap is also unchanged by the unilateral
replacement, because all of its opponents' complete strategies are unchanged.

What does **not** survive automatically is target-side cap--Nash exactness of
the copied prefix.  The changed owner strategy is an opponent strategy for
the other three players and can change their unrestricted caps.  Accordingly
one must not assert

\[
 \operatorname{IsQuittingCapNashRootStack}
   (roots_n,\operatorname{compressedSuffix}_n).
\]

Nor is the target semantic pair asserted minimum, near-minimum, low-tail, or
punishment-floor admissible.

## Atlas interface

The currently checked `FinFourAtlasConcentratedSingletonEndpoint` projects a
`FinFourLowTailRow` from every origin.  A minimum-singleton source cannot
produce such a row because that row includes nonsingleton collision data.
No fabricated `low` field is legitimate.

A narrow search found no downstream mathematical consumer of the current
common endpoint outside its definitions and atlas normalization.  The safest
handoff is therefore additive:

1. retain the current origin and endpoint unchanged;
2. define a broader literal concentrated-singleton endpoint whose common
   fields are source profile, target profile, stage, singleton, positive
   floor, and post-date live-root equality;
3. map each old endpoint into the broader endpoint, retaining the old origin
   object as provenance; and
4. add the owner-compressed minimum-singleton origin with its source chronology
   and source-side exact-stack certificate.

This avoids weakening or fabricating the stronger low-tail data of the old
origins and avoids an unnecessary breaking refactor.

## Narrow Lean handoff

The smallest useful formalization order is:

1. Prove a generic anchored first-supported-singleton theorem for
   `quittingStageCoalitionMass`.  Its output should use
   `quittingLiteralOneDateProfile reward profile who stage true` and include
   the lower bound by the `tsum` of singleton stage masses from the anchor.
2. Reuse `quittingLiteralOneDateOverride_of_ne` and
   `quittingProfileLiveRoot_literalOneDateProfile_tail_eq`; do not define a
   new interval splice.
3. Prove the source suffix-mass transport identity by summing
   `quittingStageCoalitionMass_literalRootStack_add_length`.
4. Combine joint-law convergence with
   `tendsto_capNashStackContinueProduct_one` to obtain the cofinal
   `lambda < mu` adapter.
5. Add an additive broad endpoint wrapper and the directed-node contraction
   from `minimumLawSingleton` to that endpoint.

The first-supported-date proof can use `Nat.find` on the positive support of
the anchored owner stopping masses.  A finite-window corollary is even more
elementary: choose the least positive singleton stage in the retained finite
window; its pure-Quit one-date target dominates the whole window mass.

## Final assessment

This is an exportable strict atlas contraction once the author packet adopts
the sharper one-date theorem and the source/target exactness distinction.  It
does not consume the concentrated-singleton leaf or prove a uniform payoff.
There is no unresolved mathematical objection to the strengthened result.
