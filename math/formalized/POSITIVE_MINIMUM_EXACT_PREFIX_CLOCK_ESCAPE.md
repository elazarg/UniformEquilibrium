# Positive-minimum exact-prefix rays force quantitative stopping-clock escape

Authors: Math conference synthesis

Independent reviews:
[source and boundary audit](../feedback/COMPILE_FIN4__BY_CODEX_ROOT.md),
[adversarial audit](../feedback/COMPILE_FIN4__BY_CODEX_ADVERSARY.md),
[strengthening audit](../feedback/COMPILE_FIN4__BY_CODEX_STRENGTHEN.md), and
[export-gate audit](../feedback/COMPILE_FIN4__BY_CODEX_GATE.md).

## Exact statement

Fix a finite nonempty player set \(I\) and a bounded quitting reward table.
For an actual behavioral profile \(\sigma\), let \(U_i(\sigma)\) be its
terminal payoff and let \(B_i(\sigma)\) be the supremum payoff over every
unilateral behavioral replacement of player \(i\), including Never and
arbitrarily late randomized stopping.  Put

\[
D(\sigma)=\sum_{i\in I}\bigl(B_i(\sigma)-U_i(\sigma)\bigr).
\]

The result has a generic form and a sharper source-facing Fin4 form.

### Theorem A: fixed-tail exact-prefix escape

Let \(\tau\) be an actual behavioral profile with
\(D_0:=D(\tau)>0\).  Recursively define

\[
\sigma_0=\tau,\qquad \sigma_{n+1}=x_n\star\sigma_n,
\]

where \(x_n\) is an exact quitting-root Nash profile against the unrestricted
behavioral cap of \(\sigma_n\), and \(x\star\sigma\) denotes literal one-date
prefixing.  Write

\[
c_n=\Pr_{x_n}(\text{all Continue}),\qquad
C_n=\prod_{k<n}c_k.
\]

Assume

\[
D(\sigma_n)\ge D_*>0\qquad(n\ge0).
\]

Suppose that under \(\tau\), one fixed nonempty coalition \(S\) is the
terminal quitting coalition at one fixed finite date \(s\), with probability
\(m>0\).  Set

\[
q=\frac{D_*}{D_0}.
\]

Then, for every \(i\in S\):

1. \(C_n=D(\sigma_n)/D_0\ge q\);
2. for every finite cutoff \(T\), all sufficiently large \(n\) carry at
   least \(qm\) of player \(i\)'s finite stopping mass strictly after \(T\);
3. for every fixed finite date \(t\),
   \(\Pr_{\sigma_n}(T_i=t)\to0\);
4. the Never probabilities converge to a number \(a_i\).  If
   \(C_\infty=\lim_n C_n\), then the exact missing coordinate mass
   \(e_i:=1-a_i\) satisfies

   \[
   e_i\ge C_\infty m\ge qm;
   \]

5. for every fixed actual stopping law \(\nu_i\) on
   \(\mathbb N\cup\{\infty\}\), writing
   \(b_i=\nu_i(\infty)\),

   \[
   \lim_{n\to\infty}
   d_{\mathrm{TV}}\!\left(
     \operatorname{Law}_{\sigma_n}(T_i),\nu_i
   \right)
   =1-\min(a_i,b_i)
   \ge e_i
   \ge qm.
   \]

Here total variation is the supremum over events, equivalently one half of
the \(\ell^1\) distance.

Consequently the marginal stopping-law sequence for every \(i\in S\) has no
total-variation-convergent cofinal subsequence and no common finite-tail
tightness envelope.  The ray has no ancestry-preserving actual behavioral
limit in the strategic total-variation category.

This conclusion does not exclude weak convergence in the one-point
compactification of time.  Such a weak limit promotes late finite stopping
mass to the point at infinity and fails to preserve the Never coordinate and
the displayed finite terminal event.

### Theorem B: varying-tail reverse-prefix escape

For every \(k\), let \(x_k\) be a product root.  Let

\[
c_k=\Pr_{x_k}(\text{all Continue}),\qquad
\alpha_k=1-c_k.
\]

Let \(\tau_n\) be arbitrary actual behavioral tails and define

\[
Z_n=x_{n-1}\star x_{n-2}\star\cdots\star x_0\star\tau_n.
\]

Assume \(\alpha_k\to0\).  If one player \(i\) has zero Never probability in
every \(\tau_n\), then for every fixed cutoff \(T\),

\[
\sum_{t=0}^{T}\Pr_{Z_n}(T_i=t)\longrightarrow0,
\]

\[
\Pr_{Z_n}(T_i=\infty)=0,
\]

and hence

\[
\Pr_{Z_n}(T_i>T,\ T_i<\infty)\longrightarrow1.
\]

Thus this marginal has no total-variation-convergent subsequence and is
asymptotically at total-variation distance one from every fixed actual
stopping law.

### Corollary: the source-facing Fin4 maximal-prefix ray

In the current source-facing Fin4 maximal-prefix construction, the rank
\(n\) actual profile consists of the reverse maximal exact-root word followed
by a sure fixed pure-pair row and its rank-dependent counterfactual
continuation.  Assume the positive-minimum Fin4 source has global minimum debt
\(D_*>0\), and take the strict-stall arm of the ray dichotomy.  Let \(D_0\)
be the ray-source debt and \(L\) its debt limit, so

\[
D_0\ge L>D_*>0.
\]

More explicitly, for the source-facing packet set

\[
\tau_n:=\text{\rm packet.rayBaseProfile}(n),
\qquad
Z_n:=\text{\rm packet.rayFamily.rayProfiles}(n).
\]

For each of the two fixed-pair players and every finite cutoff \(T\),

\[
\Pr(T_i>T,\ T_i<\infty)\longrightarrow1.
\]

At the same time, the fixed pair remains the terminal coalition at the
shifted marked date with probability tending to

\[
\frac{L}{D_0}\ge\frac{D_*}{D_0}>0.
\]

Therefore the actual Fin4 ray simultaneously has:

- unit escape of each fixed-pair member's finite stopping clock beyond every
  fixed window; and
- a positive time-forgetting terminal-law mass on the same fixed pair.

Its compact terminal semantic/law cluster is not the
ancestry-preserving strategic-total-variation limit of the displayed actual
ray profiles.

## Conjecture-facing change

The live question
[Compile the source-preserving Fin4 residual into an executable program](../questions/FIN4_RECURRENT_COMPONENT_CONSUMER_OR_MODEL.md)
accepts, for one precisely specified operation and adapter class, an exact
source-attached impossibility theorem that identifies the stronger passport
or alternative construction still possible.

The corollary gives that answer for the infinite canonical maximal-prefix
operation in the strict-ray part of the minimum-return component.  Every
finite ray profile is a literal actual profile, but the infinite outward end
cannot be installed as an actual compact-trace source by stopping-law
total-variation compactification.

This does not consume the strict ray.  A correct completion must instead do
at least one of the following:

1. stop after finitely many prefixes and consume that finite object;
2. discharge the escaping clock mass through an explicit decoder with
   payoff, cap, debt, law and ancestry error bounds; or
3. reconstruct an independently tight actual source before making a
   pointwise post-limit transition.

The marked atom in the separate one-root uniform-escape dispatch lies before
the post-row continuation to which that dispatch is applied.  This packet
does not assert that Theorem A applies to that continuation, and it consumes
no uniform-escape branch.

## Probability, information, and strategy class

Before absorption, a quitting game has one live public history at each date:
all players have Continued so far.  A behavioral strategy therefore induces
a stopping law on

\[
\overline{\mathbb N}=\mathbb N\cup\{\infty\},
\]

where \(\infty\) is Never.  Conversely, every probability law on this space
is behaviorally realized by its conditional hazards.  Players use independent
behavioral randomization.

A unilateral deviation replaces one player's complete behavioral strategy.
Thus the caps in the debt definition cover every stopping law, not only
stationary, bounded-horizon, finite-support, or bounded-memory deviations.

A common finite-tail tightness envelope for marginal laws
\(\lambda_i^n\) is a function

\[
E(T)=\sup_{n,i}\sum_{t>T}\lambda_i^n(t)
\]

whose sum contains only finite dates and which tends to zero.  Never
probability is a separate coordinate.  Finite-coordinate convergence,
Never-coordinate convergence, and such an envelope imply total-variation
convergence and actual behavioral reconstruction.  That general realization
theorem is existing infrastructure, not new content here.

## Proof of Theorem A

Exact cap--Nash prefixing scales every coordinate debt by the joint Continue
mass.  Summing the coordinate identities gives

\[
D(\sigma_{n+1})=c_nD(\sigma_n).
\]

Inductively,

\[
D(\sigma_n)=C_nD_0.
\tag{1}
\]

The positive lower bound on debt yields

\[
C_n\ge q=\frac{D_*}{D_0}>0.
\tag{2}
\]

The event that every prefixed root Continues and the original tail then
terminates with coalition \(S\) at date \(s\) has probability \(C_nm\).  In
\(\sigma_n\) it occurs at date \(n+s\).  Hence

\[
\Pr_{\sigma_n}
 \bigl(S\text{ is terminal at date }n+s\bigr)
=C_nm\ge qm.
\tag{3}
\]

For every \(i\in S\), event (3) forces \(T_i=n+s\).  Once \(n+s>T\), at least
\(qm\) of player \(i\)'s finite stopping mass lies beyond \(T\).  This proves
the asserted failure of a common finite-tail envelope along the full sequence
and every cofinal subsequence.

The products \(C_n\) decrease and are bounded below by \(q\), so they converge
to a positive limit \(C_\infty\).  Therefore

\[
c_n=\frac{C_{n+1}}{C_n}\longrightarrow1.
\tag{4}
\]

Put \(\alpha_n=1-c_n\).  For fixed \(t\) and \(n>t\), the root at absolute
date \(t\) in \(\sigma_n\) is \(x_{n-1-t}\).  The probability that player
\(i\) first stops there is at most the total absorption probability of that
root, so

\[
\Pr_{\sigma_n}(T_i=t)
\le\alpha_{n-1-t}\longrightarrow0.
\tag{5}
\]

Let \(p_{i,k}\) be player \(i\)'s Continue probability in \(x_k\) and put

\[
P_{i,n}=\prod_{k<n}p_{i,k}.
\]

An individual Continue probability dominates joint Continue, so
\(P_{i,n}\ge C_n\ge q\).  These decreasing products converge to some
\(p_i\ge q\), and literal prefixing gives

\[
\Pr_{\sigma_n}(T_i=\infty)
=P_{i,n}\Pr_\tau(T_i=\infty)
\longrightarrow
a_i:=p_i\Pr_\tau(T_i=\infty).
\tag{6}
\]

The retained coalition event of mass \(m\) forces \(i\) to stop finitely.
Thus \(\Pr_\tau(T_i=\infty)\le1-m\).  Since
\(p_i\ge C_\infty\ge q\),

\[
1-a_i
\ge 1-p_i(1-m)
=1-p_i+p_im
\ge p_im
\ge C_\infty m
\ge qm.
\tag{7}
\]

Fix any probability law \(\nu_i\) on
\(\overline{\mathbb N}\).  For a finite cutoff \(T\), let

\[
A_T=\{0,\ldots,T\}\cup\{\infty\}.
\]

Equations (5)--(6) imply

\[
\Pr_{\sigma_n}(T_i\in A_T)\longrightarrow a_i.
\]

Let \(\lambda_i^n=\operatorname{Law}_{\sigma_n}(T_i)\) and put
\(b_i=\nu_i(\infty)\).  On a countable space,

\[
d_{\mathrm{TV}}(\lambda_i^n,\nu_i)
=1-\sum_{t\in\overline{\mathbb N}}
  \min\bigl(\lambda_i^n(t),\nu_i(t)\bigr).
\]

The overlap at \(\infty\) tends to \(\min(a_i,b_i)\).  The finite-date
overlap tends to zero: given \(\varepsilon>0\), choose \(T\) so that
\(\sum_{t>T}\nu_i(t)<\varepsilon\); then

\[
\sum_{t<\infty}\min(\lambda_i^n(t),\nu_i(t))
\le \sum_{t\le T}\lambda_i^n(t)+\varepsilon
\longrightarrow\varepsilon.
\]

Letting \(\varepsilon\downarrow0\) gives

\[
\lim_n d_{\mathrm{TV}}(\lambda_i^n,\nu_i)
=1-\min(a_i,b_i).
\]

This is at least \(1-a_i\), and (7) gives the stated \(C_\infty m\) and
\(qm\) floors.

## Proof of Theorem B

For \(t<n\), the root at absolute date \(t\) in \(Z_n\) is
\(x_{n-1-t}\).  Let \(p_{i,k}\) be player \(i\)'s Continue probability in
\(x_k\).  Reaching date \(t\) can only reduce the chance that \(i\) stops
there, so

\[
\Pr_{Z_n}(T_i=t)\le1-p_{i,n-1-t}.
\]

Since \(c_k\) is the product of Continue probabilities,
\(c_k\le p_{i,k}\), and hence

\[
1-p_{i,k}\le1-c_k=\alpha_k.
\]

For fixed \(T\),

\[
\sum_{t=0}^{T}\Pr_{Z_n}(T_i=t)
\le\sum_{t=0}^{T}\alpha_{n-1-t}\longrightarrow0.
\tag{8}
\]

A finite prefix multiplies the tail's Never probability by an individual
Continue product.  If the tail Never probability is zero, it stays zero.
Total marginal mass is one, so (8) implies

\[
\Pr_{Z_n}(T_i>T,\ T_i<\infty)\longrightarrow1.
\]

For any fixed actual law \(\nu_i\), apply the event
\(A_T=\{0,\ldots,T\}\cup\{\infty\}\).  The \(Z_n\)-mass of this event tends
to zero, while \(\nu_i(A_T)\to1\) as \(T\to\infty\).  Hence the total-variation
distance has liminf one.

## Fin4 adapter

In the source-facing maximal-prefix construction:

1. the varying base is
   \(\tau_n=\text{\rm packet.rayBaseProfile}(n)\), and the actual descendant is
   \(Z_n=\text{\rm packet.rayFamily.rayProfiles}(n)\);
2. the outer root word is the canonical maximal exact cap--Nash word;
3. the ray survival is its joint Continue product;
4. exact debt scaling gives
   \(D(Z_n)=C_nD_0\to L>0\);
5. therefore \(C_n\) converges positively, so
   \(c_n=C_{n+1}/C_n\to1\) and \(\alpha_n\to0\);
6. the rank-dependent base profile has one fixed pure pair quitting surely at
   its first row, so both pair members have zero base Never probability; and
7. exact stage-mass transport gives fixed-pair mass \(C_n\) at the shifted
   marked date.

Theorem B therefore yields unit late-finite clock escape for both pair
members, while its mass at the shifted marked date tends to
\(L/D_0\ge D_*/D_0\).  Hence the time-forgetting terminal-law coordinate of
the pair has liminf at least \(L/D_0\), and every selected law cluster retains
at least that mass.

This adapter uses the fixed-terminal source-facing strict ray.  It does not
identify the pre-tail marked atom from the uniform-escape packet with an atom
inside that packet's post-row continuation.

The separate retainedLaw object of the strict-stall packet fixes
packet.rayBaseProfile(0) as its tail.  The source-facing corollary above
concerns the varying actual family packet.rayFamily.rayProfiles(n); it does
not conflate those two constructions.

## Source correspondence

The generic actual-profile splice identity is
quittingTerminalDebtSum_rootThenContinuation_eq_continueMass_mul_of_capNash
in
UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashEndpointTransport.lean.
Its semantic-pair counterpart is
quittingTerminalSemanticDebtSum_prefix_eq_continueMass_mul_of_capNash in
UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetExcursionReturn.lean.

The literal maximal-ray realization and atom transport are supplied by:

- quittingMaximalCapSemanticPrefixProfile_eq_literalRootStack,
  quittingTerminalDebtSum_maximalCapSemanticPrefixProfile_eq,
  quittingTerminalSemanticDebtSum_maximalCapSemanticPrefixOrbit_eq, and
  quittingStageCoalitionMass_maximalCapSemanticPrefixProfile_add in
  Research/Quitting/MaximalCapSemanticPrefixOrbit.lean;
- quittingMaximalCapSemanticPrefixSurvival_tendsto_limit_div and the strict
  ray absorption account in
  Research/Quitting/MaximalCapSemanticPrefixReturn.lean; and
- rayBaseProfile, rayBaseProfile_stageMass_eq_one,
  rayProfiles_stageMass_eq_survival, and
  nonempty_maximalPrefixRayMinimumReturn_or_stall in
  Research/Quitting/FinFourProducerAtlas/MaximalPrefixRayDichotomy.lean.

The checked rayBaseProfile_neverMass_eq_zero concerns joint terminal
nonabsorption, not a player's marginal Never law.  The marginal zero-Never
fact used here is a new elementary projection from the displayed sure
pure-pair root through quittingBehaviorStoppingLaw in
UniformEquilibrium/Quitting/Paths/BehaviorStoppingLaw.lean.

The declarations
QuittingMinimumLawCausalSuffixPureNeverMarginalLimit.not_jointTight and
QuittingMinimumLawCausalSuffixPureNeverMarginalLimit.not_opponentTight in
Research/Quitting/MinimumLawCausalSuffixPureNeverLimit.lean prove a different
source-matched failure of tightness from replicated all-Continue stacks and a
pure-Never marginal normal form.  They do not state the present exact
reverse-prefix marginal limit or unit-escape conclusion for the canonical
maximal-prefix ray.

The general tight stopping-law realization and uniform unrestricted-cap
continuity are already recorded in
exports/EXECUTABLE_ADAPTER_GRAMMAR_AND_CONSTRAINED_ROOT_NO_GO.md.  They are
cited here only to identify the topology and the missing positive passport.

No paper theorem is used.

## Boundary tests

1. Every finite prefix profile is literal and actual.  The obstruction concerns
   only promotion of the infinite outward end to a strategic-TV source.
2. If the debt lower bound in Theorem A is removed, \(C_n\) may tend to zero,
   and the retained atom may vanish.  The fixed escape floor then disappears.
3. If \(m=0\), Theorem A identifies no marginal finite mass that must escape.
4. Theorem B does not require Nash roots.  Its source-facing corollary uses
   exact Nash and positive limiting debt only to prove \(\alpha_n\to0\).
5. Pointwise convergence of every displayed live hazard to zero may produce
   the all-Never behavior.  That behavior has Never mass one and is not the
   total-variation limit of pair-member laws whose Never mass is always zero.
6. A weak one-point limit can retain neither the finite timing nor the
   distinction between late quitting and Never required by the executable
   trace.
7. A separately reconstructed tight source may still be used pointwise.
   The theorem excludes only ancestry-preserving strategic-TV compactification
   of the displayed ray.

## Lean handoff

The narrow implementation should reuse the existing exact debt and stage-mass
transport declarations rather than storing them as assumptions.

Suggested generic declarations:

- exactCapNashPrefixRay_fixedCoordinate_tendsto_zero;
- exactCapNashPrefixRay_neverProbability_tendsto;
- exactCapNashPrefixRay_tvSeparation_ge_debtRatio_mul_atomMass;
- reversePrefix_finiteHead_tendsto_zero;
- reversePrefix_zeroNever_lateFiniteMass_tendsto_one.

Suggested Fin4 declarations:

- maximalPrefixRay_pairMember_neverMass_eq_zero;
- maximalPrefixRay_pairMember_finiteHead_tendsto_zero;
- maximalPrefixRay_pairMember_lateFiniteMass_tendsto_one;
- maximalPrefixRay_pairMember_tvSeparation_eq_one.

The definitions should expose actual marginal stopping laws.  Total variation
should use one fixed normalization.  The Fin4 adapter should derive zero Never
mass from the sure-pair base and should not store it as an unrelated structure
field.

## Scope and nonclaims

This packet does not prove:

- a uniform-equilibrium payoff;
- a positive terminal exploitability gap;
- nonexistence of the strict maximal-prefix ray;
- a consumer for the clock-escape alternative;
- that the strict ray's compact semantic/law point has no unrelated
  behavioral realization;
- that the separate uniform-escape continuation carries the required atom;
- an approximate-root error ledger;
- a rank decrease or a charged near-return; or
- the Fin4 or finite-quitting uniform-equilibrium conjecture.

It proves that one named source-attached infinite-prefix operation cannot be
used as a compact executable trace edge without a clock-escape decoder or
independently tight source reconstruction.

## Formalization record

Pre-formalization packet SHA-256:
`fc9e93d9be492907d0263059415be0d4723a4a7e18339ce723fc7e3b89f404ec`.

The final source-facing Research adapter was integrated in commit
`24fc73eb9ee92671fa4fbde66234d67781557ee9`. Its checked source SHA-256 is
`5f5be502e1e7a916ea91234b12663615281959d3897ac8f0526fc334bdda54fe`.

The generic production owners are
`UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashFixedTailPrefixRay.lean`,
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/FixedTailCapNashPrefixClockEscape.lean`,
`MathUE/ProbabilityMassFunction/OptionNatEscape.lean`, and
`UniformEquilibrium/Quitting/Paths/ReversePrefixStoppingLaw.lean`. They expose
the coherent exact cap--Nash reverse-prefix ray, debt and survival-product
identities, fixed-coordinate and `Never` limits, finite-head escape, late
finite mass, quantitative general-total-variation separation, and the
no-cofinal-convergent-subsequence conclusion.

The source-facing owner
`Research/Quitting/FinFourProducerAtlas/MaximalPrefixRayClockEscape.lean`
contains the checked declarations
`maximalPrefixRay_finiteHead_tendsto_zero`,
`maximalPrefixRay_pairMember_stoppingLaw_none_eq_zero`,
`maximalPrefixRay_pairMember_lateFiniteMass_tendsto_one`,
`maximalPrefixRay_pairMember_pmfGeneralTV_tendsto_one`,
`maximalPrefixRay_pairMember_no_cofinal_pmfGeneralTV_convergent_subsequence`,
and `nonempty_finFourMaximalPrefixRayClockEscape`. The shifted pair atom has
limiting mass `L / D_0`, at least `D_* / D_0`, positive, and at most one.

Evidence seals:

- **M:** PASS. The fixed-tail and varying-tail clock-escape arguments and the
  source-facing specialization match the reviewed packet mathematics.
- **L:** PASS. The generic declarations are integrated production Lean. The
  Fin4 specialization is checked Research Lean with warnings as errors and
  representative axiom prints using only `propext`, `Classical.choice`, and
  `Quot.sound`.
- **A:** absent as an unconditional Fin4 source. The Research theorem assumes
  a supplied positive-minimum producer, forced-pair packet, and strict-stall
  branch; it does not construct them.
- **C:** absent. No declaration consumes the escaping clocks or turns them
  into a terminal approximation or uniform-equilibrium payoff.

The formalization does not claim convergence failure in a weaker topology,
nonexistence of the strict ray, an independently tight reconstructed source,
cap attainment, a rank decrease, a positive terminal gap, or the Fin4
uniform-equilibrium conjecture.
