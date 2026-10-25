# Adversarial review of the local cap collar

Reviewer: CODEX_COLLAR_ADVERSARY.

**Mathematical verdict: PASS.** No unresolved mathematical objection was
found. This is an independent check of the complete ordinary-mathematical
argument, including its unrestricted-law and semantic-closure conclusions.
No other review was read. No Lean command ran; no new Lean result is claimed.

Reviewed artifact:
[CODEX_GLOBAL_SYSTEMATIC__LOCAL_CAP_COLLAR.md](../notes/CODEX_GLOBAL_SYSTEMATIC__LOCAL_CAP_COLLAR.md).
Exact SHA256:

    6b26cd97001aeb10a3b8c0a748b42c5c38719b4f08305403bfacb77f26cdbb9d

## Claim and scope checked

The table has zero own-singleton, live and Never rewards. A supported
probability weight has strictly positive singleton drift; supported pair
participant rewards are strictly positive; and the supported forced-Quit
polynomials have no common nonpositive point except the zero root.
The theorem produces a positive constant delta such that every actual
independent stopping-law profile satisfies

    max_(i in S) B_i >= delta * Pr(absorption).

Every absorbing semantic limit therefore has a supported cap at least delta.
Neither exact Nash roots nor observer optimality are assumed. The result
does not construct equilibria, eliminate the other boundary faces, or solve
Fin4. Its native-payoff scope does not silently translate an original
game's literal Never payoff.

## Independent proof checks

1. **Local reward bounds.** For an opponent hazard sum t, singleton events
   have weighted probability at least t(1-t), while multiple-opponent
   events have probability at most t squared divided by two. Since m<=M,
   rho<=m/(4M) makes the stated supported Quit lower bound valid. The
   passive error from its linear singleton part is at most 3M s squared
   divided by two. The bound rho<=gamma/(8M) gives the claimed positive
   weighted passive drift, with slack.

2. **Root detection.** The third hypothesis says exactly that the maximum
   supported Quit value is positive at every nonzero root. Its minimum
   on the compact set sum q>=rho is therefore strictly positive. Thus a
   supported cap maximum at most eta forces the root into the local box;
   negative supported caps are then excluded by the local Quit bounds.
   The finite positive-participant-row test proves this hypothesis on
   the entire cube, not just its vertices. Singleton support of the
   weight is impossible because its own singleton drift would be zero.

3. **Full-cap recursion.** Quit now versus Continue followed by a complete
   best response gives B_i=max(Q_i,P_i+H_i C_i). Conditioning independent
   laws on all players' survival preserves independence. In the collar,
   every q_i is below one, so these actual conditional laws exist.
   A supremum need not be attained for this recursion. The argument is
   about the complete deviation supremum, not a selected continuation
   payoff or a local Nash test.

4. **The crucial bootstrap.** Initially the supported maximum is at most
   delta, hence at most eta, and the weighted cap w is at most delta.
   The upper tail bound C_i<=K w puts its supported maximum back below
   eta. Applying the local sign conclusion to this actual tail supplies
   C_i>=0 on the support. This justifies replacing H_i C_i by
   (1-s)C_i in the weighted Continue inequality. It gives

       w >= gamma*s/2+(1-s)v,
       w-v >= s*(gamma/2-w)/(1-s) >= gamma*s/4.

   At later steps the invariant is: maximum at most eta and weighted cap
   at most delta. The maximum itself is not claimed to decrease or to
   remain at most delta. This distinction closes the otherwise plausible
   gap in a weighted-cap argument with sparse weights.

5. **Infinite laws and closure.** Summing the decrease gives total hazard
   at most 4w_0/gamma. The product formula for survival and the union
   bound give the absorption estimate. No bounded support, finite period,
   eventual absorption, or interchange of an unattained supremum and a
   limit is needed. For small initial cap the Never probability is at
   least one half, proving the strict actual absorbing bound. Continuity
   of the coordinate inequalities gives the nonstrict bound on the
   absorbing carrier. Retaining the original Never masses also preserves
   the global inequality on the augmented closure.

6. **Zero maximum.** If the supported maximum is zero, the global estimate
   forces joint Never mass one. For every actual profile, all payoff,
   cap and pure-Never response magnitudes are bounded by M times its
   absorption probability: against opponents who all Never, own-singleton
   and Never rewards are zero under every deviation. This estimate passes
   to the augmented closure, so all coordinates equal the AllNever tuple.

## Calibration and attempted falsification

Exact rational multiplication gives

    ((9,7,0,8)/24) Gamma = (1/4,11/24,1/4,1/4).

The strictly positive row0 participant rewards and positive supported
pair rewards verify the detector and local tests on the calibration.
Arbitrary finite nonsingleton passive rewards remain admissible after
enlarging M; their higher-order contributions are explicitly estimated.

Negative caps really occur outside the collar. For example, when everybody
quits at the first date, the calibration's full cap vector is

    (10,0,-e,-1)

for 0<e<=1/10. Thus a proof assuming global nonnegative caps would fail.
The present proof does not make that assumption, and its supported maximum
is large on this control. Exact calculations also checked the sure
coalitions 012 and 023 and all fifteen nonzero vertex roots. These finite
controls supplement the full-cube anchor proof; they do not replace it.

The nonredundancy calculation quantifies over every nonnegative weight,
including sparse weights. The two forced-Quit triple tests imply
v1<epsilon/2 and v3<epsilon. Positive singleton columns then imply
v0<3epsilon/2 and v2<9epsilon/4. Their sum is less than
21epsilon/4<=21/40, contradicting unit total weight. Hence no alternate
weight rescues the older global forced-Quit criterion in the stated range.

The original-calibration bridge was checked separately. A finite deadline
forces absorption, so adding one to every nonempty reward adds exactly one
to that deadline's offer. The native Never offer is the limit of finite
deadline offers by bounded convergence and zero native own-singleton
reward. The original Never offer adds only the probability that some
opponent quits, so cannot exceed one plus the native full cap. This proves
the stated exact cap translation for every profile, while prescribed
payoffs translate by the actual absorption probability. On absorbing
profiles and their pair closures both translations are exactly one.
Literal Never remains zero in both games; no payoff-translation invariance
of the entire original game is assumed.

## Source correspondence

The unconditional declaration
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max`
in `UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean` states the
complete-response recursion used above. The definition
`quittingTerminalSemanticPrefix` and theorem
`quittingTerminalSemanticPair_rootThenContinuation` in
`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean` agree with the
payoff/cap prefix semantics. These declarations were inspected statically.

The incoming-decomposition note defines its boundary tails in the closure
of actual absorbing pairs. The new separation therefore excludes
B0=B1=B3=0 directly, including an all-zero endpoint, without requiring
the tail to be realized or its incoming head to be fully Nash. It leaves
the actual-minimum branch and boundary faces with a positive supported
cap open. This is the correct conjecture-facing scope of the result.
