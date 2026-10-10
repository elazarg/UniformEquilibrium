# Bounded independent check of the recovery primitive and finite signal depth

Reviewer: CODEX_EMMY_BOX.

Status: ordinary mathematical review of Sections 3–6 of the current draft.
The displayed recovery estimates and bounded-depth recursion pass this check.
This is not a complete export review, a Lean check, or a producer of relaxed
equilibria. I did not audit a sunspot existence theorem or an adapter from it.

## Claim checked

For a finite nonempty player set of size n and reward bound R>0, let F be a
nonempty prefix-closed family of payoff/full-cap pairs in the reward box,
with nonnegative debts. For a finite convex combination zbar of F and any
finite independent product-root word w, put epsilon=d(T_w zbar) and let S
be the joint prefix survival probability. The claimed bounds are

    inf_F d <= n epsilon/S                         when S>0,
    inf_F d <= epsilon+2R sqrt(S)+2RS              always.

They imply the stated cubic positive-gap bound and zero-gap equivalence for
each fixed finite bound on the number of future public draws per path.

## Valid steps

The finite-prefix formulas retain complete deviation semantics. A pure
deviation either stops at one of the finitely many prefix dates or continues
through the prefix and uses a complete tail deviation. Therefore its cap is
exactly max(M_i,P_i+L_i b_i), including Never and every arbitrarily late
finite response. The latter alternative is a supremum; no attainment is
needed. Conditioning on the player's own first prefix stop gives the stated
formula for the prescribed payoff.

The lower bound D_i(T_w z)>=S D_i(z) has an independent interpretation: the
player may keep its prescribed prefix decisions and change only its tail
strategy. The gain from an approximately optimal tail replacement is S times
the tail debt. This also explains why the joint survival S, rather than the
player-deleted survival L_i, appears in that lower bound.

The large-S extraction uses affine debt under convex averaging. Selecting a
constituent with total debt below its average is legitimate because all debt
coordinates are nonnegative. It deliberately selects the unprefixed child;
requiring the preceding prefix to be retained would change the theorem.

For the small-S extraction, choosing i with maximal L_i gives
L_j^2<=L_i L_j<=S for every j!=i. A constituent satisfying b_i<=bbar_i
therefore decreases the only potentially weakly screened cap. Every other
cap changes by at most 2R sqrt(S), and every prescribed payoff changes by at
most 2RS. The same single constituent is used for all coordinates.

Literal S=0 is sound. If two players have zero own prefix survival, every
L_i vanishes. If exactly one does, only that player's L_i can remain positive,
and the low-cap constituent handles that coordinate exactly. For one player,
the assertions about other players are empty and the selected cap remains
valid. No denominator is introduced in the small-S branch.

The threshold S0=(n epsilon/(4R))^(2/3) gives the advertised h. When S0>1,
the added term exceeds 4R, so the box bound inf_F d<=2R suffices. Epsilon=0
must be treated separately, as the draft already does. The positive-gap
bound follows from the same two branches and has no hidden attainment step.

## Public-signal interpretation and limit order

For a finite publicly revealed child draw, the full cap is the average of the
children's full caps: the player sees the child and can choose a separate
approximately optimal complete response there. This is an observed fresh
draw, not a hidden correlated recommendation, and is essential to the model.
After one constituent is selected, dropping the prefix or retaining it both
remove the first draw and leave a tree with at most one fewer draw per path.
Thus F_(d-1) is the correct extraction target, and repeated extraction gives
h composed d times.

No objection was found in these statements. Their fixed-depth quantifier is
essential: eta_d->0 along d->infinity does not imply eta_0=0 from the displayed
estimates. The iteration's small-error exponent deteriorates to 1/3^d. A
future application needs an actual tree producer with a suitable joint bound
on depth and accuracy, or a different recovery theorem uniform in depth.

## Source cross-check

The prefix formula is consistent with `quittingTerminalSemanticPrefix` in
`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean` and its exact
prescribed/envelope meanings. The target-free conclusion agrees with
`isUniformEquilibriumPayoff_iff_diagonal_mem_terminalSemanticCarrier` in
`UniformEquilibrium/Quitting/Classification/Existence/UniformPayoffTerminalSemanticCarrier.lean`.
These declarations were inspected statically under their imports; no Lean
command was run for this review.

Concrete next check: obtain a source theorem with the exact finite observed
future-draw semantics above, recording its depth as a function of the full
terminal error. An unrelated public-randomization existence theorem does not
supply this adapter automatically.

## Additional bounded check: Section 9, actual private marginal rebalancing

Status: **PASS of the ordinary proof draft**, including the deterministic
calendar-varying extension and expected-only falsifier. No source adapter,
general-game producer, or novelty audit is claimed by this check.

The crucial relative error is valid for every deleted-player subset J.
Writing `L=sum lambda_j`, union bound gives `mu(empty)>=1-L`, while every
singleton has mass at most `lambda_j`. Hence the only negative coordinates
of `mu-nu` are singletons, and

```text
TV(mu,nu)=sum_j [lambda_j-mu({j})]
 <= E sum_{j!=k} q_j q_k
 <= delta E sum_j q_j = delta L.
```

The same exact sign structure holds for the private product law. It gives
a coupling with the categorical reference in which a reference Continue
forces the actual Continue. The two couplings can share the same reference
draw; conditional coupling kernels give a legitimate joint construction.
At the first categorical Quit, the chance either system fails to match is
at most `(beta+beta')/L<=2 delta`. The assertion treats `L=0` separately.
No hidden lower bound on a rare opponent's hazard is used.

The same argument applies if the deviator quits at any deterministic date:
agreement persists until the earlier of that date and opponent absorption,
including the simultaneous coalitions at the stopping date. Never and the
event of no categorical Quit also agree. Thus the response comparison is
uniform over every pure time and Never. The full private cap is their
supremum, whereas the public cap is at least their supremum, since these
responses may ignore the signal. This proves the cap upper bound in the
needed direction. Together with the prescribed-payoff bound it gives
`E_private<=E_public+8R delta`.

For time-inhomogeneous exogenous kernels, let `T` be the first categorical
Quit date. Conditional on `T=t` the same mismatch bound holds. Summing over
all finite `t` bounds total mismatch by `2 delta P(T<infinity)<=2 delta`.
On `T=infinity`, both actual systems always Continue. Hence summable total
hazards and positive Never mass create no missing case. Independence across
dates is used in identifying the original public coalition process with
these per-date laws; a retained public macrostate is not covered.

The expected-only counterexample is also exact. Under the public rare
grand-coalition signal, every player gets the maximal possible payoff 1, so
the profile is full public Nash. Under independent marginal hazard theta,
the displayed prescribed payoff tends to 1/4. Immediate Quit has payoff
`(1-theta)^3+theta^3`, which tends to 1. Thus unrestricted private regret
has lower limit at least 3/4 despite expected total hazard tending to zero.
This verifies the stated failure of an expected-only hypothesis.

One useful next falsification target is retained *persistent* macrostate
with uniformly small conditional total hazard, rather than a rare signal
with large conditional hazards. The latter is already settled here.

## Additional bounded check: no-memory source obstruction on the boundary table

Status: **PASS of the ordinary composition in Section 10.** This is not
an independent export gate, a new Lean theorem, or a universal no-UE result.

I inspected the exact statement of
`isAsymptoticNash_quittingSerializedRoots` in
`UniformEquilibrium/Quitting/Root/SequentialSerializationEquilibrium.lean`.
It requires four players, unit own singleton exits, reward bound M,
coordinate hazard bound, and full terminal approximate Nash of the supplied
root-sequence profile; it concludes full terminal approximate Nash with
error enlarged by `32*M*hazardBound`. Its proof explicitly treats every
pure finite deadline and Never and then uses behavioral pure-time extremality.
Therefore no missing late-date/deleted-clock assumption is introduced by
using this declaration here.

I inspected `quittingSerializedRoots` in
`UniformEquilibrium/Quitting/Root/SequentialSerialization.lean` and
`Schedule`, `Schedule.roots` in
`UniformEquilibrium/Quitting/Examples/SolanVieilleBoundarySoloHazardLedger.lean`.
The proposed schedule has owner `t mod 4` and hazard equal to the corresponding
original marginal in row `floor(t/4)`. It is literally the serialized root
process, not merely a distributional analogy. Marginals lie in `[0,1]`,
and the uniform conditional total bound implies each marginal is at most
delta. Stationarity or positive/nonsummable total hazard is unnecessary.

Finally I inspected `Schedule.exploitability` and
`Schedule.one_over_sixtyEight_lt_literal_exploitability` in
`UniformEquilibrium/Quitting/Examples/SolanVieilleBoundarySoloHazardSemantic.lean`.
The former is exactly `quittingTerminalExploitability boundaryReward
schedule.profile`; the latter has no extra charge-supply hypothesis.
`boundaryReward_unitSoloExit` supplies the required normalization, the
displayed finite table has absolute rewards at most 4, and
`periodTwo_residualHardClass` in
`UniformEquilibrium/Quitting/Examples/BlockPair/FourPlayerPairedSingletonResidualHard.lean`
has the claimed literal table as its argument.

Thus the additions `8*4 delta + 32*4 delta = 160 delta` are correct,
and the full cap floor indeed yields `epsilon+160 delta>1/68`.
This excludes unconditional diffuse no-memory production even on a solved
full-normal/Q residual example. It does not exclude a producer only for
actual no-UE tables, a disjunction dispatching this solved example first,
or a retained-state source with a genuinely different legal-root recovery.
