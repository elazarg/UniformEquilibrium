# The nonpositive-social boundary chamber is closed by existence

Reviewer/contributor: CLAUDE_FABLE
Date: 2026-08-31
Re: `../questions/POSITIVE_SOCIAL_SURPLUS_ESCAPE_CONSUMER.md`, Boundary
paragraph.

The Boundary states: "If \(R(S)\le0\) for every nonempty coalition, the
supplied attainment theorem gives an actual minimum profile. That chamber
is outside this question." This can be strengthened: in that chamber
(with nonnegative solos, \(n\ge2\)) a **uniform-equilibrium payoff
exists** — the minimum debt is zero, so the attained minimum is an exact
terminal Nash profile.

Proof (two lines on checked ingredients): if not, \(D_*>0\) and a
debt-minimal carrier pair \(z=(u,c)\) exists; summing the checked
singleton moat (`minimumTerminalSemantic_singletonMargin`)
\(c_i-s_i\ge D_*\) over the \(n\) players gives
\(\sum_iu_i\ge\sum_is_i+(n-1)D_*>0\); but \(\sum_iu_i\le0\) on the whole
carrier because every actual profile has
\(\sum_iU_i=\sum_S\mathbb P(S)R(S)\le0\) and the condition is closed.

Status: kernel-checked in the scratch lane as
`fable_socialNonpositive_exists_uniformEquilibriumPayoff` together with
the unconditional necessary condition
`fable_counterexample_minimum_socialPayoff_lowerBound`
(`../fable/lean/FableSocialMoatChamber.lean`; compiles under
`lake env lean`, axioms `propext, Classical.choice, Quot.sound` only;
nothing imports it — integration pending). Ordinary-math write-up with a
weighted-costate generalization: `../fable/SOCIAL_MOAT_CHAMBER.md`.

Consequences for this question: none for its positive-social arm, which
is untouched. The Boundary's chamber closure can be upgraded from
attainment to existence, and the escape question's premise list gains a
checked screen: a table admitting a strictly positive costate \(\theta\)
with \(\theta\cdot r(S)\le0\) for all \(S\) and \(\theta\cdot s\ge0\)
cannot be a counterexample (the weighted form is also kernel-checked, in
`../fable/lean/FableWeightedSocialMoat.lean`).
