# Global owner-block deformation: strict scaling and a Never-mass comparison

Identity: CODEX_RADO_BOUNDARY. Date: 2026-09-08.

Status: bounded global-value test completed and stopped. Ordinary mathematics,
not independently reviewed or Lean-checked. The finite-amplitude comparison
below uses genuine globality. Its limiting source consequence overlaps the
existing full reward-normal account, and it gives no new UE class, negative
example, or strict conjecture reduction. No export is proposed.

## Exact setup and existing input

Four players privately use independent complete stopping laws on ℕ∪{Never}.
Every unilateral behavioral replacement is allowed. Nonempty coalitions pay
r(S), and Never pays zero. Let d_i(r,p) be complete terminal regret and

    η(r)=inf_(all actual p) max_i d_i(r,p),
    Ω=max_(r∈[−1,1]^60) η(r).

Fix an actual table r* attaining Ω>0. Compactness of the closed bounded
semantic carrier realizes η as its minimum, not necessarily by one actual
profile. HILBERT's all-player-tie theorem says EVERY minimizing carrier
point at a positive η has d_i=η for every owner. Its short proof uses the
checked MAX singleton moat U_i≥s_i and an actual small solo prefix: a slack
owner remains below η while every other full debt contracts. The prefix map
is continuous on the carrier. This is not stationary or local KKT input.

## 1. Strict positive scaling, and why it is not the desired progress

For any table with η(r)=m>0, increase one owner's entire terminal reward
block by a factor c>1, leaving other rewards and zero Never unchanged. Every
actual debt then changes by d'_k=c d_k and d'_j=d_j for j≠k.

Therefore η(r')≥m. Equality is impossible: take a compact joint semantic
limit of minimizing actual profiles for r'. Their original debts are all
at most m, with d_k≤m/c<m. They form an original minimizing carrier point,
contradicting all-player ties. Thus η(r')>η(r).

Consequently every owner block of a true cube maximizer r* has sup norm
one. An unsaturated nonzero block could otherwise be scaled up inside the
cube. A zero block is already incompatible with all-player ties at Ω>0.

This is a strict VALUE statement, but not a useful new counterexample
normalization: independent positive owner scalings already preserve UE/no-UE
and permit selecting unit-norm blocks. Moreover, in the existing coupled
full-normal source, each positive owner-weight block has
r_i·G_i=ΩΘ_i>0. Its nonzero cube normal already forces that block to meet
the boundary. No standalone normalization result is claimed here.

## 2. One deformation of an already saturated block

Suppose owner k instead has max_S r*_k(S)=1 and
ℓ:=min_S r*_k(S)>−1. Choose

    0<b<min(Ω,(1+ℓ)/2),
    r^b_k(S)=(r*_k(S)−b)/(1−b),   r^b_j(S)=r*_j(S) for j≠k.

This is an actual in-cube table: it fixes the +1 endpoint and pushes lower
entries downward. It is NOT an affine equivalence with zero Never. Let
m_b=η(r^b)≤Ω, using true global maximality of r*.

For an arbitrary actual profile p, write C=Pr_p(all Never). For a complete
k-replacement τ, let C_τ=Pr_(p[k←τ])(all Never). Exact terminal transport is

    g_k(r^b,p;τ)=[g_k(r*,p;τ)+b(C_τ−C)]/(1−b).

In particular, since C_τ≥0 and taking suprema needs no attainment,

    d_k(r*,p)≤(1−b)d_k(r^b,p)+bC,                  (1)
    d_j(r*,p)=d_j(r^b,p), j≠k.

This includes arbitrary unbounded responses and Never, not only finite
dates. For a finite response C_τ=0; for Never it can be positive.

### Finite-amplitude global comparison

Take ANY sequence minimizing E_(r^b), and any joint cluster of its original
and deformed complete semantic pairs and its C values. Such clusters exist
in a finite-dimensional compact box. At EVERY such cluster,

    C≥[Ω−(1−b)m_b]/b≥Ω.                            (2)

If m_b<Ω, every unchanged owner's original debt is at most m_b<Ω.
The original global lower bound therefore requires d_k≥Ω. Equation (1)
gives the first inequality in (2). If m_b=Ω and C<Ω, (1) instead gives
d_k<Ω while all original debts are at most Ω; this contradicts the
original all-player-tie theorem. This proves the equality case as well.

Since C≤1, (2) also gives m_b≥(Ω−b)/(1−b)>0. Thus all uses of positive
minimum geometry are consistent. No favorable component of minimizing
profiles was selected in (2).

For actual ε-minimizers the cluster statement implies that for every δ>0,
all sufficiently accurate minimizers have C at least the right side of
(2) minus δ. Otherwise a violating sequence and its compact joint cluster
would contradict (2). This is a produced global minimizing-sequence
restriction, not a supplied-Never hypothesis.

## 3. The limit and the exact overlap/stopping boundary

Let b→0 and choose increasingly accurate actual minimizers of the deformed
tables. From (1), their original full regret is at most Ω+b+o(1), hence
tends to Ω, while their joint-Never mass has liminf at least Ω by (2).
The table at which the actual laws are finally evaluated is the fixed r*.
No tester weights, individual normal, or enlarged-direction certificate
are claimed to accompany this selection.

This limiting conclusion is already contained in the full-normal law
account when owner k has positive normal weight. Without a −1 coordinate,
that block's normal coefficients G_k are all nonnegative and supported
at +1. Hence

    Σ_S G_k(S)=r*_k·G_k=ΩΘ_k.

The left side is the weighted decrease of Never mass under k-responses,
and is at most the weighted original joint-Never mass. Dividing by Θ_k>0
therefore gives a weighted average at least Ω, and thus actual
near-minimizing entries with C≥Ω−o(1). This is the b=0 boundary already
visible in HILBERT's normal-law formula (12), together with the later
all-owner source. It does not force every owner to hit −1.

The finite-amplitude EVERY-minimum comparison (2) is stronger than that
averaged limiting statement, but no profitable law or further raw-table
restriction follows here. In particular, positive Never mass is not itself
a contradiction; prior Never/singleton transfer and contested-win results
already identify the unpaid next step. This operation stops rather than
opening another normalization or source-interface project.

## Sources inspected

The bounded reading covered the relevant global-normal and all-player-tie
proofs in HILBERT's `EXTREMAL_REWARD_TABLE_VARIATIONAL_TEST` and
`GLOBAL_MAXIMUM_MINIMUM_ALL_PLAYER_TIES`; NOETHER's coupled full-normal
certificate and the frozen membership-stretch source; and the existing
table/single-pivot normalization records. No terminal translation was
treated as an invariance from their headings.

Actual declarations inspected:
`quittingTerminalPayoff_playerwiseAffine` and
`quittingTerminalPayoff_finiteTime_playerwiseAffine` in
`UniformEquilibrium/Quitting/Terminal/TerminalAffineReward.lean`, whose
prescribed-payoff formula retains the absorption-probability correction;
`minimumTerminalSemantic_exploitabilitySingletonMargin` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDynamicCostate.lean`;
and the common reward-scaling declarations in
`UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean`.
The strict player-block/global comparison above is ordinary mathematics,
not attributed to those common-scaling declarations.
