# Uniform payoff for the fullCoreMatrix singleton fibre

Authors: `CODEX_NEGATIVE_CERTIFICATE`

Independent reviews:
[CODEX_SPINOZA adversarial audit](../feedback/CODEX_NEGATIVE_CERTIFICATE__FULLCORE_BALANCED_CYCLE_FIBER_EXCLUSION__BY_CODEX_SPINOZA.md),
[CODEX_SNELL independent falsification audit](../feedback/CODEX_NEGATIVE_CERTIFICATE__FULLCORE_BALANCED_CYCLE_FIBER_EXCLUSION__BY_CODEX_SNELL.md)

## Exact statement

Let (I=\operatorname{Fin}4).  A quitting reward table is a function

\[
 r:\{S\subseteq I:S\ne\varnothing\}\longrightarrow (I\to\mathbb R).
\]

Write (r_i(S)) for its coordinate at player (i).  Define the four columns

\[
\begin{aligned}
C^0&=(0,1,-1,-1),&C^1&=(-1,0,3,1),\\
C^2&=(1,-1,0,1),&C^3&=(1,1,-1,0).
\end{aligned}
\]

These are the columns of the checked `fullCoreMatrix`, with recipient indexing
the row and singleton owner indexing the column.

**Theorem.**  Suppose there is a vector (s\in\mathbb R^4) such that

\[
 r_i(\{j\})=s_i+C^j_i\qquad(i,j\in I).                 \tag{1}
\]

There is no assumption on (s), and all rewards at coalitions of size at
least two are arbitrary.  Then the quitting game associated with (r) has
the uniform-equilibrium payoff

\[
 v=\left(s_0,
 s_1+{1+5\sqrt {13}\over54},
 s_2+{11+\sqrt {13}\over54},
 s_3\right).                                          \tag{2}
\]

In project notation the conclusion is

```text
(quittingGame r).IsUniformEquilibriumPayoff none v.
```

Equivalently, (1) says
`normalizedSoloMatrix r = fullCoreMatrix`: because (C^i_i=0), necessarily
(s_i=r_i(\{i\})), and

\[
 r_i(\{j\})-r_i(\{i\})=C^j_i.
\]

The result is a 48-dimensional affine-fibre theorem.  A Fin4 table has
(4(2^4-1)=60) real coordinates.  The normalized singleton condition fixes
the 12 off-diagonal differences and leaves four own-singleton baselines free.
The 11 coalitions of size at least two contribute (11\cdot4=44) further
free coordinates.  Hence (4+44=48).

## Conjecture-facing change

The exact-search question
[`ESCAPE_AWARE_FIN4_CERTIFICATE_SEARCH`](../questions/ESCAPE_AWARE_FIN4_CERTIFICATE_SEARCH.md)
requires either an all-behavior positive-gap certificate or an executable
uniform-payoff object.  `fullCoreMatrix` was a principled residual-hard seed:
the checked source has full normal core, is standard Q and nonhomogeneous, and
has no relabelled cyclic-open-sign skeleton.  Before this result, lifting its
zero own-singleton rewards to positive baselines and choosing hard
nonsingleton completions remained a candidate direction.

The theorem removes that entire 48-dimensional fibre from counterexample
search.  It covers every positive-solo lift, every boundary choice of the
baseline, and every nonsingleton completion by an executable balanced
singleton cycle whose checked consumer handles unrestricted behavioral
deviations.  What remains open is the Fin4 conjecture outside this fibre and,
in particular, normalized singleton matrices with no balanced singleton
cycle.

## Definitions and assumptions

A behavioral profile observes the complete public history and may randomize
at every finite history.  A unilateral deviator may replace one player's
entire behavioral policy; the replacement may be randomized,
history-dependent, may stop arbitrarily late, or may be Never.

The checked definition
`StochasticGame.Game.IsUniformEquilibriumPayoff` means the following.  For
every (\varepsilon>0), there are one behavioral profile
(\sigma^\varepsilon) and one threshold (N_\varepsilon) such that for every
horizon (N\ge N_\varepsilon):

1. (\sigma^\varepsilon) is an (\varepsilon)-Nash equilibrium of the
   (N)-stage average-payoff game against every unilateral behavioral
   replacement; and
2. every player's prescribed (N)-stage payoff is within (\varepsilon) of
   the same vector (v) in (2).

The profile may depend on (\varepsilon).  The target (v) does not depend on
(\varepsilon), the subdivision mesh, the horizon, or a deviation.

For a cycle with phase owner (o_k), hazard (p_k), singleton endpoint
(r(\{o_k\})), and next coarse value (v_{k+1}), the balanced singleton arc
is

\[
 v_k=p_k r(\{o_k\})+(1-p_k)v_{k+1}.                  \tag{3}
\]

The reader-facing checked structure
`BalancedSingletonCycleCertificate` additionally requires

\[
0\le p_k<1,\qquad
(v_k)_{o_k}=r_{o_k}(\{o_k\}),\qquad
r_i(\{i\})\le(v_k)_i,                                \tag{4}
\]

and, for every player, a positive-hazard phase owned by a different player.
It places no restriction on nonsingleton reward rows.

## Source correspondence

The matrix is defined in

```text
UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/
  FullSupportLCPSignBarrier.lean
```

The relevant checked declarations are:

- `fullCoreMatrix` and `fullCoreMatrix_diagonal`;
- `normalizedSoloMatrix_fullCoreReward`;
- `fullCoreMatrix_standardQ` and `fullCoreMatrix_noHomogeneous`; and
- `fullCoreMatrix_not_exists_relabelledCyclicOpenSignSkeleton`.

The actual-data normalization bridge is
`normalizedSoloMatrix_eq_soloReward_sub` in

```text
UniformEquilibrium/Quitting/Classification/PreemptionGateDictionary.lean
```

The certificate interface and semantic consumers are in

```text
UniformEquilibrium/Quitting/Cycles/BalancedSingletonCertificate.lean
```

with checked declarations:

- `BalancedSingletonCycleCertificate`;
- `BalancedSingletonCycleCertificate.isTerminalNash_and_hasValue`;
- `BalancedSingletonCycleCertificate.isHorizonNash_and_delivers`; and
- `BalancedSingletonCycleCertificate.isUniformEquilibriumPayoff`.

That file imports `UniformEquilibrium/Quitting/Cycles/SingletonArcCycle.lean`,
which contains the one-owner mesh assembly and reaches terminal
uniformization.  The semantic definition and explicit unrestricted-deviation
equivalence are `StochasticGame.Game.IsUniformEquilibriumPayoff` and
`StochasticGame.Game.isεHorizonNash_iff` in
`GameTheory/Stochastic/Uniform.lean`.

The new content is the exact four-phase certificate below and the adapter for
every table satisfying (1).  A narrow search for `sqrt 13`, the hazard
fractions, and a balanced full-core instance found no existing declaration or
conference result.  An existing unrelated (\sqrt {13}) computation concerns
an alternating pair profile, not this matrix or certificate.  No paper claim
is used.

## Proof

Put (t=\sqrt {13}), so (t^2=13) and (3<t<4).  Use four phases, initial
phase zero, with owner (o_k=k).  Define

\[
\begin{aligned}
p_0&={1+5t\over54},&p_1&={19+7t\over138},\\
p_2&={1+t\over14},&p_3&={13+t\over78}.               \tag{5}
\end{aligned}
\]

Define excess values, with phase indices read modulo four,

\[
\begin{aligned}
z_0&=\left(0,{1+5t\over54},{11+t\over54},0\right),\\
z_1&=\left(0,0,{19+7t\over46},{7+5t\over46}\right),\\
z_2&=\left({3+t\over14},0,0,{1+t\over14}\right),\\
z_3&=\left({13+t\over78},{13+7t\over78},0,0\right), \tag{6}
\end{aligned}
\]

and coarse values (v_k=s+z_k).

### Probability, active, and floor fields

Every numerator in (5) is positive.  Using (t<4), those numerators are,
respectively, smaller than (21,47,5,17), hence smaller than their
denominators (54,138,14,78).  Thus (0<p_k<1) for all four phases.

All entries of all (z_k) are nonnegative, and ((z_k)_k=0).  Therefore

\[
(v_k)_k=s_k=r_k(\{k\}),\qquad
r_i(\{i\})=s_i\le s_i+(z_k)_i=(v_k)_i.              \tag{7}
\]

This proves the active-owner equality and every solo-floor inequality.

### Exact arc algebra

We prove

\[
z_k=p_kC^k+(1-p_k)z_{k+1}\quad(k=0,1,2,3).          \tag{8}
\]

Write (q_k=1-p_k).  All nontrivial coordinates follow from the eight exact
products

\[
\begin{array}{ll}
q_0(7+5t)/46=p_0,&
q_0(19+7t)/46=(12+6t)/54,\\
q_1(3+t)/14=p_1,&
q_1(1+t)/14=(2+8t)/138,\\
q_2(13+7t)/78=p_2,&
q_2(13+t)/78=1/7,\\
q_3(11+t)/54=p_3,&
q_3(1+5t)/54=6t/78.                                 \tag{9}
\end{array}
\]

Each is obtained by multiplying numerators and substituting (t^2=13).
For example,

\[
(53-5t)(7+5t)=46(1+5t),\quad
(13-t)(13+t)=156,\quad
(65-t)(11+t)=54(13+t).
\]

Now inspect (8).  For (k=0), the second coordinate is (p_0), the third is

\[
-p_0+(12+6t)/54=(11+t)/54,
\]

and the fourth is (-p_0+p_0=0); the first is zero.  For (k=1), the first
is (-p_1+p_1=0), the third is
(3p_1=(19+7t)/46), and the fourth is

\[
p_1+(2+8t)/138=(7+5t)/46;
\]

the second is zero.  For (k=2), the first is
(p_2+1/7=(3+t)/14), the second is (-p_2+p_2=0), the
fourth is (p_2), and the third is zero.  For (k=3), the first is (p_3),
the second is

\[
p_3+6t/78=(13+7t)/78,
\]

the third is (-p_3+p_3=0), and the fourth is zero.  This checks all 16
coordinates of (8).

As an independent elimination check, the same system reduces to

\[
\begin{aligned}
p_3(39p_3^2-13p_3+1)&=0,\\
27p_0&=1248p_3^2-221p_3,\\
23p_1&=468p_3^2-65p_3,\\
 7p_2&=234p_3^2-39p_3.
\end{aligned}                                       \tag{10}
\]

The selected admissible root is (p_3=(13+\sqrt {13})/78); substituting its
quadratic relation gives the other three hazards in (5).

Adding (s) to both endpoint and continuation in (8), and using (1), gives

\[
v_k=p_k(s+C^k)+(1-p_k)(s+z_{k+1})
   =p_k r(\{k\})+(1-p_k)v_{k+1}.                    \tag{11}
\]

Thus all four literal singleton Bellman arcs (3) hold.

### Opponent divergence and semantic conclusion

For each player (i), each of the three phases owned by a player (k\ne i)
has (p_k>0).  Hence the opponent-divergence field holds.  Equivalently, the
one-cycle survival product after deleting player (i)'s prescribed hazard is
strictly below one.  This is the contraction used by the terminal compiler
for Never and arbitrarily late stopping rules.

Equations (5)--(11), with the owner map (k\mapsto k), coarse map
(k\mapsto v_k), and initial phase zero, satisfy every field of
`BalancedSingletonCycleCertificate`.  The checked theorem
`BalancedSingletonCycleCertificate.isTerminalNash_and_hasValue` gives, at
every positive subdivision (m), an asymptotic terminal Nash profile against
every randomized history-dependent unilateral behavioral policy, terminal
error

```text
balancedSingletonCycleCollisionCap(r)
  * balancedSingletonCycleIntensityCap(certificate) / m,
```

and exact terminal payoff (v_0).  The reader-facing conversion derives the
finite collision cap from the actual finite reward table.  Letting the mesh
grow and invoking the checked
`BalancedSingletonCycleCertificate.isUniformEquilibriumPayoff` yields the
uniform-horizon conclusion at the same fixed (v_0).  Formula (6) identifies
(v_0) with (2), completing the proof.

## Boundary tests

1. **Strict positive solos.**  Taking (s=(1,1,1,1)) gives a genuinely
   positive-solo class, not the zero-solo/all-Continue branch.  The proof is
   unchanged for every positive, zero, negative, or mixed baseline vector.

2. **Zero baseline overlap.**  At (s=0), the known zero-solo theorem may
   already give payoff zero.  The present certificate remains valid and gives
   the different displayed payoff (2).  Uniform-equilibrium payoffs need not
   be unique, so this is consistent.

3. **Hazard boundary.**  All four coarse hazards lie strictly inside
   ((0,1)); no missing zero-hazard phase or sure-quitting boundary convention
   is used.  Only subdivision microhazards tend to zero.

4. **Adverse nonsingleton completion.**  Give arbitrary pair, triple, and
   grand-coalition rewards very large positive or negative magnitudes.  The
   coarse arcs and target do not change.  Large magnitudes increase
   `quittingRewardBound`, hence the finite collision cap and mesh required for
   a requested accuracy, but the error remains a fixed finite constant divided
   by (m).  No mesh uniform over the unbounded 48-dimensional fibre is
   asserted.

5. **Collision provenance.**  At a microphase only one prescribed owner can
   Quit.  One unilateral passive deviator can therefore create only its own
   singleton or a pair collision with that owner.  No nonsingleton row is
   identified with a singleton row.  Coalitions of size at least three are
   unreachable under one unilateral replacement at that microphase, though
   the global reward bound harmlessly includes them.

6. **Never and late clocks.**  Deleting any deviator leaves three positive
   opponent hazards in the cycle, so the deleted-opponent product is strictly
   below one.  This rules out the diffuse/nonattainment regression in which
   mass escapes every finite date without a terminal contraction.

7. **Orientation falsifier.**  The proof uses columns (C^j_i), with owner
   (j) and recipient (i), exactly as
   `normalizedSoloMatrix_eq_soloReward_sub` does.  Transposing the matrix does
   not satisfy the 16 checked identities.  Both independent reviews audited
   this orientation explicitly.

8. **Open-sign no-go.**  The checked theorem excluding a relabelled
   `CyclicOpenSignSkeleton` is not contradicted.  That skeleton belongs to a
   different sufficient producer.  The present balanced orbit has nonuniform
   hazards and explicit continuation excesses.

The two named reviewers independently expanded all 16 radical identities and
attempted the adverse large-collision, reversed-orientation, Never, and
late-clock regressions.  Both reported PASS with no unresolved objection.

## Adapter and consumer

For an arbitrary actual reward table (r) with
`normalizedSoloMatrix r = fullCoreMatrix`, define
(s_i=r_i(\{i\})).  The checked identity
`normalizedSoloMatrix_eq_soloReward_sub` gives (1) coordinatewise.  This is
the actual-data adapter; it does not assume any supplied strategy or any
nonsingleton sign condition.

The new ordinary-mathematics step constructs the concrete owner, hazard, and
coarse-value fields and proves the exact identities above.  The existing
checked reader-facing conversion derives all finite intensity and collision
caps from this certificate and the actual reward table.  The existing checked
consumer
`BalancedSingletonCycleCertificate.isUniformEquilibriumPayoff` reaches the
semantic `IsUniformEquilibriumPayoff` endpoint.  Thus the theorem is a
producer for every table in the fibre, not merely a verifier for an externally
supplied cycle.

## Lean handoff

The narrow formalization should add an explicit four-player instance, without
changing the generic compiler.

Suggested declarations:

1. `fullCoreBalancedHazard : Fin 4 → ℝ` using `Real.sqrt 13`;
2. `fullCoreBalancedExcess : Fin 4 → Payoff (Fin 4)`;
3. exact lemmas `fullCoreBalancedHazard_nonneg`,
   `fullCoreBalancedHazard_lt_one`, and the four arc identities;
4. a constructor taking arbitrary `reward` and
   `normalizedSoloMatrix reward = fullCoreMatrix` and returning
   `BalancedSingletonCycleCertificate reward`; and
5. the fibre theorem concluding the target (2) through
   `BalancedSingletonCycleCertificate.isUniformEquilibriumPayoff`.

Likely imports are

```text
UniformEquilibrium.Quitting.Cycles.BalancedSingletonCertificate
UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.
  FullSupportLCPSignBarrier
UniformEquilibrium.Quitting.Classification.PreemptionGateDictionary
```

The algebra needs only `Real.sq_sqrt`, positivity of 13, the elementary bounds
(3<\sqrt {13}<4), `ring_nf`, and finite-coordinate extensionality.  A useful
finite regression is to prove all 16 coordinates of (8) separately before
assembling the structure.  The desired semantic conclusion must not be added
as a certificate field; it must be obtained from the existing checked
consumer.

## Scope and nonclaims

- The specialized radical certificate and fibre adapter are exact ordinary
  mathematics, not yet checked Lean declarations.  The generic certificate
  compiler and semantic consumer are already checked.
- This does not prove the Fin4 or general finite-quitting conjecture.
- It does not prove that balanced singleton cycles are complete for any larger
  matrix class.
- It says nothing about normalized singleton matrices other than
  `fullCoreMatrix` and its literal relabelings obtained by transporting the
  construction.
- It imposes no bound uniform over the unbounded nonsingleton fibre and no
  common mesh scale over all tables in that fibre.
- It does not claim a stationary profile, a pure equilibrium, a bounded-clock
  completeness theorem, or uniqueness of the payoff.
- It does not weaken arbitrary nonsingleton rewards to zero or discard their
  effect on the finite error constant.
