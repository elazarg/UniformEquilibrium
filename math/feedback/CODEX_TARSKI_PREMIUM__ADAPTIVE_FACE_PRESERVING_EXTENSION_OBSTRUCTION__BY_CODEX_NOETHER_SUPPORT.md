# Independent review of adaptive face-preserving extension failure

Reviewer: CODEX_NOETHER_SUPPORT.

Primary reviewed source:
[ADAPTIVE_FACE_PRESERVING_EXTENSION_OBSTRUCTION](../notes/CODEX_TARSKI_PREMIUM__ADAPTIVE_FACE_PRESERVING_EXTENSION_OBSTRUCTION.md),
SHA256 `76dc32aec1d83ffbf82c2706f6ee5834a8650ab45b23f72c7287c552bdc65533`.

Verdict: PASS for the complete theorem and its explicit solved-game witness.
No mathematical repair is required. I reconstructed an unrestricted-clock
proof from the raw table before reading the manuscript, including the
all-four-face conclusion. The direct adjacent-date argument below is an
optional proof simplification, not a correction of the valid original
conditional-tail proof. This review is ordinary mathematics, not Lean-checked.

## 1. Claim, raw data, and independent falsification target

For the specified table, every nonempty coalition S pays

    r_0(S)=1 if 0∈S, else 2·1_{2∈S};
    r_1(S)=(2·1_{0∈S}−1)·1_{1∈S};
    r_2(S)=(2·1_{1∈S}−1)·1_{2∈S};
    r_3(S)=1_{3∈S}.

Never is zero. Own singletons are (1,−1,−1,1), not the canonical vector
(1,0,0,0). Let E(μ) be maximum full terminal debt, and E_−d(μ_−d) the same
quantity for the actual induced game after deleting d and retaining every
surviving marginal. The claimed theorem is

    ∃c>0 ∀μ ∀d∈{0,1,2,3}, E(μ)+E_−d(μ_−d)≥c.

The laws are arbitrary independent behavioral laws on ℕ∪{Never}. There is
no support, hazard, deadline, or moment restriction, and the outsider may
use any independent law. This rules out adaptive omitted-player selection,
not just a fixed deleted face or an unfavorable best-reply tie.

My initial attempted falsifiers were: a diffuse anchor clock, a moving
deadline, hidden active clocks placed arbitrarily after anchor absorption,
and the possibility of selecting the formerly inactive dummy face. The
parent-rigidity argument eliminates the first two; the adjacent-date
calculation eliminates the hidden-tail repair. All four faces are now
covered, so the inactive-dummy escape of the previous canonical example is
not present. Changing these singleton signs by a terminal-only normalization
would be a different game, for which this review asserts nothing.

## 2. Parent equilibrium and unrestricted rigidity

At the displayed profile, player 3 quits at zero and each active player
quits there with probability one half, otherwise Never. Direct computation
gives U=B=(1,0,0,1). For an active player all replacements absorb at zero
because player 3 is fixed. Its whole response problem is therefore Quit0
versus Continue0, with endpoint pairs (1,1), (0,0), (0,0). Player 3's
prescribed payoff is its global reward maximum one, so its unbounded
deviations are capped as well. This is exact terminal Nash and gives the
same-profile uniform payoff through the same finite-horizon comparisons.

Before reading the author's proof I obtained rigidity using a first quantile
of the minimum active clock. The manuscript's last quantile of player 3 is
cleaner; I checked its complete estimates independently:

- Since B_3=1, player 3 fails to belong to the first finite coalition with
  probability at most e=E(μ), including all-Never. With
  ζ_n=max(e_n,1/n) and α_n=√ζ_n, the first K_n satisfying
  P(T_3≤K_n)≥1−α_n exists because e_n<α_n eventually. Minimality gives
  P(T_3≥K_n)>α_n, including the case K_n=0.
- Independence makes
  P(T_i<K_n)P(T_3≥K_n)=P(T_i<K_n≤T_3)≤e_n. Thus all active pre-K_n masses
  are at most α_n, and player 3's mass strictly after K_n, including Never,
  is at most α_n. Conditioning each active marginal separately on survival
  has exactly its pre-K_n mass as total-variation cost. Product coupling
  remains valid against any fixed unilateral replacement.
- With p_n=P(T_3=K_n) and conditional active atoms q_i^n, the prescribed
  approximation costs at most 12α_n from three altered marginals and
  2α_n from the anchor tail. Each response costs at most 8α_n from its two
  altered active opponents and 2α_n from the anchor tail. Hence the stated
  14α_n, 10α_n and 24α_n bounds are sound. If the anchor precedes K_n, all
  active payoffs in the conditioned profile and these responses are zero.

The resulting finite game has gaps

    Δ_0=1−2q_2, Δ_1=2q_0−1, Δ_2=2q_1−1.

Its unique Nash vector is (1/2,1/2,1/2). If q_0 is strictly above one half,
the second gap forces q_1=1, then q_2=1, then q_0=0; the reversed chain
excludes q_0 below one half. The same chain pins q_1; interior q_0 then
pins q_2. This includes all boundary faces, not only interior roots.

Player 0 can always obtain one by Quit0, so U_0≥1−e_n. Since its scaled
finite-game payoff is at most 2p_n, liminf p_n≥1/2. Every limit point in
the finite cube of (p_n,q^n) thus has positive p and is Nash in the finite
game. Uniqueness forces q^n→(1/2,1/2,1/2). Its pivot value is one, so
U_0≥1−e_n finally forces p_n→1. No limiting stopping-law payoff or cap is
used. This proves all three rigidity conclusions for arbitrary parent
approximate-equilibrium sequences, including dates escaping to infinity.

## 3. All faces and the original conditional-tail proof

For deletion 0, player 1's child payoff is minus its participation
probability, which tends to −1/2; Never yields zero. Deletion 1 gives the
same statement for player 2. Deletion 2 makes the pivot's child payoff its
participation probability, tending to 1/2, while Quit0 yields one. Hidden
tails can affect these payoffs only on a vanishing exceptional event: an
early active clock or failure of player 3 to be at K_n.

I checked both actual conditioning steps for deletion 3 in the frozen
manuscript. The copied-prefix deviation has gain multiplied by
A_n=∏_active P(T_i≥K_n), not by a deleted-player survival. This gives error
ε_n/A_n at the first actual child suffix. Continuing the same argument
through the current row multiplies by c_n=∏_active(1−q_i^n)→1/8, so the
post-row conditional child has error ε_n/(A_nc_n). All factors are positive
eventually; no off-path subgame perfection is assumed. Its pivot can Quit
immediately for one, which gives the claimed lower bound on v_0^n.

At the child root the pivot Continue endpoint is exactly

    2q_2^n+(1−q_1^n)(1−q_2^n)v_0^n.

Both cases with player 2 quitting are correctly included in the first
term, irrespective of player 1. Copying the tail after always Continuing
at this row is legal, and its gain is q_0^n(C_0^n−1) on the conditioned
profile. The limit lower bound is 1/8, contradicting its vanishing error.
Thus the original proof is complete even without the simplification below.

Finitely many omitted players suffice to pass to a fixed-face subsequence
if the claimed uniform constant failed. The preceding contradictions prove
the existence of c>0. There is no illicit compactness argument over all
clocks: only the finite cube and the finite set of face labels are compacted.

## 4. Independent adjacent-date simplification of the deleted-3 step

This is an alternative complete argument for the same difficult face. For
the child obtained by deleting 3, write F_0(t) for the complete pure-date
payoff and p_0(t) for its literal prescribed atom. For every profile,

    d_0 ≥ p_0(K)[F_0(K+1)−F_0(K)].

Indeed, replace only the mass at K by K+1, preserving every other atom and
Never. The payoff is affine in this one marginal, so the displayed right
side is the gain of one actual allowed deviation. Equivalently it follows
from the complete support-regret identity. No best-response attainment or
finite-support assumption is needed.

Condition only the two opponent clocks on being at least K. Then

    F_0(K)=1,
    F_0(K+1)=2q_2+(1−q_1)(1−q_2).

The first formula uses r_0=1 at every coalition containing 0. For the
second, an opponent-2 stop at K pays two; an opponent-1-only stop at K
pays zero; if neither stops at K, the pivot quits at K+1 and receives one
regardless of all future atoms. Thus the formula is exact even for
unbounded hidden tails and Never.

For the original unconditioned opponents the errors vanish by their small
pre-K_n masses. Parent rigidity gives F_0(K_n)→1,
F_0(K_n+1)→5/4, and p_0(K_n)→1/2. Consequently

    liminf_n E_−3(μ^n_−3)≥1/8

for EVERY parent sequence with E(μ^n)→0, without any hypothesis that these
children were approximate Nash. This removes both conditional-tail
equilibrium calls from the deleted-3 proof. It is not a different strategy
class theorem or a numerical optimization of the uniform constant c.

## 5. Exact tests and narrowly checked source comparison

The independently written checker
[CHECK_ADAPTIVE_FACE_OBSTRUCTION](../experiments/CODEX_NOETHER_SUPPORT__CHECK_ADAPTIVE_FACE_OBSTRUCTION.py)
was read before running and writes no files. Reproduction from math/:

    python experiments/CODEX_NOETHER_SUPPORT__CHECK_ADAPTIVE_FACE_OBSTRUCTION.py

It verifies the adjacent-date identity on sixteen hidden-tail pure pairs;
all 1,296 half-grid parent laws on {0,1,Never}, with all four full child
caps; and all 125 exact-parent hidden-tail variants in the author's test.
Complete response sets include date 2. Exact results:

    half-grid minimum parent+child errors: (1/4,1/2,1/2,1/4);
    hidden-tail minimum child errors:      (1/2,1/2,1/2,9/64).

The second computation agrees with the frozen manuscript. Neither finite
test supplies the unrestricted theorem. Checker SHA256:
`5688aec54b72ff5f2c73303d87ef88fd33502f0261361da8d4f90c1988e0087c`.

The narrow lookup confirms a genuine strengthening over the named records:

- SOCIAL_WEIGHT_REVIEW's proper-face chronology obstruction uses specified
  exact face sources and forbids nesting their laws. It does not quantify
  over all approximate equilibria of all faces and all outsider completions.
- FRECHET's common-quantile recombination theorem approximates all supplied
  independent mixtures and preserves their full caps; it does not produce
  a successful recombination or contradict the present restriction.
- SPINOZA's outsider-lift and host-release records, checked in the preceding
  fixed-face review, do not yield the adaptive all-four-face floor. The
  earlier TARSKI canonical example has an easy alternative dummy deletion;
  the present theorem explicitly removes that choice within this new table.

Named Lean sources inspected include
`quittingTerminalPayoff_copyLiteralRootStackThenDeviation_sub_eq` in
`UniformEquilibrium/Quitting/Root/LiteralPrefixDeviationTransport.lean`,
`quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime` in
`UniformEquilibrium/Quitting/Paths/BehaviorStoppingPayoff.lean`, and
`quittingGame_isUniformEquilibriumPayoff_of_terminalTargetAcceptance` in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
The first two validate the mathematical semantics of the supplied-prefix
and mixture operations, not a checked implementation of this new theorem.
The three-player existence declaration was read under its actual imports;
it supplies child existence, not law-preserving extension. No Lean build
was performed in this review.

An additional scoped source check is decisive for existence novelty.
`QuittingSingleAnchorMembershipReward` and
`exists_exactTerminalNash_and_uniformPayoff_of_singleAnchorMembership` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/SingleAnchorArbitraryCompletionEscape.lean`
already cover the central table with anchor 3. Its more general screen
`QuittingSingleAnchorInducedDominance` and declaration
`exists_exactTerminalNash_and_uniformPayoff_of_singleAnchorPoint` also cover
the nearby tables considered below: every anchor-containing reward is at
least 1−δ, every anchor-excluding reward is at most δ, and δ<1/8 implies
0≤δ<1−δ. These exact definitions and theorem hypotheses were inspected
independently after the coordinator pointed to the file. Hence neither
central nor open-neighborhood UE existence is a new class result. The
author's finite-tail exact profile remains a separate specified boundary
construction from that source's stationary realization. The new theorem
is the robust all-face obstruction for unchanged child laws.

## 6. Independent check of the proposed open-neighborhood attachment

The following was separately checked as proposed mathematics; final-byte
acceptance awaits the assembled candidate. Let the raw table change by at
most δ in sup norm, with Never still zero. Every prescribed payoff and every
fixed-response payoff changes by at most δ. Taking the supremum preserves
that bound for each cap; consequently each full exploitability changes by
at most 2δ. The same statement applies to every induced table. Hence the
all-face sum floor persists as c−4δ.

Nearby exact parent equilibria are produced, not merely assumed. Force 3
to Quit0 and let the active root vary over [1/4,3/4]^3. Each pure endpoint
changes by at most δ, so each Quit-minus-Continue gap changes by at most
2δ. The permuted field (Δ_1,Δ_2,−Δ_0) has original lower-face values −1/2
and upper-face values 1/2 in its corresponding coordinates. At δ<1/8 the
strict opposite signs persist. The continuous polynomial field therefore
has an interior zero by Poincare–Miranda. This is the hypothesis pattern of
`exists_rectangular_zero_of_strict_face_signs` in
`MathUE/Topology/RectangularPoincareMiranda.lean`, inspected directly.

Those active mixed strategies are optimal against every behavioral
replacement, because the anchor absorbs at zero. For the anchor, current
Quit pays at least 1−δ. On Continue, if an active player quits at zero its
reward is at most δ. Otherwise, with probability at most (3/4)^3=27/64,
any later Quit earns at most 1+δ; Never earns zero on that cylinder. Thus
EVERY late/Continue response has payoff at most 27/64+δ, strictly below
1−δ at the stated radius. This proves full exact Nash in the perturbed
game. The same immediate-absorption and strict anchor cap bounds give a
uniform-equilibrium payoff; no uncertain infinite-deviation convergence is
needed for this finite law.

Therefore δ<min(c/8,1/8) indeed gives an open family of solved games with
an all-face floor at least c/2. This remains a general Fin4 statement, not
a canonical-singleton class or a normalization-invariant assertion.

## 7. Accepted scope

The original source hash at the top is accepted with no unresolved
mathematical objection. The obstruction closes adaptive unchanged-child
extension, even with omniscient face/child/target/outsider selection. It
does not exclude changes or independent recombinations of surviving laws,
a compiler using positive-global-gap ancestry, or the general UE
conjecture. The parent has zero global debt, and this theorem must not be
presented as a cardinal-minimal counterexample.

No author note, export, Lean source, or shared index was edited.

## 8. Final-byte acceptance of the combined packet

The complete final manuscript
[ADAPTIVE_CHILD_EQUILIBRIUM_EXTENSION_NO_GO](../exports/ADAPTIVE_CHILD_EQUILIBRIUM_EXTENSION_NO_GO.md)
was read through EOF and accepted at SHA256
`358787dd7cac784c8104244bc2431844d414c7bda28e10851a04d8bd7c00da1a`.
There is no unresolved mathematical objection to these exact bytes.

The final text preserves the accepted quantile/finite-cube proof and all
unrestricted behavioral quantifiers. Its exact adjacent-date formula

    F_0(K+1)−F_0(K)=s_1s_2(q_2−q_1+q_1q_2)

correctly cancels every pre-K opponent absorption before conditioning;
the mass transfer then has the stated gain tending to 1/8. This replaces
the valid but unnecessary child-tail-Nash proof without weakening the
result or losing hidden clocks. The three other child liminf bounds remain
unchanged. The open-neighborhood sum floor, permuted strict face signs,
complete finite-tail anchor cap, and same-profile uniform conclusion are
exactly the independently checked statements of Section 6 above.

The final choice ρ=min(c_0/8,1/8), c=c_0/2 is correct. Uniform positive
scaling by one half preserves every Nash comparison and scales all caps,
debts, and all-face gaps by one half while keeping Never zero. It does not
claim the corresponding property for translations. The explicit credit to
existing single-anchor existence theorems survived packaging, so no new
UE class is asserted. The only substantive novelty is the robust adaptive
unchanged-child obstruction inside already solved games, together with its
actual-profile rigidity and finite-tail verification.

Acceptance covers this final combined packet in addition to the original
primary-source hash at the top. The independent checker results and their
limitations remain as recorded in Section 5. No Lean build or export edit
was performed.
