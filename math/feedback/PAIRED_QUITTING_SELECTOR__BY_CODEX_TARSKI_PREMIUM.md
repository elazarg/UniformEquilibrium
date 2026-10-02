# Independent audit of the asymmetric paired selector

Reviewer: CODEX_TARSKI_PREMIUM.

Verdict: PASS as ordinary mathematics for the explicit Fin4 raw class,
its exact finite-cap identities, the canonical normalization, the selected
late pivot repair, the rational residual certificate, and the stated extension
to every even number of players at least four. No mathematical objection
remains from this review. This is not a Lean check or an export decision.

Source reviewed completely:
[PAIRED_QUITTING_SELECTOR.md](../gpt/PAIRED_QUITTING_SELECTOR.md), SHA256
`784fb8d61e6818b4e1d21784b89a7472d124f10afa274e4f12d4263701f7a4fa`, and
[its response](../gpt/PAIRED_QUITTING_SELECTOR_RESPONSE.md), SHA256
`5747cd443d2d7825f2166104de54cf2e326eba4444063082cea79cadd74f8328`.
The main proof was reconstructed independently. The archive's numerical runs
are not used as evidence for any universal statement.

## 1. Exact claim and source quantifiers

Players independently sample complete stopping laws; Never pays zero and all
behavioral replacements are allowed. With pairs {0,2} and {1,3}, each player's
singleton s lies in [9/10,11/10], partner singleton b and opposite-pair passive
reward d in [-1/10,1/10], own-pair reward P and either opposite singleton
reward in [19/10,21/10]. Joining a nonempty subcoalition of the other pair
pays at most s+1/50. Other reward coordinates are arbitrary.

The theorem constructs ONE four-dimensional hazard vector, one exact
two-periodic all-suffix Nash profile, and its exact-cap finite selectors.
It supplies the original table and the profile from raw inequalities; neither
a root sequence nor original-game caps are assumed. The same claim holds
for any cyclic list of disjoint pairs covering an even player set, under
the corresponding inequalities for every other pair.

## 2. Simultaneous root and both action comparisons

Write h for the partner's hazard, u,v for the other pair, and

    X=s+h(P-s),      Y=s+h(P-b)/(1-h),
    R=u(1-v)a_k+(1-u)v a_l+uv d,
    c=(1-u)(1-v),    H=Y-R-cX.

Active Continue equals h b+(1-h)Y=X, so active indifference is exact for
every candidate. Quiet Continue equals Y precisely when H=0. The relabeling
F_j=H_{partner(j)} is correct: the opposite faces belong to h, not to the
player's own hazard.

For fixed h, H has positive coefficients on s,P and negative coefficients
on b,a_k,a_l,d throughout the specified hazard rectangle. It is affine in
each reward and separately affine in u,v. Its extrema therefore reduce to
the displayed corners without an unproved optimization claim. An independent
Fraction enumeration of all 512 corners exactly reproduced all eight
displayed face bounds. In particular the whole lower face is negative and
the whole upper face is positive. Their hypotheses are simultaneous for
all four players; rectangular Poincare--Miranda supplies an interior common
zero even for fully asymmetric table choices.

The inactive Quit endpoint is at most s+(1-c)/50≤s+3/200, whereas
Y-s≥1/55. Thus every inactive Continue inequality is strict. Unspecified
coordinates cannot enter these comparisons: prescribed absorption involves
one active pair, and one deviation adds at most its single inactive owner.

For direct Lean reuse there is a small interface detail, not a mathematical
gap. `Math.Topology.exists_rectangular_zero_of_strict_face_signs` asks for a
globally continuous field, whereas H has a denominator 1-h. Use the cleared
field (1-h)H, then apply the partner relabeling. It is polynomial globally,
has the same signs and zeros on the rectangle, and matches that interface.

## 3. Complete deviations, finite caps, and pivot repair

Both phase inequalities telescope against an arbitrary behavioral deviator.
All opponents retain their positive scheduled hazards, so their survival
after K complete periods is D_i^K with D_i=∏_{j≠i}(1-q_j)<1. This discharges
the terminal remainder uniformly over every deviating law, including Never;
it does not identify a behavioral response arrow with a temporal Nash arrow.
The fixed profile has a uniform bound on expected absorption time even under
deviation, so the direct finite-average argument is valid for signed rewards.

The truncation claim is EXACT. At the cycle boundary v_i≥s_i≥0. A finite
response before the cutoff sees identical opponent laws in the infinite
and censored profiles. A response after the cutoff, including Never, is
bounded by the legal infinite-profile response which waits to the cutoff
and then resumes prescribed play: the conditional comparison is s_i or 0
versus v_i. Finally the first active date lies inside every K≥1 truncation
and attains v_i. Therefore B_i^K=v_i, not merely B_i^K≤v_i. Periodic renewal
separately gives U_i^K=(1-C^K)v_i. These arguments control the same literal
independent laws and the whole cap vector.

The selected pivot repair is also valid. All its active dates before the
cutoff attain its cap; moving its Never mass to its last active date makes
its complete law a mixture of best responses. For another player, the
coupling event requires original pivot Never and survival of its two other
opponents through the preceding K-1 periods. Its probability is at most
(1-q_0)D_i^{K-1}. The original 4M bound pays separately for the prescribed
payoff and cap changes. No claim of unchanged nonpivot caps is needed.

## 4. Normalization and rational certificates

The terminal-only shifts leave Never at zero, so they are not globally
affine transformations of finite-profile payoffs. The source explicitly
avoids that false identity. Under the infinite periodic profile EVERY
unilateral deviation absorbs almost surely. Affine transport of exactly
those payoff comparisons proves Nash in the transformed table. The cap
truncation argument is then rerun in that table using vhat_i≥shat_i≥0.
The relative-open canonical region has dimension 56, obtained by fixing
the original four singletons to one and freely varying the other entries
within strict inequalities.

For a rational approximate zero the local Bellman error occurs once per
period, at the quiet phase. The prescribed cycle residual is H_i multiplied
by either 1 or the preceding pair's survival; the cap residual has the
analogous opponent-survival coefficient at most one. Summing these errors
gives exactly the two denominators 1-C and 1-D_i in the stated bound. The
tail cap max(s_i,0) is below the candidate initial v_i. Rational-grid
termination follows from continuity near the proved interior exact zero.

Independent arithmetic reproduced the reference H fraction verbatim and
verified that the sixty-date rational bound is below 1817/10^11 and hence
below 10^-6. This is finite arithmetic only; the common-zero and cap proofs
above establish the general class claim.

## 5. Every-even-size extension

For n=2m, each other pair induces T_B(z)=R_B+c_B z. On the lower h face
the Fin4 estimates give T_B(X)>Y>X for EVERY pair. Since all maps are
increasing, every composition of the m-1 maps remains above Y. On the upper
h face, X≤8/5 and every map preserves the upper bound 21/10; but Y≥27/10.
Thus the partner-relabeled field again has strict opposite face signs.

For quiet incentives, uv/(u+v-uv)≤1/3 whenever 0<u,v≤1/2. The conditional
passive absorption mean is therefore at least 37/30. Starting from X≥s,
every intermediate value remains at least s. At a quiet pair, Continue
exceeds s by at least (2/15) times that pair's absorption probability,
whereas Quit exceeds s by at most (1/50) times the same probability.
This verifies every phase, not only the phase immediately after one's own.
Deleted survival per complete cycle is at most (99/100)^(n-1), so the same
complete-deviation and exact-cap truncation proofs apply. Odd player counts,
unpaired outside players, and arbitrary partitions with larger blocks are
not claimed by this extension.

## 6. What is new relative to the nearest inspected work

[DESCENDANT's corpus note](../notes/CODEX_DESCENDANT__TRACKED_CORPUS_ALTERNATING_PAIR_EQUILIBRIA.md)
already has simultaneous Poincare--Miranda selection for four asymmetric
tables and full-dimensional open balls around them, exact alternating-pair
behavioral equilibria, and finite upper selectors. Neither asymmetry, an
open class, alternating pairs, nor Poincare--Miranda is new here. Its finite
cap conclusion is a geometric error estimate; it does not state B_i^K=v_i.

The production `FourPlayerPairedSingleton.periodTwoProfile_isExactTerminalNash`
and `periodTwo_isUniformEquilibriumPayoff` in
`UniformEquilibrium/Quitting/Examples/BlockPair/FourPlayerPairedSingletonPeriodTwo.lean`
already solve the specific Solan--Vieille table by the same two active pairs.
That table has own-pair participant reward equal to its singleton, as
`SolanVieilleBoundary.boundaryReward_pair_eq_one` in
`UniformEquilibrium/Quitting/Examples/SolanVieilleBoundaryTable.lean` shows.
The current class requires P_i>s_i. Positive playerwise scaling and terminal
translation preserve this strict-premium distinction. The current rectangle
is not another parameter presentation of that boundary table.

Thus the supported additional content is the EXPLICIT raw reward rectangle
(including arbitrary unused coordinates), its simultaneous producer,
the exact complete-cap truncation ledger, and the even-size row adapter.
The rectangle is also not contained in the four stated corpus balls: those
lie inside a reward cube of radius approximately one, whereas current pair
coordinates are at least 19/10. No claim that the new rectangle contains
those old balls, or that it lies outside every other solved class, follows.
The general periodic cap lemma is elementary and should be described as
such, not as a new universal cap-preserving compression theorem.

Other source declarations inspected were the rectangular zero theorem in
`MathUE/Topology/RectangularPoincareMiranda.lean`,
`finiteMenuFullEarlyAbsorption_of_terminalProfiles_liveMassZero` in
`UniformEquilibrium/Quitting/Terminal/TerminalProfileFiniteEarlyAbsorption.lean`,
and the stationary-or-Q alternative in
`UniformEquilibrium/Quitting/Classification/LCP/StationaryExistence.lean`.
The last is an alternative, not automatic coverage of the new rectangle.
No complete classification of that rectangle against every singleton-matrix
producer was undertaken or is claimed.

A minimal self-contained candidate is preserved in
[the paired-cycle note](../notes/CODEX_TARSKI_PREMIUM__ASYMMETRIC_PAIRED_CYCLE_EXACT_CAP_SELECTOR.md).
No source manuscript, production file, shared index, or export was changed.
