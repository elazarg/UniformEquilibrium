# Independent review of the signed local cap collar

Reviewer: CODEX_LOCAL_COLLAR_REVIEW. Date: 2026-10-25.
Mathematical verdict: **PASS**. No unresolved objection.
This reviews ordinary mathematics, not a Lean check or an export approval.

Artifact: `math/notes/CODEX_GLOBAL_SYSTEMATIC__LOCAL_CAP_COLLAR.md`.
Complete 305-line artifact SHA256:

`0a579ac7f2a3b06fd74daad481637c84f844ed21623bbd865556ce40926d1406`.

## Claim and semantic scope

For native own-singleton, live and Never rewards zero, let a probability
weight z supported on S have strictly positive weighted singleton and
participant-pair drifts. Suppose the common nonpositive forced-Quit
sublevel on S consists only of the zero root. Then a positive table
constant delta satisfies max_S B >= delta*(1-nu) for every actual profile.
Individual supported caps and participant pairs may have either sign.

The supported zero face is absent from the absorbing semantic closure.
The augmented inequality also excludes nontrivial zero-cap tuples with
positive absorption. All private stopping laws and all complete unilateral
replacements, including Never, are priced. No root Nash property, actual
realization of a closure point, or minimum-source ancestry is assumed.

The note correctly limits its conclusion to tables passing the raw tests.
It does not produce a UE, exclude every boundary face, exclude an actual
global partial-Nash minimum, or make observer Nash into full Nash.

## Signed-cap proof audit

1. The singleton-event probability loss is at most s^2 and multiple-
   opponent probability at most s^2/2. Both expansion errors are therefore
   at most (3M/2)s^2. The chosen rho gives zQ >= kappa*s and
   zP >= gamma*s/2, where kappa=mu/2. Also Q_i >= -Ms and |P_i|<=Ms.

2. Root isolation gives a positive minimum d0 on the compact root set
   s>=rho. Thus max_S B<=eta=d0/2 forces s<rho. Writing w=zB gives
   kappa*s<=w<=max_S B, while the weighted negative cap part is at most
   Ms. Consequently sum z_i|B_i| <= (1+2M/kappa)w=Cw and, on S,
   B_i <= [(1+M/kappa)/z_min]w=Aw. These estimates do not assert
   individual nonnegativity and remain valid when some caps are negative.

3. The full cap recursion bounds the next caps by
   B_i^+ <= (B_i-P_i)/H_i <= 2(B_i+Ms) <= Kw.
   The second inequality is valid even with a negative numerator, since
   B_i+Ms>=0 and H_i>=1/2. The small weighted-cap threshold puts the next
   actual tail inside the larger collar before any weighted sign is used.
   Reapplying the collar there gives v=zB^+>=0 and sum z_i|B_i^+|<=Cv.

4. Signed continuation transport gives
   w >= gamma*s/2 + v - s sum z_i|B_i^+|
     >= gamma*s/2+(1-Cs)v.
   Since Cs<=1/2 and w<=gamma/(4C), this implies
   0<=v<=w-(gamma/4)s. The induction invariant is max_S B<=eta together
   with w<=delta, not a decreasing maximum cap. All subsequent laws are
   well-defined because s<rho<1. Thus no unsupported positivity or
   monotonicity premise occurs in the induction.

5. Telescoping gives total hazard <=4w_initial/gamma and hence
   1-nu<=4b/gamma. With b<=delta<=gamma/8, absorption is at most1/2,
   and the advertised global inequality follows since delta<=gamma/4.
   If b>delta it is immediate. Root isolation also gives b>=0 at the
   initial root. The strict bound for actual absorbing profiles and its
   weak bound after closure are therefore correctly distinguished.

6. The augmented limit is sound. Every response is zero if all opponents
   use Never, so |B_i|<=M*(1-product_(j!=i)N_j)<=M*(1-nu).
   The analogous prescribed-payoff bound is immediate. At nu=1 all N_i
   equal1 and every payoff and cap is zero. This justifies the full tuple
   assertion, rather than only a statement about supported coordinates.

The native complete-cap recursion matches
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max`
in `UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`.
Literal prefixing matches `quittingTerminalSemanticPair_rootThenContinuation`
and `quittingTerminalSemanticPrefix` in
`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`.
These declarations do not implement the new collar theorem. No Lean ran.

## Exact strict examples and original-level bridge

For the calibration, (9,7,0,8)*Gamma=(6,11,6,6). Positive supported pairs
supply zJ>0, and the positive row0 anchor plus a positive pair into0
supply root isolation. M=10 bounds the displayed table. Thus the entire
independent-premium box has the sparse-face exclusion stated in (8),
without a premium-independent constant as the premiums tend to zero.
The older global weighted-Quit test fails for every weight: its four
necessary inequalities force sum v_i<21*epsilon/4<=21/40<1.

For the signed example I independently expanded every Quit polynomial.
The two opposite-pair products a0*a2=6/7 and a1*a3=3/5 force the common
nonpositive sublevel to be {0}. Exact multiplication gives
zGamma=(16,23,2,10)/30 and zJ=(1/20,1/30,3/50,1/210).
Every row has a negative participant pair, so no nonempty support passes
the former individual-positive-pair test. I independently recomputed all
four vectors in (11); their weighted sum is exactly
(-166,-166,-166,-166). Thus every weight fails the older global test.
This is strict enlargement, not merely a different choice of old weights.

The openness argument is valid. Strict zJ controls all sufficiently small
nonzero roots uniformly; compactness controls the remaining roots.
Strict singleton drift, the negative participant pairs and the strictly
negative four-test coefficient vector persist under small perturbations.
Passive nonsingleton entries do not enter these tests and remain arbitrary
finite data. Their magnitudes change only numerical collar constants.

For ell>=0, every finite deadline absorbs, so its original offer is ell_i
plus its native offer. Bounded convergence makes native Never the limit
of finite deadline offers. Original Never equals native Never plus
ell_i*(1-opponentNever), hence is at most ell_i+B_i(native). This proves
B(original)=ell+B(native) for every profile. Prescribed payoff translates
by ell*(1-nu), and both vectors translate by ell on the absorbing carrier.
The nonnegative-level assumption is essential: with negative ell and all
opponents Never, original Never0 can dominate every finite own-singleton
offer ell. The artifact neither shifts literal Never nor drops this sign.
Positive levels together with the open native class indeed give an open
full-dimensional class of original tables.

## Missing-hypothesis and source checks

Without singleton drift, two players with passive singletons -1 and joint
rewards1 satisfy the pair and root-isolation tests. Independent uniform
clocks on T dates absorb and have caps1/T. Without root isolation, three
players with passive singletons1, participant pairs1, passive pairs-1 and
grand rewards-1 have both positive weighted drifts. An empty date followed
by everyone quitting gives all caps0 despite absorption. These exact
controls confirm that the two other tests cannot simply be discarded.

The incoming boundary tail belongs to the absorbing semantic closure, so
no tail realization or full Nash assertion is needed for the application.
The calibration excludes B0=B1=B3=0; the signed example excludes the
all-zero face. Other source faces and the actual-minimum branch remain
open. The source does not supply these reward tests for arbitrary games.
Keeping this as an internal boundary theorem, rather than exporting it as
a new UE class or global source closure, accurately reflects its scope.
