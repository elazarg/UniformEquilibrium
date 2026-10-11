# Bounded check of balanced membership-ratio clocks

Verdict: PASS for Sections 1–3 and 6, as ordinary mathematics. No mathematical
objection found. This is not a Lean check, an exhaustive novelty audit, or an
admission to exports.

The checked source is `CODEX_EMMY_BOX__MEMBERSHIP_RATIO_CLOCK_BALANCE.md`,
whole-file SHA256
`4ac5d975aedf308712260acad7d1880f611d7f65285f20f834426997b0439b55`.
Section 7's additional named-source comparisons and the separately proposed
incoming-pair completion extension are outside this review.

## 1. Claim and agency checked

For arbitrary finite n>=2, arbitrary real own rewards s_i and background
arrays g_i, the literal membership identity, M_i>1 and weak rate balance
produce the displayed private stationary clocks. They form an exact terminal
Nash equilibrium against every complete independent unilateral replacement,
including Never. The same profile yields its fixed terminal payoff uniformly.
Strict balance and nonzero background expectations give a full-raw local IFT
extension. Separately, the rational four-player completion excludes EVERY
initial-sure-quitter exact terminal Nash profile, for every common M>=2,
while retaining the explicit interior stationary equilibrium.

The correlated, public, finite-menu and bounded-controller interpretations
are not used. Opponent date-coalition draws are the independent stationary
ones induced by the actual private clocks.

## 2. Exact cancellation, boundary and raw Jacobian

I reconstructed product p=k and every deleted continuation alpha_i=a_i.
Weak balance permits p_i=1 but never alpha_i=1; consequently at least two
players have positive hazards. The stated Q and B identities give

    (1-alpha_i) Q_i-B_i=[M_i(1-alpha_i)-1] gbar_i=0.

Thus the payoff of every pure finite deadline is Q_i, and Never has the
same payoff. Mixing over complete private deadlines proves the full cap,
including an inactive player's deviations. No payoff sign is needed. The
opponent geometric tail bounds terminal/finite-average differences uniformly
over the deviator's complete law, so the same profile and payoff work for
all accuracies.

As an independent exact boundary test I used n=3, p=(1,1/2,1/3), hence
alpha=(1/6,1/3,1/2) and M=(6/5,3/2,2), with s=(-7,3,0).
For every nonempty opponent set of binary mask m, set
g_i(A)=(-1)^(m+i)(i+2)(m+1)/3. Exact rational evaluation gives
Q=Never=(-17/5,-2,4), and the same values at deadlines 0,1,7. This tests
both equality balance and signed rewards; it is not a substitute for the
general proof.

For strict balance, differentiating the self-consistent field kills the
derivative of gbar at the center. Its Jacobian is
diag(M_i alpha_i gbar_i) (ones-I) diag(1/p_i). The determinant in (6)
therefore has the stated sign and factor n-1. The IFT conclusion really is
open in all raw recipient-coalition coordinates; membership identities need
not persist in that neighborhood. Interior hazards and opponent contraction
do persist.

The nearby semantic consumers inspected are
`isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts` and
`isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts` in
`UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean`.
The alpha=1 boundary branch of that compiler is irrelevant here: every
deleted alpha is strictly less than one even at weak balance.

## 3. Exhaustive owner faces independently reconstructed

I formed every face gain directly from the raw g table, independently of the
listed support conclusions. Writing f_j for the join-minus-Continue gain
after dividing by the positive M-1 gives the following complete polynomials.

Owner0:

    f1=3+13q2+q3-(167/10)q2q3,
    f2=-1+2q1-2q1q3,
    f3=-1+17q1+9q2-(247/10)q1q2.

All background gains for player1 are positive, then those for player3 are
positive, and player2 has gain -1. This gives the unique (1,0,1) face point.

Owner1:

    f0=3-(27/10)q2-4q3+(77/10)q2q3,
    f2=-1+2q0(1-q3),
    f3=-1+17q0+(13/10)q2-17q0q2.

If q2>0, f2>=0 forces q0>=1/2 and q3<=1/2. Both q2-endpoints of f0
are positive, so q0=1; f3>=3/10 then forces q3=1, a contradiction.
The remaining response cycle uniquely gives (q0,q2,q3)=(1/17,0,3/4),
with the omitted player's f2=-33/34. Boundary and fully mixed cases are
included, rather than discarded by numerical root enumeration.

Owner2:

    f0=-1+(13/10)q1+17q3-(133/10)q1q3,
    f1=-1+17q0+9q3-(247/10)q0q3,
    f3=3+5q0-(27/10)q1-5q0q1.

Positive raw player3 gains force q3=1, then q0=1, then q1=1. This is
the unique face point.

Owner3:

    f0=-1+17q2-12q1q2,
    f1=-1+5q0+9q2-(127/10)q0q2,
    f2=-1+4(1-q0)(1-q1).

If q0>0, the q2=1 branch forces q1=1 and contradicts f2>=0. In the
remaining mixed branch, f2=f0=0 gives exactly the substitutions stated in
the source. The resulting f1 numerator is positive on [0,3/4], contradicting
q1<=3/4. Thus q0=0, and the unique cycle point is (0,3/4,1/9), with
f0=-1/9. This explicitly checks the potentially missing all-mixed support.

Exact rational reconstruction of the owner's (alpha,gbar,Q-B) at M=2 gives

    owner0: (0,       -1,      -1),
    owner1: (4/17,    -33/68,  -1/4),
    owner2: (0,       -1,      -1),
    owner3: (2/9,     -67/120, -121/360).

Every absent reward is nonnegative. Therefore the owner's complete Never
replacement has payoff at least B, independently of EVERY off-path
continuation. These strict negative Q-B gaps rule out actual terminal Nash
with an initial sure quitter, not merely a selected stationary owner face
or a particular punishment. Multiple simultaneous sure quitters are already
included in this argument.

For every M>=2 all face gains have the common positive factor M-1, so the
face correspondence is unchanged. The four owner gaps in (11) stay strictly
negative. The asserted whole-family, whole-owner quantifiers are valid.

## 4. Perturbation scope and significance

The four gbar expressions in Section 6.6 match direct expectation. They
are positive, including gbar2=q(p^2-q)>0, so the full-raw IFT extension
applies. Compactness and closedness of the finite face Nash graphs justify
persistence of the strict Q-B inequalities near the center. Since some
absent rewards are zero, the author correctly does NOT infer the stronger
arbitrary-future Never argument on an unrestricted open reward neighborhood
without another bound. Within the nonnegative-absent cone it survives.

This is an actual raw-table producer and a rigorous whole-sure-owner
separation, not a conditional strategic verifier or a bad-branch example.
The bounded review does not determine coverage by every other implemented
or accepted producer. In particular, it does not assert a new surviving UE
counterexample restriction: these tables have the explicit equilibrium just
proved.
