# Signed single-column jackpot equilibria

## 1. Exact finite-data question and theorem

Let I be any finite player set of cardinality n>=2. A finite nonempty quitting
coalition S absorbs at reward r(S) in R^I; perpetual continuation and live
dates pay0. Randomization is private and independent. Deviations replace one
player's ENTIRE behavioral law, including arbitrary finite deadlines and Never.
All payoff claims are in expectation.

Fix arbitrary singleton entries and put

    s_i=r_i({i}),
    Gamma_ii=0,       Gamma_ij=r_i({j})-s_i for j!=i.

Assume Gamma is invertible. Choose ONE recipient a and ONE sign sigma in{-1,1}
for which v=sigma*Gamma^-1 e_a is strictly positive in every coordinate. No
sign condition is imposed on the other inverse columns. Choose ONE coalition
S* containing a, with |S*|=d+1>=2, and one coefficient A>0.

**Theorem.** For every finite R>=0 there exists finite M0 such that, for every
M>M0, EVERY original raw table with the fixed singleton rows and

    r_a(S*)=sigma*A*M+c,       |c|<=R,
    |r_i(S)|<=R for every OTHER nonsingleton coordinate(S,i)    (1)

has an exact terminal Nash equilibrium with independent stationary hazards
strictly between0 and1. Its actual terminal payoff is a uniform-equilibrium
payoff, with that SAME profile working for every accuracy over all sufficiently
long finite horizons. Only one reward coordinate grows. All other participant,
passive, triple and grand coordinates in(1) are arbitrary inside their box.
No strategic witness, continuation value, root or payoff target is an input.
There is no sign assumption on own singleton rewards. For sigma=-1 the
selected coordinate is a large NEGATIVE participatory penalty, not a positive
jackpot. Utilities and Nash ordering are not reversed.

The threshold and leading hazard asymptotics are uniform over compact sets
of singleton data and A inside the displayed invertibility/positive-column
region, with the sign, recipient and coalition fixed. This is not arbitrary-game
existence or a claim that every invertible comparison matrix has a positive
inverse column.

In fact a scale-thick raw region is available: for the fixed singleton data,
A, recipient and coalition, there exist kappa>0 and M1 such that(1) may be
replaced by

    |c|<=kappa*M^(1/d),
    |r_i(S)|<=kappa*M^(1/d) for all OTHER nonsingleton coordinates,
    M>M1.                                                (1a)

This is one unbounded original-table region, not only bounded perturbations
of an asymptotic ray. The stronger bounded-data limit below refers to(1),
not to arbitrary parameters varying throughout(1a).

## 2. Exact endpoint polynomial and explicit leading root

For stationary hazards q, let Q_i(q) be the immediate forced-Quit endpoint,
B_i(q) the terminal stopping contribution received when i Continues and an
opponent quits at that date, and alpha_i=product_(j!=i)(1-q_j). The stationary
Continue/Quit indifference field is

    H_i(q)=(1-alpha_i)Q_i-B_i.                       (2)

The selected large coordinate contains its recipient a. It therefore enters
Q_a only, at opponent coalition S*\{a}, and never B_a or any other recipient's
payoff. Put t=M^(-1/d), q=t*z. Dividing(2) by t gives the exact polynomial
extension

    Phi(t,z)=sigma*A*P(z)*e_a-Gamma*z+t*E(t,z,c,b),  (3)
    P(z)=(sum_(j!=a)z_j)*product_(j in S*\{a})z_j.

Here b denotes all the other bounded nonsingleton data. The polynomial E is
uniformly bounded with all derivatives on fixed compact sets of(t,z,c,b).
To check the pole, the selected term is

    (1-product_(j!=a)(1-t*z_j)) * sigma*A*t^(-d)
       * product_(j in S*\{a})(t*z_j)
       * product_(j notin S*)(1-t*z_j).

It is divisible by t, and after division its constant term is sigma*A*P.
The bounded data contribute at linear order -Gamma*z and otherwise at
order at least t. Thus(3) is an exact identity, not a formal asymptotic claim.

P is positive on the positive orthant and homogeneous of degree d+1.
Since v=sigma*Gamma^-1 e_a>0, define

    rho=(A*P(v))^(-1/d),       z*=rho*v.            (4)

Then A*P(z*)=rho and Gamma*z*=sigma*rho*e_a, so Phi(0,z*)=0.
This is an explicit positive limiting root. It does not require all columns
of Gamma^-1 to be nonnegative or a radial topological selection.

## 3. Nondegeneracy from Euler's identity

The derivative at the limiting root is the rank-one perturbation

    J=sigma*A*e_a*(grad P(z*))^T-Gamma.

The determinant lemma and Euler's homogeneous identity give

    det J=det(-Gamma)*(1-A*grad P(z*) dot v)
         =-d*det(-Gamma) !=0.                       (5)

The two signs cancel because Gamma^-1 e_a=sigma*v. Indeed
z*=rho*v and A*P(z*)=rho, hence
A*grad P(z*) dot v=A*(d+1)*P(z*)/rho=d+1.
Consequently the implicit-function theorem produces an exact nearby root
z(t,c,b)>0 of Phi=0 for all sufficiently small t>0, uniformly on the compact
bounded-data box. Uniformity can be seen by applying the parameter IFT at
every point(0,z*,c,b) and taking a finite subcover; local solutions agree in
the common small ball by uniqueness. Equivalently, the common invertible
J and uniform derivative bounds give one uniform quantitative contraction.
For compact singleton/A data the same argument applies because z* and J
vary continuously and remain positive/invertible on that compact set.

Thus q=t*z(t,c,b) is an ACTUAL all-interior stationary root of every H_i=0.
In particular it is not an approximate local Nash point with an unpriced
conditional tail error.

For(1a), replace every bounded nonsingleton coefficient by b_j=e_j/t,
including the selected residual c. The divided field(3) remains polynomial
in(t,z,e): a bounded-reward monomial from a nonsingleton coalition has
degree at least2 in q before division by t, so after this substitution
its t exponent is nonnegative. The selected residual likewise contributes
order t^(d-1)*e, which is nonnegative because d>=1. At(t,e)=(0,0) the
limiting root and Jacobian are exactly(4)--(5). The ordinary parameter IFT
therefore supplies all solutions whenever t is sufficiently small and
every |e_j| is sufficiently small. Choosing one kappa inside that parameter
neighborhood proves(1a), with the same full-agency consumer.

For fixed bounded data in(1), z=z*+O(t). All nonselected recipients have
U_i=Q_i=s_i+O(t); the selected recipient has

    U_a=s_a+sigma*A*product_(j in S*\{a})z*_j+O(t).  (7)

The selected reward's probability is small, but its payoff contribution
does not vanish. Its sign may be positive or negative; it balances the selected
player's indifference conditions without changing all other players'
singleton-scale payoffs.

## 4. Full terminal and uniform consumer

Every player has a proper opponent, since all n>=2 hazards are positive.
Let U_i be the actual stationary terminal value. First-step evaluation gives

    U_i=[q_i Q_i+(1-q_i)B_i]/[1-(1-q_i)alpha_i].

Equation H_i=0 gives B_i=(1-alpha_i)Q_i, hence U_i=Q_i and
B_i+alpha_i U_i=U_i. Iterating this Bellman equality shows that every pure
finite deadline against the stationary opponents earns exactly U_i, and
Never earns B_i/(1-alpha_i)=U_i. Any complete private behavioral replacement
is a distribution on finite first-Quit dates and Never, so its payoff is also
U_i. This proves unrestricted exact terminal Nash, not only stationary
best replies. Opponent absorption has a geometric tail under EVERY such
replacement. Terminal and finite-average payoffs therefore converge
uniformly over all replacements. The same fixed profile and its actual
payoff give original uniform equilibrium.

The relevant inspected Lean consumers are
`isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts` and
`isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts`
in `UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean`.
They are existing consumers, not implementations of the new raw producer.

## 5. Early exact tests and scope of the sign relaxation

An exact three-player calibration checks the pole, signs and full cap at a
moderate reward value, independently of asymptotic IFT. Put all own singletons1
and take

    Gamma=[0,1/2,1/2;1,0,-1;1,-1,0],
    Gamma^-1=[1,1/2,1/2;1,1/2,-1/2;1,-1/2,1/2].

Set every nonsingleton reward coordinate to1 except r_0(01)=1+M.
For equal hazards q, direct expansion gives

    H0=q(1-q)[M*q*(2-q)-1],       H1=H2=0.

For M>1 choose q=1-sqrt(1-1/M). At the rational value M=4/3 this gives
q=1/2 and actual full Nash payoffs(4/3,1,1). For player0, after subtracting
the common finite-terminal constant1, Quit=1/3, Continue stopping=1/4,
opponent absorption=3/4; thus both endpoint and Never values are1/3.
For players1,2 those shifted quantities are0. Every unilateral replacement
still absorbs surely because the two other clocks are proper, so the common
finite-terminal shift is constant under EVERY comparison. This is only an
exact mechanism calibration in a solved player count, not new class coverage.

Strict positivity of only one inverse column is genuinely weaker algebraic
data. For example

    Gamma=[0,1,0,0; 1,0,-1,0; 0,1,0,-1; 1,-1,0,0],
    Gamma^-1=[1,0,0,1; 1,0,0,0; 1,-1,0,1; 1,0,-1,0].

Its determinant is-1, its column0 is the all-one vector, and its inverse
has negative entries. This algebraic example establishes the sign distinction
only; it is NOT claimed to separate all implemented game-theoretic producers.

At the hard paired singleton matrix on cyclic labels, mate i+2, one has

    Gamma=[0,-1,3,-1; -1,0,-1,3; 3,-1,0,-1; -1,3,-1,0],
    Gamma^-1=(1/15)[2,3,7,3;3,2,3,7;7,3,2,3;3,7,3,2].

For recipient0 and S*=I, write w=(2,3,7,3), so Gamma*w=15*e0.
The leading root in(4) is equivalently

    z*=h*w,        h=(5/(273*A))^(1/3),

because P(h*w)=819*h^4. Thus a family with ONLY r_0(I) growing, the other
three grand rewards fixed negative and all proper rewards fixed, has an
explicit all-interior small stationary component for all sufficiently large M.
This does not solve the corresponding fixed negative-grand table; a varying
reward-table limit is not an equilibrium construction for that fixed game.

If the positive-column hypothesis is replaced by v>=0 with a zero coordinate,
the proof supplies no all-interior root and the full-opponent contraction
consumer may fail. If S* does not contain its recipient, the large term
enters B rather than Q and the displayed sign/pole equation is wrong.
The pole sign must MATCH the uniform inverse-column sign. An opposite-sign
pole does not give the positive root(4). None of these weakenings is claimed.

## 6. Full-four-player source separation

Consider the following four-player comparison matrix:

    Gamma=[0,1,1,-1; -1,0,-1,2; -1,2,0,-1; -1,-1,2,0],
    Gamma^-1=(1/7)[7,1,-5,-3;7,3,-1,-2;7,2,-3,1;7,5,-4,-1].

Its determinant is7, column0 is all1, and column1 is also strictly positive.
Other inverse entries are negative. Fix own singleton rewards1 and
r_i({j})=1+Gamma_ij for i!=j. These singleton rewards are all nonnegative.
Thus the ordinary theorem applies with v=ones, recipient0, S*=I, A=1:

    r_0(I)=M,       z*=(1/3)^(1/3)*ones,
    q_i=(3M)^(-1/3)+O(M^(-2/3)).                    (6)

For any fixed bounded completion in this family, the exact payoff tends
to(4/3,1,1,1), by(7). This is a limit across DIFFERENT reward tables;
for each fixed table the theorem already supplies its own one-profile
uniform-equilibrium target. No cross-table target is being asserted.

Complete the bounded rows as follows, writing successor j=i+1 modulo4.
At each adjacent pair{i,j}, pay-1 to i, pay r_j({i})+7 to j, and pay1
to both outsiders. At each opposite pair pay-1 to both members and1 to
both outsiders. At each triple pay-1 to its members and1 to its outsider.
Set the remaining grand rewards to(-10,-11,-12) for recipients1,2,3.
All nonselected nonsingleton coordinates have absolute value<=12.
Consequently this entire one-parameter family has actual full-support
stationary Nash/UE for all sufficiently large M.

Equivalently, its literal singleton and pair rows are

    0:(1,0,0,0), 1:(2,1,3,0), 2:(2,0,1,3), 3:(0,3,0,1),
    01:(-1,7,1,1), 12:(1,-1,10,1),
    23:(1,1,-1,10), 03:(7,1,1,-1),
    02:(-1,1,-1,1), 13:(1,-1,1,-1).

This family has NO root Nash with a sure quitter, for ANY continuation and
any M>=0. Fix a supposed sure owner i. Every nonsuccessor j!=0 has strictly
negative reward whenever it joins that owner (pair, triple or grand), whereas
Continue receives nonnegative nonparticipant rewards. So such j must
Continue. At least one of the two nonsuccessors is not0; hence the grand
coalition is already unreachable. The remaining nonsuccessor, even if it
is0, must then Continue by the same negative joining comparison. The
successor now strictly prefers to join: its reward rises by7 over the
owner's singleton. The owner receives-1 and can instead withdraw to its
nonnegative singleton payoff at that successor. This contradicts Nash.
It excludes the ENTIRE sure-owner and persistent-base source selections,
not merely pure profiles.

Every proper nonempty child C has an unsafe EXACT child Nash witness.
Choose d in C with successor(d) outside C; such d exists since a directed
four-cycle has no proper nonempty successor-closed subset. Within C let
only d Quit surely at date0 and all others choose Never. Each other child
member receives a nonnegative singleton payoff from d; joining yields-1,
and no delayed deviation beats the already selected singleton. Player d
earns its own singleton1 rather than Never0. Thus every child full debt is0
and its joint all-Never probability is0. The absent successor gains
EXACTLY7 by Quit0. Therefore no raw withdrawal/future-join reward certificate
whose conclusion bounds that outsider's gain by child debts plus a bounded
Never-slack term can hold on ANY proper child of this table. This is the
same whole-child semantic falsifier, not just a chosen pointwise row screen.

The matrices and the nonnegative-child/passive-row distinction are checked
in the inspected tracked files:

- `Math.CyclicChildJointPhase.SharedFixture.matrix_eq` and `matrix_det` in
  `MathUE/LinearProgramming/CyclicChildSharedFixture.lean`;
- `full_inverse_not_nonnegative`, `only_nonnegative_child_inverse`, and
  `no_nonnegative_deleted_inverse_and_passive_row` in
  `MathUE/LinearProgramming/CyclicChildSharedFixtureScreens.lean`.

These declarations provide matrix facts, not a producer for the new collision
completion or a claim of universal source separation. Criteria requiring the full inverse to be nonnegative do not apply to
this Gamma. The theorem applies because only the selected signed column
must be positive.

## 7. Additional whole-source boundary tests

The only premium trap in the displayed four-player family is the full
player set: each player's only strict proper-coalition participant premium
comes from its incoming directed pair, so a proper trap would have to be
closed under the entire predecessor cycle.

For any nonzero nonnegative weight vector w, put

    H_w(S)=sum_i w_i [r_i(S union{i})-s_i].

The four singleton tests in the literal table give exactly

    sum_d H_w({d})=2w0+2w1+5w2+5w3>0.

Thus no such weights make all supportwise forced-Quit upper averages
nonpositive. At equal weights this sum is14. In particular, the boxed
charge condition requiring every singleton's outsider inserted-premium
sum to be strictly negative fails at the full trap. These are failures of
the respective full finite tests, not a claim about arbitrary strategies.

The inverse has a mixed-sign column3 with signs(-,-,+,-). Consequently
no independent sign choice on its columns can make the entire inverse
positive. Positive rowwise payoff scaling rescales inverse columns
positively and player relabeling only permutes entries, so neither
operation removes this obstruction.

For every ordered recipient/partner pair(i,p), one of successor(i) and
i+2 differs from p. Call it j. At the sole-sure outsider row j, the
recipient's zero-partner endpoint difference is

    r_i({i,j})-r_i({j})=-1-r_i({j})<0.

Every singleton coordinate is nonnegative, so this violates even a weak
nonnegative lower face for every chosen pair. This excludes the whole
selection of crossed-face guards requiring that lower face, not merely
one chosen partner.

These calculations have the following tracked source correspondences:

- `exists_positive_odds_of_positive_inverse` in
  `MathUE/LinearProgramming/PositiveInverseTwoPairOdds.lean`
  requires the entire inverse to be positive and does not supply this
  single-column arbitrary-completion producer.
- `QuittingCrossedSourceGuards` in
  `UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseGuards.lean`
  requires the lower face just falsified.
- `HasBoxedQuittingNashCharges` in
  `UniformEquilibrium/Quitting/Classification/BoxedQuittingNashChargeReturn.lean`
  uses the strict singleton charge tests just falsified.
- `CappedClockParentRewardCertificate` in
  `UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockPointwiseDomination.lean`
  implies an outsider-gain bound by child debts. The zero-debt child
  witnesses in Section6 falsify that bound for every proper child.

This is a comparison with these concrete whole source selections.
It is not an assertion that the fixture lies outside every unspecified
implicit-function neighborhood or every conceivable existence theorem.

## 8. Actual-data adapter and formalization handoff

The inputs are singleton rewards, one recipient, one containing coalition,
one signed positive inverse column, a positive pole coefficient, and raw
bounds on every other nonsingleton coordinate. No strategy, continuation,
Nash component, or target is assumed. Sections2–3 produce actual interior
hazards directly from those inputs. Section4 produces their terminal
payoff and bounds every complete unilateral behavioral deviation.

The new mathematical inputs to formalize are the exact canceled
polynomial, its explicit positive rank-one pole root, the determinant
identity(5), and the compact-parameter root production. The existing
stationary endpoint compilers named in Section4 then apply: joint and
player-deleted continuation probabilities are strictly less than one,
the produced value is a fixed point, and both pure endpoints equal it.

For the scale-thick conclusion, formalize the additional substitution
e=t*b and its polynomial extension; bounded-box uniformity alone does
not prove it. Compact parameter uniformity is restricted to the displayed
open invertibility/strict positivity region.

The counterexample restriction is concrete: no sufficiently large table
in the stated signed single-pole region can be a uniform-equilibrium
counterexample, even when the full inverse has mixed signs. It is not
a normalization of every reward table into that region.

The new raw-data producer and asymptotics are ordinary mathematics, not
yet Lean-checked declarations. No arbitrary-game existence theorem,
finite-controller completeness, or conclusion about a fixed limiting
negative-grand table is asserted.
