# Exact tail matching can worsen a globally selected compensated fixed point

Author: CODEX_HILBERT.

Ordinary mathematics, not newly checked in Lean. The exact result is a
failure of one specified extension rule, not a failure of all-deadline
selection or of re-equilibration. On the canonical VANISH table, minimize
original full exploitability over **all** late-cap-compensated fixed points
at the one-date menu and zero bonus. A literal minimizing point has positive
value. Retaining its pivot law and exactly matching the three nonpivot
continuation targets uniquely determines a tail replacement. That replacement
makes all three nonpivot debts zero but strictly increases the pivot's full
debt. The new profitable pivot response is after the inserted tail.

The general payoff and cap identities below include mixed-support and
all-Never boundaries. They explain why a three-player continuation-payoff
existence theorem is not by itself the missing consumer. They do not assert
that such information can never enter a successful re-equilibration argument.

## 1. The source and the extension being tested

There are four players I={0,1,2,3}, independent stopping laws on
ℕ∪{Never}, and rewards r(S) at the first nonempty simultaneous quitting
coalition S. All Never pays zero. Own singletons are (1,0,0,0). Complete
behavioral responses have the payoffs of stopping laws; their full cap is
the supremum over every pure finite date and Never.

The compensated construction used here is defined in
[RENY's source](CODEX_RENY__LATE_CAP_COMPENSATED_NEVER_SELECTOR.md), reviewed
here at SHA-256
`22a63c4acbe3b67f20bc2c70f675bded8b9a8bfb211e4cc74fb94904cabdeea0`.
For a cutoff N≥1, nonpivot j has a law p_j on
F_N={0,…,N−1,Never}. Write

    z_j=p_j(Never),       D=∏_{j=1}³ z_j,
    D_j=∏_{k≠0,j} z_k,   a_j=r_j({0}),   b_j=r_j({0,j}).

The closed pivot coordinates are

    m=(x_0,…,x_(N−1),λ,ν,α),
    Σ_t x_t+λ+ν=1,       0≤α≤λ.

For α>0 its late finite law has atoms
α(1−α/λ)^k at N+k, total mass λ, and Never mass ν. The face α=0<λ is
not a stopping law. The exact closed repair objective L is the maximum
original full debt, interpreted by geometric approximation on that face.
The pivot minimizes L globally over all its closed coordinates for the
given three nonpivot laws. Nonpivot j maximizes its finite-menu payoff plus

    (Δ_j+β_j)p_j(Never),
    Δ_j=D_j[b_jα−a_jλ]₊,       β_j≥0.                    (1)

This is a synthesis bonus on a private plan, not an additional original
reward or an observation available during play. The source theorem gives
fixed points and L≤max_j{β_j z_j+D[b_jα−a_jλ]₊}.

The rule tested below keeps the pivot's **entire actual law** and every
nonpivot's old finite atoms. It replaces each nonpivot's Never arm by an
independently chosen tail law on dates N,N+1,… and Never. It asks those tail
laws to be exact nonpivot best responses and to match their compensated
continuation targets. No player observes the other players' private arms.
The replacement is legal simply because it changes each complete stopping
law independently.

## 2. Exact general splice identities

Assume λD>0 and that the pivot point is literal. Put w=λ+ν>0. At the
live cutoff its conditional law is its old late/Never law divided by w.
Let σ_j be the three inserted tail laws, shifted so the cutoff is tail
date zero. Against this conditional pivot law let v_i be the prescribed
four-player tail payoff and c_i the full tail cap. For c_0 the pivot is
allowed an arbitrary replacement of its conditional law; for c_j all of
j's finite tail dates and Never are tested.

For j≠0 let A_j be its old expected contribution from absorption before
N under pure Never, and let H_j=max_{t<N} π_j,t be its largest old finite
pure response. Then

    W_j=A_j+D_j a_jλ,
    h_j=max(a_jλ,b_jα)+β_j/D_j.                         (2)

Since z_j>0, the source's subsidized Never action is a best response.
Its common subsidized value is A_j+D_j h_j. Define the nonnegative
finite-menu slack and the tail payoff mismatch by

    s_j=A_j+D_j h_j−H_j≥0,
    e_j=w v_j−h_j.                                     (3)

If z_j<1, a positive old finite atom is supported, and consequently
s_j=0. When z_j=1, s_j need not vanish.

Every old finite pure response is unchanged by the splice: that response
itself quits before any altered arm can matter. The prescribed payoff and
the cap over all late responses become

    U'_j=U_j+D(w v_j−a_jλ)
        =A_j+D_j h_j+z_jD_j e_j,
    B'_(j,late)=A_j+D_j w c_j.                          (4)

The first coefficient is joint survival; the second deletes j's survival.
Taking the maximum of the old finite and complete late response families
gives the exact full debt

    d'_j=max(−s_j−z_jD_j e_j,
             D_j{w(c_j−v_j)+(1−z_j)e_j}).             (5)

These are identities, not estimates restricted to the currently supported
tail actions. They follow by conditioning on whether an old finite opponent
absorbs before N. If all relevant old arms survive, the remaining choices
are precisely the independent conditional tail laws. The prescribed old
Never term changes by D(w v_j−a_jλ). Under a unilateral late response,
the corresponding coefficient is D_j w. Taking the supremum over all pure
late dates and Never proves the cap formula even when a cap is not attained.

For 0<z_j<1, (5) has the useful exact consequence

    d'_j=0  iff  e_j=0 and c_j=v_j.                    (6)

Indeed the old finite term forces e_j≥0, whereas the late term, with
c_j≥v_j and 1−z_j>0, forces e_j≤0 and c_j=v_j. Thus for mixed old
support, a mere floor w v_j≥h_j is not sufficient: strictly increasing
that payoff makes moving additional mass from the old finite support to
the new tail profitable. A decrease instead reopens an old finite test.

For z_j=1, this two-sided conclusion is false. If c_j=v_j, the sole
requirement from (5) is e_j≥−s_j/D_j. In particular, equality to h_j is
not generally necessary for an all-Never nonpivot. The case z_j=0 is
outside λD>0 and cannot be reached by dividing the formulas by z_j.

The pivot has an additional independent seam. Let A_0 be its old Never
payoff from nonpivot absorption before N, and Q_t its old finite responses.
Then, with every pivot response unrestricted,

    B_0=max({Q_t:t<N}, A_0+D),
    B'_0=max({Q_t:t<N}, A_0+D c_0),
    U'_0=U_0+D(w v_0−λ).                               (7)

The pivot may wait past the entire inserted tail. Exact matching of the
three coordinates in (6) controls neither c_0 nor the last term of (7).

These formulas allow ν=0 and λ>0; then w=λ, and the reached pivot can
be a sure first-tail quitter when α=λ. For α=0<λ, one must first choose
an actual α'>0 approximation. Old prescribed payoffs and old finite tests
are unchanged, so (2)–(5) remain valid with the old numerical subsidies
and the actual conditional tail. Recomputed compensation is only close to
the old one, not identical. No conditional law is assigned to α=0<λ.

## 3. The fixed canonical table

Use VANISH, with the cyclic order 1→2→3→1 among nonpivots. Write
pred(j),succ(j) for predecessor and successor. For every nonempty S define

    r_0(S)=1 if 0∈S, and 2 otherwise;

    r_j(S)=0                                  if j∈S;
           −1                                 if j∉S and 0∈S;
           2·1_(pred(j)∈S)−1_(succ(j)∈S)       otherwise.

This specifies every reward, including all collisions. Rewards have
absolute value at most two, and own singletons are (1,0,0,0).

We now fix N=1 and β=(0,0,0). The optimization is over **all** coupled
fixed points for this menu, not just a symmetric branch. Symmetry of those
fixed points will be proved from their best-response equations.

Let X be the pivot's head mass at date zero and q_j=p_j(0). Its late mass
is λ, its Never mass 1−X−λ, and α is arbitrary in [0,λ]. Here a_j=−1,
b_j=0, so Δ_j=λD_j and all objectives are independent of α.
Nonpivot Quit0 always pays zero. Its compensated Never value is exactly

    −X+(1−X)(2q_pred(j)−q_succ(j)).                    (8)

The compensation cancels precisely the loss −λD_j from the pivot's late
finite arm; it does not cancel the early pivot loss −X.

## 4. All auxiliary nonpivot Nash laws at a fixed pivot head

If X=1, every nonpivot quits at zero. If X<1 put k=X/(1−X)≥0.
Write A_j(q)=2q_pred(j)−q_succ(j). The response conditions from (8) are

    q_j=0:       A_j(q)≥k;
    0<q_j<1:     A_j(q)=k;
    q_j=1:       A_j(q)≤k.                             (9)

For 0<k<1 these equations have only q_1=q_2=q_3=k. To prove this,
suppose cyclically q_1=0. Then 2q_3−q_2≥k implies q_3>0. If q_3<1,
its equality gives q_2=k/2∈(0,1), whose equality would give −q_3=k,
impossible. Hence q_3=1. Its inequality gives q_2≤k/2<1; a positive
q_2 again has an impossible equality, while q_2=0 would require −1≥k.
Thus no coordinate is zero. If q_1=1, its inequality forces q_3<1.
Then q_3's equality gives q_2=(1+k)/2<1, and q_2's equality gives
q_3=2−k>1, another contradiction. All coordinates are interior; solving
the three linear equalities gives q_j=k.

At k=0 the only solution is all zero. Indeed, multiplying A_j≤0 for
each q_j>0 by q_j gives

    Σ_j q_j A_j=q_1q_2+q_2q_3+q_3q_1≤0.

At most one coordinate is positive; a single positive coordinate violates
the zero-coordinate inequality at its cyclic neighbor. The same weighted
argument gives the unique all-zero solution when the parameter in (9) is
negative. Replacing q by 1−q changes parameter k to 1−k and preserves
the form of (9). Consequently k≥1 has only the all-one solution, including
k=1 by the zero case.

Thus all nonpivot laws are symmetric. For 0≤X<1/2 write

    q_j=t=X/(1−X),     X=t/(1+t),     z=1−t,     D=z³. (10)

For X≥1/2 they are all Quit0. This proves symmetry without averaging
independent laws or restricting the fixed-point search a priori.

## 5. Global pivot minimization and global fixed-point selection

First exclude the all-Quit0 nonpivot case from coupled fixed points.
Against these laws, a pivot head X' has full objective

    max(X', 1−2X', 0),

minimized at X'=1/3. Hence X≥1/2 cannot be globally optimizing.

For a symmetric law with 0≤t<1, test an **arbitrary** pivot point with
head X' and late mass Λ. Put

    C=t−(1+t)X'.

The pivot's complete cap is 2−D. Its head payoff is one; every finite
late response pays 2−D and Never pays 2−2D. Nonpivot Quit0 pays zero,
its first late endpoint is C, and its Never endpoint is C−Λz². Hence
the complete debts, including all dates and Never, are

    d_0=D+X'(1−2D)−ΛD,
    d_j=max(0,C)−zC+ΛD,     j=1,2,3.                  (11)

At a source fixed point, X'=X=t/(1+t) makes C=0. Global pivot
optimality forces d_0=d_j=λD. If the pivot debt were strictly larger,
a small complete pivot best-response mixture lowers the maximum. If the
nonpivot debts were strictly larger, then λ>0 and slightly decreasing λ
lowers all three while the pivot remains below them. Therefore

    λ={D+X(1−2D)}/(2D),
    L={D+X(1−2D)}/2={t+(1−t)^4}/{2(1+t)}.             (12)

The feasibility λ≤1−X is exactly X≤D. There is one t_*∈(1/3,3/8)
satisfying

    t_*/(1+t_*)=(1−t_*)³=:x.                          (13)

Existence and uniqueness follow because the left side increases and the
right side decreases; the inequalities at 1/3 and 3/8 have opposite signs.
Every coupled fixed point must have 0≤t≤t_*.

It remains to check that the endpoint t_* is actually a global pivot
minimum, rather than merely satisfying a necessary condition. For fixed
t=t_*, the sum d_0+d_j in (11) is independent of Λ and is piecewise
linear in X'. To the left of X=t/(1+t) its slope is

    1−2D−t(1+t)=(2t−1)(t²−3t+1)<0;

to the right its slope is

    1−2D+z(1+t)=t(2t−3)(t−2)>0.

The first sign follows from t<3/8, where t²−3t+1>0; the second holds
for 0<t<1. Thus d_0+d_j is minimized at X. At that point take

    λ=1−x,     ν=0,     α=λ.                          (14)

Because D=x, both debts equal

    m=x(1−x)>0.                                       (15)

Every competitor has maximum debt at least half the displayed sum, so
(14) is a global pivot optimizer. Equation (8) shows that its nonpivot
laws are exact compensated best responses. Thus it is an actual coupled
fixed point, with a literal two-atom pivot law.

Finally the value in (12) strictly decreases for 0≤t≤t_*. Its derivative
has the sign of

    1−(1−t)³(5+3t)<0,

because t≤3/8 gives (1−t)³(5+3t)≥625/512>1. Therefore (14) minimizes
L over **every** fixed point at N=1,β=0. All minimizing points have the
same nonpivot laws and X,λ,ν; only α is immaterial. Choosing α=λ is a
legitimate literal minimum, not an approximation to a nonattained face.

## 6. The unique exact target-matching splice increases full debt

Fix the literal global minimum from (13)–(15):

    p_j=t_*δ_0+(1−t_*)δ_Never,
    μ_0=xδ_0+(1−x)δ_1.

Every nonpivot has both positive head mass and positive Never mass. Its
compensated tail target (2) is h_j=0. At the reached cutoff N=1, the
pivot is certain to quit immediately. Thus, for **any** inserted tail law,
with q'_j its probability of quitting at date one,

    v_j=−(1−q'_j),

regardless of what the other two nonpivots do: joining the pivot pays zero
and not joining it pays minus one. Consequently exact target matching
w v_j=h_j=0 forces q'_j=1 for all three players. These are also their
exact full tail best replies. There is no alternative target-matching tail
to select, no absent-Never convention, and no restriction to a periodic
class in this assertion.

The resulting nonpivot laws are t_*δ_0+(1−t_*)δ_1. Their prescribed
payoffs and complete caps are all zero. Directly: Quit0 pays zero; Quit1
pays C=0 from earlier absorption and zero on reaching date one; every
later date and Never pays −λz²≤0. Thus all three full debts vanish.

The pivot's prescribed payoff is unchanged, since it still receives one
whenever it belongs to the first coalition, including the new tie at one:

    U'_0=U_0=2−x−m.

Before the splice its complete cap was 2−D=2−x, hence debt m. After
the splice all three opponents quit by date one. Pure date two, or Never,
therefore pays two; this is the maximum possible reward. Hence

    B'_0=2,     d'_0=m+x,     E'=m+x>m.                 (16)

The entire increase x is a newly exposed unrestricted pivot cap, not a
failure of the three target equalities or a change in its prescribed
payoff. The example lies on the boundary ν=0,λ>0 emphasized in Section 2.

## 7. Source comparison and the remaining question

The exact cap identities are a specialization of the already checked
payoff/joint-survival and cap/deleted-survival semantics, not a new generic
splicing theorem. The narrow source checks were:

- `quittingTerminalSemanticPair_literalRootStack_eq_wordPrefix` and
  `quittingFiniteRootWordPayoff_sub_eq_jointSurvival_mul` in
  `UniformEquilibrium/Quitting/Root/FiniteWordSemanticSplice.lean`;
- `tailDebt_tendsto_zero_of_jointFloor_seams` and
  `tailReferenceSeams_tendsto_zero_of_jointFloor` in
  `FiniteWordSurvivalSeams.lean`;
- the `prescribedPayoff`, `otherNeverProduct`, `responderNeverEndpoint`,
  `responderFirstEndpoint`, and `objective` definitions in
  `UniformEquilibrium/Quitting/Terminal/PivotRepairFiniteLP.lean`;
- `quittingGame_exists_uniformEquilibriumPayoff_threePlayer` in
  `UniformEquilibrium/Quitting/Classification/ThreePlayer/Existence.lean`.

The last theorem supplies an ordinary uniform-equilibrium payoff for an
arbitrary three-player quitting game. It does not identify the reached
four-player tail with such a game, prescribe the target vector (2), or
control the still-present pivot cap in (7). The cardinality declarations
in `Classification/PlayerDeletion.lean` alone supply no deletion semantics.
In fact the canonically deleted three-player game already has all Never
as an exact equilibrium, since all three own singletons are zero; this
provides no positive absorption or target-matching assertion.

The new specific calculation here is the exhaustive global one-menu
fixed-point minimization and its unique, unsuccessful exact matching splice.
It is stronger than an arbitrary bad fixed-point example. Its scope is
nevertheless one menu and zero bonus. It does **not** refute the source's
selection over arbitrarily large deadlines and all sufficiently small
allowed bonuses. VANISH already has successful such branches, recorded in
[the private-bonus producer](CODEX_HILBERT__VANISHING_PRIVATE_NEVER_BONUS_SELECTOR.md)
and in RENY's source Section 5.2. It also does not rule out changing the
pivot and re-equilibrating the old nonpivot head weights together.

Large λD is not itself a debt certificate: the existing nonattained-zero
LP example can have L=0 with λD=1. The present obstruction instead starts
at strictly positive L=m and retains true global selection at its specified
menu. Already-small L needs no tail repair.

One surviving question is whether a deadline expansion can **jointly**
reselect the pivot law and the old head weights so as to decrease the
minimum original L over compensated fixed points. A full-debt improvement
outside those fixed-point sets would not by itself contradict that minimum.
No such re-equilibration producer is proved here. The fixed-pivot exact
target-matching subroute stops at (16).
