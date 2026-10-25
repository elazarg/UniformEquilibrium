# Exact Nash nonattainment on the small-premium calibration

Owner: CODEX_NEGATIVE_CAPS. **Proved ordinary mathematics; independently
reviewed [here](../feedback/CODEX_NEGATIVE_CAPS__EXACT_NASH_NONATTAINMENT__BY_CODEX_COLLAR_ADVERSARY.md)
and [here](../feedback/CODEX_NEGATIVE_CAPS__EXACT_NASH_NONATTAINMENT__BY_CODEX_LOCAL_COLLAR_REVIEW.md).**
Ordinary mathematics, not Lean checked. This is an unrestricted exact-Nash
nonattainment result, not a counterexample to uniform equilibrium existence.
The calibration includes classes already known to have uniform equilibria.

## Statement and precise data

There are four players, one live state, independent private Continue/Quit
choices, and absorption at the first nonempty quitting coalition. Original
live and Never rewards are zero. Original own singleton rewards are1.
Write Z_i(A)=r_i(A)-1 for nonempty A only; this does not translate Never.
The native singleton matrix is

    Gamma=[0,3,-1,3;2,0,1,-3;2,-2,0,-1;-1,-2,1,0].

Every passive native reward is additive: Z_i(A)=sum_(j in A)Gamma_ij
when i is not in A. Every proper nonsingleton participant reward in rows
0,1,2,3 is respectively e,h1,e,h3. The native grand reward is
(10,-2,-e,-1). These rules specify all sixty rewards.

**Theorem.** There is epsilon0>0 such that, for every independent
choice 0<e,h1,h3<epsilon0, this game has no exact terminal Nash profile,
even allowing arbitrary independent behavioral stopping laws, infinite
supports and positive Never masses.

The main new step is a uniform global nonnegativity theorem for bounded
exact-Nash continuation sequences. A one-root nonnegativity invariant alone
does not give this conclusion: its input might have negative coordinates.
Sections1--4 eliminate that possibility using the complete infinite sequence.

## 1. Root identities and the two previously established finite facts

Write q=(x,y,z,w), H_i=product_(j!=i)(1-q_j), D_i=1-H_i. Against a native
continuation C, the Quit and Continue endpoints are

    Q0=eD0+(10-e)yzw,
    Q1=h1D1-(2+h1)xzw,
    Q2=eD2-2exyw,
    Q3=h3D3-(1+h3)xyz,
    K_i=(Gamma q)_i+H_i C_i.                       (1)

Every actual native continuation lies in[-3,10]^4, and its coordinate2
is at most2. For sufficiently small positive premiums, no exact Nash root
against any actual continuation has a sure quitter. The complete finite
sure-owner census, including arbitrary feasible punishment tails, is in
Section8 of [the unequal-premium theorem](../exports/UNEQUAL_PREMIUM_CONTRACTION_UNIFORM_EQUILIBRIUM.md).
It assumes only the actual lower bound C2>=-3; its explicit parameter box
contains every sufficiently small independent positive choice here.

An exact terminal Nash profile therefore has positive joint survival at
every finite date, and every conditional tail is exact terminal Nash.
Precisely, C_i^t is its ORIGINAL terminal payoff at the conditional tail
starting at date t, minus1; q^t is that tail's first-date hazard vector.
Thus native bookkeeping assigns Never the value-1, while the original
game's Never payoff remains zero. It is not the payoff of a game that
uses Z on absorption and leaves Never at zero. Nash then gives

    C_i^t=K_i(q^t,C^(t+1))>=Q_i(q^t),
    q_i^t>0 implies C_i^t=Q_i(q^t).                (2)

These are full behavioral consequences: a profitable tail replacement
would multiply its gain by positive reach to improve the original profile.
In particular C0^t>=0 and C2^t>=-e at every date.

The second finite fact is the zero-premium part of the polynomial
certificate in [the cap-region theorem](CODEX_UNEQUAL_GLOBAL__NONNEGATIVE_CAP_ROOT_ACTIVITY.md):

    if C>=0, C2<=2, and Q^0(q)=Gamma q+H(q)C,
    then q=0.                                    (3)

Here Q^0=(10yzw,-2xzw,0,-xyz), and q may be anywhere in the closed cube.
For clarity, the certificate uses the four inequalities

    z+2x(1+zw)<=3w, z<=x+2y,
    2y+w-2x<=2(1-x)(1-y)(1-w),
    10yzw-3y+z-3w>=0.

Their only solution is zero; the cited note supplies the exact bivariate
Bernstein certificate. No limiting equality or positivity premise is lost
at a zero or unit hazard.

We first study ANY bounded infinite sequence obeying(2) at zero premiums,
with C^t in[-3,10]^4 and C2^t<=2. The closed relation(2) is retained even
if a limiting hazard equals1. Thus C0^t,C2^t>=0 automatically.

## 2. A negative coordinate forces a full-support successor forever

At zero premiums, C1<0 requires x,z,w>0, while C3<0 requires x,y,z>0.
No other coordinate can be negative. A negative phase consequently has
support012,023, or0123. We first exclude the two proper supports.

Suppose q=(x,y,z,0) has support012 and C3^t<0. Its active equalities and
nonnegative coordinates0,2 give

    z>=3y, y>=x, C1^(t+1)<0.

Its passive row3 term is -x-2y+z>=0. Hence C3^(t+1)<0 too. The next
phase must therefore have full support. These identities also exclude
unit hazards in the current proper support: z=1 contradicts row1,
x=1 forces y=1 by row2, and y=1 contradicts row0.

Write the next hazards as (X,Y,Z,W). Their output is
(10YZW,-2XZW,0,-XYZ). Since C2^(t+1)=0, the current active row2 gives
x=y=s. Put H=(1-s)(1-z)>0. The current rows0,1 then give

    z=3s+10H YZW, 2s+z=2H XZW,
    5s=2H ZW(X-5Y)>0.

Thus X>5Y. Nonnegative coordinate2 at the subsequent tail and the next
full row2 imply W>=2(X-Y)>8X/5. The supposedly negative coordinate is

    C3^t=H YZ[10W-(1-s)X]>0,

a contradiction.

Now suppose q=(x,0,z,w) has support023 and C1^t<0. Active rows0,2,3 give
z>=3w, w>=2x, and C3^(t+1)<0. Its passive row1 term2x+z-3w>0 makes
C1^(t+1)<0 as well. Again the next phase is full. Unit hazards in the
proper support are impossible directly from its active rows0,2,3.
Since the next coordinate2 is zero, w=2x. Write x=s, so z>=6s and s<1/6.
Put H0=(1-z)(1-2s) and H3=(1-s)(1-z). The current rows0,3 give

    z=6s+10H0 YZW, z=s+H3 XYZ,
    5s=YZ[H3 X-10H0 W]>0.

Since H0/H3=(1-2s)/(1-s)>4/5, we have X>8W. The next row2 gives
Y>=X-W/2>15X/16. Consequently

    C1^t=2s+2H0 ZW[5Y-(1-s)X]>0,

again a contradiction. Therefore every negative phase has full support.

If its next vector were nonnegative, all four current active equalities
would contradict(3). Hence every negative phase is followed by another
negative, full-support phase. It would generate an infinite consecutive
full-support chain. We now exclude every such chain.

## 3. Ratio descent followed by geometric growth

Along that chain coordinate2 is zero at every phase. Thus its active
row2 gives w=2x-2y, and

    a=y/x in(0,1), b=z/x>0, K=2xzw>0.

Write primes for the next phase and set

    A=4-6a-b, B=6-3a-b,
    H1=(1-x)(1-z)(1-w), H0=(1-y)(1-z)(1-w).

Rows1 and0 are exactly

    K=xA+H1 K', 5aK=xB+5H0 a'K'.                 (4)

The second identity implies B<=5aK/x<=10a, hence

    A<=-2+7a.                                    (5)

Define

    D=B-5aA=30a^2-23a+6+(5a-1)b.

For a>=1/5, D>=191/120>0, since the minimum of
30a^2-23a+6 is191/120. If a<=1/4, (5) gives A<=-1/4, so H1=0 is
incompatible with the first identity(4). If a>1/4 and H1=0, (4) would
instead imply D<=0, also impossible. Therefore H1>0 throughout the
chain, and H0>0 too. In particular every hazard is strictly below1.

Put t=K/x=2zw<=2. Eliminating K' from(4) yields

    a'=(H1/H0)[a-D/(5(t-A))],
    H1/H0=(1-x)/(1-y)<1.                          (6)

For a>1/4, t-A<=4+b and D>=191/120+b/4. Therefore

    a'<a-1/20.                                   (7)

This forces a<=1/4 within finitely many steps. That interval is forward
invariant: for1/5<=a<=1/4 use D>0 in(6); for0<a<1/5, rewrite(6) as

    a'=(H1/H0)(a t-B/5)/(t-A),
    (t-A)/5-(a t-B/5)=(1/5-a)t+(2+3a)/5>0,

which gives a'<1/5. Once a<=1/4, (4),(5) and K<=2x give

    K'>=K+x/4>=9K/8.                             (8)

This is impossible forever because0<K<=2. Thus no negative phase
exists in any bounded zero-premium continuation sequence satisfying(2).

## 4. Uniform extension to small positive premiums

For a bounded positive-premium sequence define

    delta=sup_(t,i) max(-C_i^t,0).

First delta tends to zero uniformly as max(e,h1,h3) tends to zero.
Otherwise select sequences, shift each to a date with a negative
coordinate bounded away from zero, and pass to a coordinatewise
subsequence of all hazards and continuation vectors at every subsequent
integer date. The compact product has a diagonal subsequence; relation(2)
is closed. Its limit is exactly a bounded zero-premium sequence with a
negative initial coordinate, contradicting Sections2--3.

Uniformly, a phase with any negative coordinate also has hazard sum
s=x+y+z+w tending to zero. Such a phase has support012,023,013 or full:
its negative Quit endpoint requires all three opponents to have positive
hazards. Support013 is impossible already at positive premiums, since
its active row0 and C0^(t+1)>=0 give
3(y+w)<=e(y+w-yw). After selecting a fixed support and passing to a
zero-premium limit, full support retains all four active equalities,
so(3) forces q=0. Support012 retains row1, giving2x+z<=0, then row0
gives y=0. Support023 retains z>=3w, w>=2x and x>=z, again forcing zero.
This proves the claimed uniform convergence of s on negative phases.

Choose a common positive threshold so that premiums are at most1/10,
delta<1/20 and s<=1/2 on every negative phase. We improve the qualitative
conclusion to exact nonnegativity by a cubic bootstrap.

For a full-support negative phase, use k=(9,7,0,8), with
k Gamma=(6,11,6,6). Active equalities and C^(t+1)>=-delta give

    6s<=(9e+7h1+8h3)s+90yzw+24delta
       <=(12/5)s+(10/3)s^3+24delta.

Since s<=1/2, this implies s<9delta, and in particular s<=12delta.
For support012, active rows0,1 give

    y<=11z/29,
    (19/10)x+(9/10)z<=delta,

so s<3delta. For support023 they give the convenient weaker bounds

    w<=2z/5, x<=3w/5+3delta/5, z<=4x/3+6delta/5,

so z<=50delta/17 and s<6delta. Thus s<=12delta in every case.

Every negative coordinate satisfies C_i^t>=Q_i>=-s^3/9: use
Q1>=-3xzw, Q3>=-2xyz, Q2>=-2e xyw and the arithmetic-geometric mean
bound on each triple product. Taking suprema gives

    delta<=192delta^3.

Together with delta<1/20 this forces delta=0. We have proved uniform
nonnegativity for all bounded exact-Nash continuation sequences in the
stated range; the three positive premiums need no ratio restriction.

## 5. Nonnegativity excludes every exact terminal Nash profile

Decrease the common premium threshold further so that the reviewed
[cap-region activity theorem](CODEX_UNEQUAL_GLOBAL__NONNEGATIVE_CAP_ROOT_ACTIVITY.md)
applies. It implies that a positive player0 hazard can occur only in a
solo0 phase. Once this restriction holds, every player's Quit endpoint
is strictly positive whenever some opponent has positive hazard: all
queried participant premiums are positive, and the only queried grand
reward is player0's positive10.

No solo phase is possible. A solo-j phase forces C_j^t=C_j^(t+1)=0.
Until a first later date with another active owner, solo-j and empty
phases preserve that zero. At such a first date the positive Quit
endpoint contradicts it. If no other owner ever acts, select an outsider
i with Gamma_ij<0 (every column has one). Its actual native payoff is a
mixture of Gamma_ij and the native Never value-1, hence is negative.
That contradicts the proved nonnegativity. In particular player0 never
acts at any date.

Only owners1,2,3 can now act. Let v_t=C2^t>=0. Row2's Continue identity
is

    v_t=-2y_t-w_t+(1-y_t)(1-w_t)v_(t+1).          (9)

Thus v_t<=v_(t+1). If z_t>0, the absence of solo phases gives
D_t=y_t+w_t-y_t w_t>0, and its active equality gives

    v_t=eD_t>0, v_(t+1)>=D_t>=v_t/e.

The sequence is bounded above by2 and e<1, so there can be only finitely
many dates with z_t>0. Beyond the last such date, players0 and2 both
Never quit. Player2's native terminal reward is then one of-2,-1,-3
if players1 or3 quit, and-1 if nobody quits. Its actual tail payoff is
at most-1, contradicting v_t>=0. This proves the theorem.

## 6. Zero-debt points in the semantic closure have nonnegative native payoffs

Let K be the closure of all actual pairs(U,B), where U is the original
terminal payoff vector minus1 and B is the vector of full unilateral
response suprema minus1. The closure is in the bounded Euclidean payoff
and cap box. Its points may fail to be realized by actual profiles.

**Corollary.** At the same sufficiently small independent positive premium
parameters, every point(U,B) in K with B=U has U_i=B_i>=0 for every i.

For an actual profile, separate its first root q and conditional tail
(U',B'). Put P=Gamma q and h=product_i(1-q_i). The exact identities are

    U_i=q_i Q_i+(1-q_i)(P_i+H_i U'_i),
    B_i=max(Q_i,P_i+H_i B'_i).

For a point in the closure, compactness extracts q in the closed cube and
a child pair(U',B') in K with the same identities. Write

    R_i=max(Q_i,P_i+H_i B'_i)
        -q_i Q_i-(1-q_i)(P_i+H_i B'_i)>=0.

Then B_i-U_i=R_i+h(B'_i-U'_i). If B=U, all R_i vanish, so q is a full
exact Nash root against B'. Every actual response cap's native coordinate2
is at least-e (Quit immediately) and at most2, and these bounds pass to K.
The complete sure-root exclusion therefore gives q_i<1 for every i.
Hence h>0, and the same identities force B'=U'.

Iterating this extraction gives an infinite bounded sequence obeying(2).
Section4 applies to the entire sequence and proves U=B>=0 at the initial
point. This argument does not assert actual realization of its infinite
semantic tail. In particular Section5's actual Never-payoff contradiction
cannot be applied to an arbitrary chain extracted from K.

## Scope and sources

This excludes exact Nash profiles, not arbitrarily accurate Nash profiles.
It supplies no positive lower bound on unrestricted exploitability. Its
intersection with the known contracting-block existence regions gives
games with uniform equilibria but no exact terminal Nash. This includes the
ray(e,h1,h3)=(beta,beta/10,beta) for sufficiently small beta: the
[three-diffuse-flow theorem](../exports/THREE_DIFFUSE_FLOWS_UNEQUAL_PREMIUM_UNIFORM_EQUILIBRIUM.md)
supplies its uniform equilibrium.

The result does not apply to canonical partial-Nash incoming heads:
their pivot can pay positive regret, violating(2). It therefore does not
exclude the actual-global-minimum or zero-observer-boundary branches.

Inspected semantic sources: `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
and `quittingGame_fixedProfile_uniformPayoffWitnesses_of_terminalNash_exact`
in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
No Lean commands were run. Existing whole-law nonattainment examples and
restricted common-clock obstructions do not establish the global
nonnegativity argument for this calibration.

Both independent reviews checked the compact-product limit, the two proper
negative supports, the cubic bootstrap, the actual full-behavior consumer
and the semantic-closure corollary. No mathematical objection remains.
