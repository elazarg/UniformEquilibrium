# Complete positive joining-excess axis and the remaining joint-return boundary

Owner: CODEX_COORDINATOR. Ordinary mathematics, not checked in Lean. The
positive joining-excess axis below is completely covered. Arbitrary Fin4
remains open; this is a family with a fixed singleton matrix and specified
higher entries, not an arbitrary-table theorem.

## 1. Exact raw family

Fix the native singleton matrix

    Gamma=[0,3,-1,3;2,0,1/2,-3;2,-2,0,-1;-1,-2,1,0]

and the higher native entries

    Z0(02)=-1/10, Z1(02)=5, Z3(02)=-219/29,
    Z1(13)=-100, Z2(23)=3, Z3(13)=10, Z3(23)=-100,
    Z3(03)=1, Z3(023)=15/2.

Let Z0(03) be any fixed nonpositive number. Every unspecified higher entry
is arbitrary fixed finite, except

    Z1(12)=-K, Z2(12)=p, Z2(02)=2+eta.

For every eta>0 there is finite M_eta such that every real p and every
K>=M_eta(1+|p|) has an exact periodic terminal Nash equilibrium and an original
uniform-equilibrium payoff. Original own levels kappa are arbitrary, with
r_i(D)=kappa_i+Z_i(D) on nonempty coalitions; live/Never remain zero.

Moreover, throughout the whole unbounded tail

    eta>=305713711170/4725703339153,

one only needs K>=1+max(Z1(01),0)+max(Z1(012),0), independently of p and eta.
There is no missing middle interval. No uniform M_eta as eta decreases to
zero, and no positive-p conclusion at eta=0, is asserted here.

## 2. Exhaustive proof by the two raw producers

The rational parametrization in Section5 of the
[direct-return theorem](../exports/CORE_FREE_JOINT_RETURN_UNIFORM_EQUILIBRIUM.md)
selects one b in(0,1/3) for every eta>0. Explicitly,

    eta(b)=-(3b-1)(73b-1450)(190b+29)
                /[29b(219b^2-1030b-1160)].

Its proved strictly negative derivative and endpoint limits give a unique
simple root. The same section supplies C,T,j,X1,X2 and proves throughout
this entire interval, not merely its tail,

    0<C<3, T>0, X1>0, X2>0,
    C-j>0, 3X2>4b/10, Q3_join<0.

These are all the common strict return guards. There are exactly two cases.

1. If j>100T/3, all assumptions of the
   [finite-core theorem](../exports/JOINT_QUITTING_NEGATIVE_VALUE_UNIFORM_EQUILIBRIUM.md)
   hold, including j<C and the raw prefix interval. Its finite core and
   adjacent-length gluing give every real p once K>=M_eta(1+|p|).
2. If j<=100T/3, the direct-return theorem applies. When j>0, the raw
   continuation (C,-j,T,0) already satisfies its wash inequality
   T>=3j/100. When j<=0 it has no negative quiet coordinate and needs no
   wash. Both cases give exact finite returns and the displayed explicit
   K bound; p never occurs in any root or unilateral comparison.

The direct theorem's larger generic bound on K can be sharpened uniformly
here: x/[(1-x)b]<=1 and x/(1-x)<=1, so the stated K bound makes the quiet1
joint offer strictly negative for every b. Taking the larger of that bound
and the finite-core threshold in the first case supplies M_eta.

The function j increases and T decreases with b. At b=331/1000,

    j-100T/3=-5546944652414753/1500285581257994157<0.

The strictly decreasing eta map therefore identifies the stated entire tail
as a subset of the direct-return case. The actual transition is a single
algebraic point; neither its numerical approximation nor a guessed threshold
is used to cover the two cases. This proves the full axis claim.

The direct theorem also gives an exact five-date example at
eta=12281660/12608823, valid for every K>=1 and arbitrary p. At p=0 and
K>=1000 it lies in a rigorously stationary-free region. Its failure of the
finite-core guard is strict, so the second producer closes a surviving
region rather than merely shortening an already-covered strategy.

## 3. One removable sign and a real topology limitation

The finite-core proof also permits arbitrary d=-Gamma30, keeping its other
hypotheses and explicit D>0 test. This follows by auditing its equations:
d occurs only in

    X3=e*b-x[d-b(Z3(02)+d-e)]+(1-x)(1-b)C3.

Its limiting x derivative is -D, supplied by the retained raw guard.
Neither the core, wash, return nor resonance arguments use d's sign.
The cubic remains the exact elimination equation. Thus no negative
Gamma30 hypothesis is needed for that extension. The direct theorem already
states this more general sign scope.

This does not make the finite-core architecture universal in the singleton
matrix. The existing pointed witness3 in the
[residual partition](CODEX_COORDINATOR__FIN4_RESIDUAL_PARTITION.md) is

    [0,3,-3,1;2,0,-1,-1;-1,-1,0,2;-1,-2,3,0].

It has determinant7, mixed inverse, positive inverse columns0,1,3, R0 degree+1,
negative columns, a negative reciprocal pair, and no inverse-positive child.
Its only opposite-sign reciprocal pair is03. The finite-core architecture
still requires two distinct opposite-sign pairs02 and23, so every labeling
fails before higher rewards are tested. These are already established matrix
facts, not a new no-UE example. The all-completion nonnegative-inverse theorem
also requires negative determinant; a positive inverse by itself must not
be treated as that theorem's full hypothesis.

The next substantial obligation is a producer for arbitrary higher rewards
on the remaining matrix patterns, or a true global-source exclusion. The
completed eta axis and the sign extension do not supply either one.
