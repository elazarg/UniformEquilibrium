# A raw reward neighborhood with a thirty-three-phase uniform equilibrium

## Conjecture-facing change and strategic inputs

The raw center defined below has an exact absorbing periodic equilibrium and
lies in a full sixty-dimensional open class with the same property. Every
stationary prescription and every fixed disjoint-pair two-phase prescription
at this center has a strictly positive unrestricted exploitability gap.
The center also has no sure-first root followed by any behavioral continuation.
All three exclusions are proved in full below, including their finite exact
certificates. They coexist with the proper longer-period equilibrium.

All strategic data are produced from the reward table: the cycle hazards and
continuation values are obtained from a certified contraction; the same
strict margins produce them for each nearby raw table. No equilibrium, root,
continuation, minimal source, payoff target, or calendar is assumed as input.
The same produced profile supplies every accuracy in the fixed-target uniform
conclusion. The complete older raw-class comparison appears in Section 10.

The general four-player quitting conjecture remains open. This theorem
removes the specified raw neighborhood, not all exceptional matching tables.

## 1. Exact statement and literal table

There are four players, numbered 0,1,2,3. At every live history each independently
chooses Continue or Quit. A nonempty quitter coalition C absorbs permanently at
reward r_i(C); live and Never payoffs are zero. Set r_i(C)=1+Z_i(C), with
Z_i({i})=0. Define the two rational matrices

```
A = [ 0       1       -6       -1/100 ]
    [ 1       0       -3/2     -2/5   ]
    [-1/1000 -3/5      0        1     ]
    [-7/100  -1/25     1        0     ]

J = [ 0       1/1000   2        9/1000]
    [ 1/10    0       13/10     3/10  ]
    [ 1/2000  9/20     0        1/100 ]
    [ 1/200   1/1000   1/10     0     ].
```

For i≠j put Z_i({j})=A_ij+J_ij and Z_i({i,j})=J_ij. For the
opponent pairs B=01,02,03,12,13,23 assign the signs
σ_B=+1,−1,+1,+1,−1,−1, respectively. If i is the smaller of the two
players outside B, put Δ_i(B)=σ_B; for the larger put Δ_i(B)=−σ_B.
Then put

```
Z_i(B)       = max(0,−Δ_i(B)),
Z_i(B ∪ {i}) = max(0, Δ_i(B)).
```

Finally Z_i({0,1,2,3}\{i})=1 and Z_i({0,1,2,3})=0. These rules
specify all sixty nonempty-coalition rewards, without free entries.

**Theorem.** This raw table has a proper periodic behavioral profile with
physical phase supports

```
123 repeated thirty times, then 023, then 023, then 012.
```

Every listed player quits with probability strictly between 1/10000 and 7/10;
each omitted player continues surely. The profile is exact terminal Nash from
every phase against all behavioral deviations and defines a uniform-equilibrium
payoff. Its joint survival through a full period is less than 1/1000.
There exists δ>0 such that every table r' satisfying
max_{i,C≠∅}|r'_i(C)−r_i(C)|<δ, with live payoff zero, has an exact periodic
terminal Nash profile with the same support word, and a uniform-equilibrium
payoff. The neighborhood statement varies all sixty raw entries independently.
No numerical lower bound on δ is asserted.

The proof is a contraction of a four-dimensional continuation map, not a
rounding of a numerical equilibrium.

## 2. Root equations and the direction of composition

For a root hazard vector q and owner i define H_i(q)=∏_{j≠i}(1−q_j),
P_i(q) as the expected native reward Z_i(B) from nonempty opponent coalition B,
and Q_i(q) as the expected Z_i(B∪{i}) when owner i quits. In P the empty
coalition contributes zero. Given a proposed native continuation vector b,
write

```
C_i(q,b) = P_i(q)+H_i(q)b_i,
g_i(q,b) = Q_i(q)−C_i(q,b).
```

A proper root on support S is Nash with this continuation when g_i=0 for
i∈S and g_i≤0 for i∉S. Its output value is C(q,b) for every owner.
For an active owner the mixed prescribed payoff equals C because Q=C.
For an inactive owner Continue is prescribed and dominant.

Let T_S(b)=C(q_S(b),b), with the particular smooth root branch below. Our
composition is the **prefix** order

```
F = T_123^30 ∘ T_023 ∘ T_023 ∘ T_012.
```

Starting with continuation b, first prepend the 012 root, then the two 023
roots, then thirty 123 roots. Thus actual chronological play is the reverse
word stated in the theorem. If F(b)=b, the resulting circular list of values
and roots satisfies the Bellman and Nash equations at every physical phase.
Reversing this orientation incorrectly would not give the claimed equilibrium.

## 3. Explicit algebraic branch for a triple

Write S={i,j,k} in increasing order and z=q_k. At an active owner a, with the
other two active players u,v, the gap polynomial is

```
g_a = c_a + a_a q_u + b_a q_v + d_a q_u q_v,
c_a = −b[a],
a_a = b[a]−A[a,u],
b_a = b[a]−A[a,v],
d_a = Δ_a({u,v})+A[a,u]+A[a,v]−b[a].
```

The use of b_a as a polynomial coefficient in this display is local; b[a]
denotes the continuation coordinate. In the checker the coefficients are
returned in this order by `coeff`.

Set

```
N_x(z)=−c_j−b_j z,    D_x(z)=a_j+d_j z,
N_y(z)=−c_i−b_i z,    D_y(z)=a_i+d_i z.
```

Then q_i=N_x/D_x and q_j=N_y/D_y solve the first two active equations.
After multiplying the third equation by D_x D_y it becomes

```
E(z) = c_k D_x D_y + a_k N_x D_y
       + b_k N_y D_x + d_k N_x N_y
     = e_0+e_1 z+e_2 z².
```

Throughout the certified box and all its intermediate images the discriminant
is positive and every displayed denominator is nonzero. Use the same branch
at all thirty-three stages:

```
z = (−e_1 + sqrt(e_1²−4e_2 e_0))/(2e_2).
```

Consequently the three active equations hold **exactly**, by the quadratic
identity and the two rational substitutions. Interval inclusion of zero is
only an additional consistency check, not the proof of equality. The
certificate verifies properness and strict negativity of the remaining gap.
This supplies a smooth, explicitly defined composition on a neighborhood of
the entire starting box.

## 4. Exact contraction certificate

The complete standalone source is embedded in Appendix A. It depends only on
the Python standard library; save that block as `cycle_certificate.py` and run
`python cycle_certificate.py`. No external input file is needed.

The four exact decimal rational literals in Appendix A's `center` array define c.
Their leading digits are

```
c ≈ (0.746971766391142631747982490611703517,
     0.000184187760798227902857052124745075,
     0.001317526198792427496306501502294370,
     0.000013024428955622556983739324485142).
```

Let X={b: ||b−c||∞≤10^−60}. The complete exact output is

```
sup_X ||DF||∞ < 1/100,
||F(c)−c||∞ < 10^−62,
all 99 active hazards > 1/10000 and < 7/10,
all 33 inactive gaps < −7/100,
period joint survival < 1/1000.
```

Every comparison uses integer arithmetic, not the displayed floating-point
diagnostics. For orientation, the computed derivative bound is below .009208,
the center residual bound below 2.1×10^−119, and the period survival is about
.000658637. Those decimal summaries are not used by the proof.

The interval engine represents [l/2^512,h/2^512] by integer endpoints l,h.
Addition and negation are exact; multiplication and division round outward
using floor and ceiling integer division. Division rejects any denominator
interval containing zero. Square-root endpoints are obtained by integer
square root, rounding the upper endpoint upward unless exact. Every square
root has a strictly positive lower input. Four-component interval automatic
differentiation applies the usual sum, product, quotient, and square-root
rules. Thus the final derivative intervals enclose every derivative of F on
X; no finite-difference estimate or floating-point inverse is involved.

The propagated natural interval range is wider than X because it loses
correlations. It is **not** used to claim F(X)⊂X. Instead, the mean-value
inequality and the certified derivative bound give, for b∈X,

```
||F(b)−c||∞ ≤ ||F(c)−c||∞ + ||DF||∞ ||b−c||∞
           < (1/100+1/100)10^−60 < 10^−60.
```

Hence F maps the closed cube into its interior and contracts it with factor
less than 1/100. The contraction theorem gives a unique fixed point b*∈X.
Every branch and inequality certified on X therefore holds at b*. This proves
existence without identifying b* by an unverified approximate number.

## 5. Actual behavioral equilibrium and uniform payoff

Reverse the prefix list to obtain the physical periodic profile. Every
period contains a positive hazard from all four players. After deleting any
owner, at least one opponent still has a positive hazard in each period.
Thus joint survival and every opponent-deleted survival tend to zero
geometrically, from every phase.

The thirty-three cyclic native values satisfy each prescribed Bellman equation
and the two-action Bellman optimality inequalities. The values are bounded
because the list is finite. Iterating the prescribed equations leaves a
remainder bounded by a constant times joint survival, which tends to zero;
therefore these are the actual native terminal payoffs.

For an arbitrary unilateral behavioral deviation, iterate the Bellman
inequality along the unique all-Continue live history. The remaining term is
bounded in absolute value by a constant times opponent-deleted survival,
uniformly in that deviation. Taking the limit gives terminal payoff no larger
than the proposed value. This includes every finite deadline, mixtures of
such deadlines, and Never. It is not restricted to periodic or Markov
deviations. The prescribed profile attains the value, so it is exact terminal
Nash at every phase.

For the actual rewards r=1+Z, every profile obtained by a unilateral deviation
still absorbs almost surely because its opponents do. The actual terminal
payoff is consequently exactly one plus its native payoff. The native
terminal comparisons therefore give the actual comparisons. In particular,
at the initial physical phase the exact payoff is 1+b*, approximately

```
(1.7469717664, 1.0001841878, 1.0013175262, 1.0000130244).
```

Finally, the opponent-deleted geometric tail gives a finite expected
absorption-time bound uniform over all deviations. If M bounds the absolute
raw rewards, the difference between terminal payoff and the T-stage average
payoff is at most M E[τ]/T (or the harmless bound 2M E[τ]/T under either
initial-stage convention). It tends to zero uniformly over deviations. The
same periodic profile is therefore an ε-Nash profile in every sufficiently
long finite-horizon game and has payoff converging to the single displayed
terminal target. This proves uniform equilibrium under the repository's fixed
target contract.

## 6. An open class in all sixty raw reward coordinates

Let Z'=r'−1, independently at every nonempty coalition; no normalization or
punishment identity is assumed for the perturbed table. For a triple with
active opponents u,v, put

```
d_∅ = Z'_a({a}),
d_u = Z'_a({a,u})−Z'_a({u}),
d_v = Z'_a({a,v})−Z'_a({v}),
d_uv= Z'_a({a,u,v})−Z'_a({u,v}).
```

The four active-gap coefficients become

```
c=d_∅−b[a],
a=d_u−d_∅+b[a],
b=d_v−d_∅+b[a],
d=d_uv−d_u−d_v+d_∅−b[a].
```

The same rational/quadratic construction therefore defines F_{r'} continuously
in all sixty entries, together with its first derivative in b, near {r}×X.
The discriminants, nonzero denominators, proper hazard bounds, inactive
inequalities, derivative bound, and strict self-map inequality have positive
margins on the compact cube X. By continuity, all persist on a sufficiently
small full sixty-dimensional open neighborhood of r. For example one can
relax the contraction bound to 1/2 and the center-residual bound to one quarter
of the radius. Compactness supplies one common neighborhood for all stages
and b∈X. The contraction theorem then gives a fixed point for every such r'.

The resulting profile still has positive opponent-deleted absorption, so the
previous actual-terminal and uniform-payoff arguments apply. This proves a raw
open class, not just the isolated rational center. No claim that the listed
10^−60 continuation radius is a reward-neighborhood radius is made.


## 7. Complete stationary comparison

A stationary prescription repeats one fixed hazard vector q∈[0,1]^4 at
every live date. Deviations remain unrestricted behavioral replacements.

### 7.1. The stationary field and exact complementarity

For the opposing independent quitter set B, let

    H_i=PRODUCT_(j!=i)(1-q_j),
    P_i=E Z_i(B), Q_i=E Z_i(B union{i}),
    F_i=(1-H_i)Q_i-P_i,

where Z_i(empty)=0 only in the passive expectation. Each F_i is independent
of q_i and has degree at most two in each other coordinate. All these fields
are constructed directly from the sixty displayed rewards.

**Proposition.** The only cube-complementary point is q=0:

    q_i F_i(q)>=0 and (1-q_i)F_i(q)<=0 for all i
      implies q=0.                                    (1)

For q!=0, put d=1-PRODUCT_i(1-q_i)>0. The stationary law absorbs surely,
and its native terminal payoff is

    V_i=[q_i Q_i+(1-q_i)P_i]/d.

Forced Quit has native endpoint Q_i. Forced Continue followed by the
prescribed stationary profile has endpoint P_i+H_i V_i. Exact algebra gives

    Q_i-V_i=(1-q_i)F_i/d,
    P_i+H_i V_i-V_i=-q_i F_i/d.                         (2)

Both deviations are complete legal responses. Adding the actual own offset
one preserves these endpoint differences, because the prescribed continuation
absorbs surely. Thus exact terminal Nash requires (1).

At q=0 the actual payoff is zero, and immediate Quit gives one. Hence (1)
plus this separate literal-Never comparison excludes EVERY exact stationary
terminal Nash profile. No translation of a positive Never probability has
been assumed. the analytic-origin and exhaustive-subdivision arguments below prove (1) exhaustively.

### 7.2. Analytic origin exclusion for every support size

Put delta=1/256. Suppose 0<||q||_infinity<=delta and (1) holds, and let S
be the positive support. Every active coordinate is strictly below one, so
F_i=0 for i in S. We separate the four possible support sizes.

For |S|=1, let a be the sole active owner and t=q_a. Choose an inactive
crossing receiver i with Gamma_ia<0. Direct one-opponent expansion gives

    F_i=t[J_ia t-Gamma_ia]>0,

contradicting the inactive inequality in (1).

For |S|=2, write S={i,j}. The same exact formula gives

    F_i=q_j[J_ij q_j-Gamma_ij].                         (3)

If the pair is crossing, Gamma_ij<0, so F_i>0. If it is a favorite pair,
Gamma_ij=J_ij+A_ij>J_ij>0 and q_j<1, so F_i<0.
Both contradict F_i=0. This argument covers all six pairs without any
small inverse estimate.

For |S|=3, choose its unique owner i whose favorite is absent, and let j,k
be the other active owners. Both Gamma_ij and Gamma_ik are negative.
Every participant reward is nonnegative, so Q_i>=0 and F_i>=-P_i.
Put b_j=-Gamma_ij, b_k=-Gamma_ik and p=Z_i({j,k})>=0. Since q_j,q_k>0,

    -P_i=q_j q_k[b_j/q_k+b_k/q_j-(b_j+b_k+p)]
         >=q_j q_k[(b_j+b_k)/delta-(b_j+b_k+p)].        (4)

The bracket is strictly positive in all four cases:

| S | i | b_j+b_k | p |
| --- | --- | --- | --- |
| 012 | 2 | 301/2000 | 0 |
| 013 | 3 | 13/125 | 1 |
| 023 | 0 | 4001/1000 | 1 |
| 123 | 1 | 3/10 | 0 |

Indeed delta(b_j+b_k+p)<b_j+b_k for every row. Thus F_i>0,
contradicting its active equality. The weak small crossing entries do not
force an unnecessarily tiny origin box.

For |S|=4, expand F(q)=-Gamma q+R(q), where R has only terms of total
degree at least two. Exact coefficient summation gives

    K=max_i SUM_(degree>=2 monomials) |coefficient of F_i|=1913/50.

Consequently ||R(q)||_infinity<=K||q||_infinity^2 on the unit cube. The
full inverse has exact infinity operator norm

    L=||Gamma^-1||_infinity=59425126500/10327361611.

All four coordinates of F vanish, so q=Gamma^-1 R(q) and

    ||q||_infinity<=LK||q||_infinity^2.

But

    LK delta=1136802669945/1321902286208<1,

a contradiction. Only the full inverse is needed in this case. This completes
the proof that the entire origin box contains no nonzero complementary point.

### 7.3. Exact exhaustive certificate on the remaining closed cube

The complete standalone checker is embedded in Appendix B.
It reads no external data. It reconstructs the literal table and F, checks
all the analytic facts in the analytic-origin argument, and generates a complete binary subdivision
of [0,1]^4. All arithmetic used for exclusion is rational or integer.

Before conversion, the checker asserts degree at most two in EVERY coordinate
of EVERY polynomial. Each F_i is then expressed in the tensor Bernstein basis
of degree (2,2,2,2). The polynomial lies between the minimum and maximum of its Bernstein
coefficients on the whole closed box. Its independence from q_i simply
corresponds to degree elevation along that coordinate. A positive common
denominator clears all initial coefficients.

For a degree-two slice (a0,a1,a2), exact midpoint subdivision gives the
following child numerators at FOUR TIMES the parent's positive denominator:

    left  = (4a0,2(a0+a1),a0+2a1+a2),
    right = (a0+2a1+a2,2(a1+a2),4a2).

The midpoint children are both closed, and their union is the parent. Every
split retains BOTH children. A box is closed only by one of these tests:

- it lies in the origin box already handled by the analytic-origin argument;
- some coordinate has lower endpoint>0 and every coefficient of F_i is
  strictly negative, contradicting q_i F_i>=0;
- some coordinate has upper endpoint<1 and every coefficient of F_i is
  strictly positive, contradicting (1-q_i)F_i<=0.

The strict coordinate requirements preserve all zero/sure faces. No boundary,
partial support, or shared split surface is discarded. The deterministic
run completes with 175585 total nodes, 87793 leaves, maximum depth62, and
exactly one analytic-origin leaf. The full binary identity
175585=2*87793-1 is checked. Every other leaf has an explicit strict integer
coefficient sign witness. Exhausting the node or depth budget raises an
error; it never accepts an unresolved box. This proves (1).

The optional `--write-certificate PATH` flag writes every leaf, box, split
path, strict bound and denominator. The ordinary reproduction command
regenerates the whole proof directly, so an enormous retained leaf dump
is unnecessary.

### 7.4. Positive gap over all stationary prescribed profiles

Let E(q) be the supremum terminal gain over all players and their complete
behavioral replacements against the stationary profile q. All payoffs are
bounded because the reward table is finite. We prove

    inf_(q in [0,1]^4) E(q)>0.                         (5)

For q!=0 the maximum of the eight nonnegative parts of the endpoint gains
in (2) is continuous, bounded above by E(q), and strictly positive by
the exhaustive-subdivision argument. It therefore has a positive minimum on every compact subset
bounded away from q=0. At q=0, immediate Quit gives E(0)>=1.
It remains to exclude a vanishing-gap sequence approaching q=0.

Suppose q^n!=0 tends to zero and E(q^n) tends to zero. Passing to a
subsequence, write t_n=SUM_i q_i^n>0 and q^n/t_n->w in the unit simplex.
For prescribed play, the total absorption probability is t_n+O(t_n^2),
and the native one-date absorbing numerator for owner i is

    SUM_j Gamma_ij q_j^n+O(t_n^2).

Hence its actual stationary terminal payoff tends to 1+(Gamma w)_i.
Its immediate-Quit value tends to one. Vanishing exploitability implies

    Gamma w>=0.                                       (6)

If w has singleton support a, choose a crossing receiver i with
Gamma_ia<0, contradicting (6). Thus w has at least two positive coordinates,
and every positive w_i is strictly below one.

For an i with w_i>0, the opponents' total hazard is
(1-w_i)t_n+o(t_n)>0. Literal Never against these opponents has actual value
converging to

    1+(Gamma w)_i/(1-w_i).

Its limiting gain is therefore w_i(Gamma w)_i/(1-w_i). By (6) and the
vanishing-gap assumption, (Gamma w)_i=0 for every positive w_i. Thus, with
S=support(w),

    Gamma_SS w_S=0, |S|>=2.                            (7)

Every such principal matrix is nonsingular. The exact determinants, listed
by support, are

    01: -11011/10000;       02: -1/500;
    03: -13/200000;         12: -3/100;
    13: -39/10000;          23: -1111/1000;
    012: 6601001/10000000;  013: 32747/5000000;
    023: 5252011/20000000;  123: 12189/500000;
    0123: 10327361611/10000000000.

These are recomputed directly by the checker. Equation(7) contradicts
w_S>0. Therefore no vanishing-gap sequence can approach the origin either.
Compactness of the hazard cube now proves (5). The deviations used here
are complete legal responses: immediate Quit, one-date Continue followed
by prescribed stationary play, and literal Never.

The conclusion restricts the PRESCRIBED profiles to stationary ones. It
provides no positive floor over arbitrary prescribed behavioral profiles,
and hence does not invoke the unrestricted counterexample equivalence.
It is compatible with the thirty-three-phase construction above.


## 8. Complete fixed-disjoint-pair comparison

Choose any partition into two pairs. Alternate the pairs, with every owner
using one fixed hazard in[0,1] whenever its pair is active. Both phase orders
are allowed; the other pair continues. This entire prescribed family has
a positive gap against unrestricted behavioral deviations.

### 8.1. Necessary equations for a proper four-owner schedule

Let m be the mate involution, and let {j,k} be i's opposite pair. Set

    p_i=J_i,m(i), c_i=p_i-Gamma_i,m(i)=-A_i,m(i),
    x_i=q_i/(1-q_i), V_i=p_i q_m(i), W_i=c_i x_m(i).

When every q_i is in (0,1), all opponents absorb geometrically. Thus native
annotations transfer correctly to actual rewards by adding one. Active
indifference forces the value V_i at i's active phase and W_i at its inactive
phase: its Quit endpoint is p_i q_m(i), and its Continue endpoint is
Gamma_i,m(i) q_m(i)+(1-q_m(i))W_i.

For its opposite pair define

    C_i(q)=Gamma_ij q_j(1-q_k)+Gamma_ik q_k(1-q_j)
           +P_i({j,k})q_jq_k+p_i q_m(i)(1-q_j)(1-q_k),
    Q_i(q)=J_ij q_j(1-q_k)+J_ik q_k(1-q_j)
           +Q_i({j,k})q_jq_k.

In the second formula Q_i on the left is the endpoint, while Q_i({j,k}) on
the right is the literal three-player participant reward defined in Section 1.
To avoid rational denominators define polynomial fields

    E_i(q)=(1-q_m(i))C_i(q)-c_i q_m(i),
    H_i(q)=(1-q_m(i))Q_i(q)-c_i q_m(i).                (1)

Every proper paired Nash must satisfy all four E_i=0 and H_i<=0. The first
are exact policy recursions; the second are the full inactive Quit tests.
No outsider-joining reward has been replaced by a cone cap.

For the friendly schedule 01|23, all c_i=-1. Then W_i=-x_m(i)<0, while
the inactive Quit expectation is nonnegative. This excludes that complete
proper schedule immediately.

For each crossing schedule, the origin and subdivision arguments below prove a stronger closed-cube fact:

    q in[0,1]^4, E(q)=0, H(q)<=0 implies q=0.          (2)

The origin is not a proper profile and is not Nash in the actual table.

### 8.2. Analytic exclusion of the origin box

In both crossing schedules the linear part of E is exactly Gamma q. Write
E(q)=Gamma q+R(q), with R containing only terms of total degree at least2.
Let K be the largest sum of absolute nonlinear monomial coefficients in
one E_i, and let L be the maximum absolute row sum of Gamma inverse.
Exact arithmetic gives

    L=59425126500/10327361611,
    K=15 for02|13, K=121/10 for03|12.

For q in[0,1]^4 and r=||q||_infinity, ||R(q)||_infinity<=K r^2. Therefore
E(q)=0 implies r<=LK r^2. Taking delta=1/256, the exact products are

    LK delta=222844224375/660951143104<1 for02|13,
    LK delta=359522015325/1321902286208<1 for03|12.

Consequently the only E-root in[0,delta]^4 is q=0. This proof needs no
support assumption, inactive condition, or numerical root approximation.

### 8.3. Complete exact cube subdivision

Each E_i and H_i has degree at most two separately in every coordinate.
For a polynomial sum_beta a_beta q^beta, its tensor Bernstein coefficient
of multidegree(2,2,2,2) at index alpha is

    b_alpha=sum_(beta<=alpha) a_beta
                           product_j binom(alpha_j,beta_j)/binom(2,beta_j).

The polynomial on the cube is a convex combination of these coefficients.
Clearing all rational denominators gives integer coefficient arrays for all
eight fields. A midpoint split along one coordinate changes its coefficient
slice (a0,a1,a2) to

    left =(4a0,2(a0+a1),a0+2a1+a2),
    right=(a0+2a1+a2,2(a1+a2),4a2),

at FOUR TIMES the previous common positive denominator. Thus every
subdivision and sign test can use Python integers without rounding.

Starting at the whole closed cube, bisect a longest side, with lowest-index
tie breaking, and retain BOTH closed children. A leaf is rejected if one
of the following holds:

1. Its upper corner is coordinatewise at most delta, using the origin argument.
2. Some E_i has all Bernstein coefficients strictly positive or all strictly
   negative, which contradicts E_i=0 on that entire closed box.
3. Some H_i has all coefficients strictly positive, which contradicts H_i<=0.

The deterministic exact checker terminates with

| Pair schedule | Nodes | Leaves | Maximum depth |
| --- | ---: | ---: | ---: |
| 02 / 13 | 103 | 52 | 32 |
| 03 / 12 | 689 | 345 | 39 |

Every leaf has one of the exact reasons above. Both children always remain
in the finite tree until certified, so their union covers the whole cube,
including every face and splitting hyperplane. No box is accepted because
it is small or a search budget expired. This proves (2).

### 8.4. Sure rates and zero rates

The complete sure-first classification in Section 9 excludes every root with
a sure owner, against arbitrary behavioral continuation.

An exact equilibrium's continuation after a positive-probability finite live
history must also be exact Nash: a profitable continuation replacement can
be appended after that history while preserving earlier play, multiplying
its positive gain by a positive probability. Thus if either scheduled phase
contains a sure hazard, its first occurrence is either initial or is reached
with positive probability from a preceding proper phase. The sure-first
theorem excludes it. We may henceforth assume every hazard is below one.

Suppose both phases have a positive hazard but some owner has hazard zero.
Because there are four disjoint assigned positions, at least one phase is
solo. Let i be its sole mixing owner. At that phase its forced native Quit
value is zero and no opponent quits. Proper mixing therefore forces its
value at the next, opposite phase also to be zero. At the opposite phase
at least one opponent has a positive proper hazard. There is strictly
positive probability that exactly that opponent quits, so immediate Quit
there has strictly positive native expected reward: every J_ij>0 and every
other participant reward is nonnegative. This contradicts the prescribed
zero value of i at that phase.

If one phase is empty, only the other phase absorbs. With two proper active
owners i,m, the empty-phase value equals the active-phase value V_i.
Active indifference gives

    V_i=J_i,m q_m,
    V_i=Gamma_i,m q_m+(1-q_m)V_i,
    hence J_i,m q_m=Gamma_i,m.                         (3)

Every directed crossing Gamma_i,m is negative, whereas J_i,m>0. Every
favorite Gamma_i,m=J_i,m+1 exceeds J_i,m. Therefore (3) is impossible in
either case for 0<q_m<1. With only one active owner, that owner eventually
quits alone. A negative-crossing observer then obtains actual payoff
1+Gamma_ji<1, while its immediate Quit guarantees at least1. With no active
owner, actual payoff is zero and immediate Quit gives one. These exhaust
all zero-hazard patterns and complete the proposition.

### 8.5. A strictly positive gap over the entire fixed-pair family

Let U_i(q) be the actual prescribed terminal payoff, B_i(q) the supremum
over all complete behavioral responses, and

    D(q)=max_i[B_i(q)-U_i(q)]>=0.

The supremum is at least the prescribed payoff. We prove inf D(q)>0 over
all three partitions, both phase orders, and q in[0,1]^4. Suppose otherwise.
The finite schedule choice can be fixed on a subsequence, and compactness
gives q_n tending to q*. We can assume D(q_n) tends to zero.

First suppose at least two coordinates of q* are positive. Joint and every
opponent-deleted absorption probability per period are then strictly positive.
The actual prescribed payoff U_i is a finite polynomial numerator divided
by 1-product_l(1-q_l), so it is continuous near q*.

The full cap is continuous there as well, not merely a chosen local cap.
Let H_i=product_(l!=i)(1-q_l), let E_i be i's passive expected reward within
one period against its opponents, and let L_i(0),L_i(1) be its pure deadline
payoffs at the two phases of the first period. These are polynomials in the
hazards. Literal Never pays N_i=E_i/(1-H_i). A deadline at phase t in period
k has payoff

    (1-H_i^k)N_i+H_i^k L_i(t).

Therefore B_i=max(N_i,L_i(0),L_i(1)); complete behavioral laws are mixtures
of these deadlines and Never. This is a finite maximum of continuous
functions while H_i<1. Consequently D(q*)=0, contradicting the preceding complete fixed-pair exclusion.

If q* has exactly one positive coordinate j, choose an observer i with
Gamma_ij<0. The prescribed payoff is still continuous because joint period
absorption is positive, and U_i(q*)=1+Gamma_ij<1. Immediate Quit guarantees
at least1 for this table against every opponent law. Hence
liminf D(q_n)>=-Gamma_ij>0, another contradiction.

It remains to treat q*=0, where division by absorption precludes a direct
continuity argument. AllNever has debt at least1, so along a subsequence we
may assume h_n=sum_i q_n,i>0. Pass to a further subsequence with
w_n=q_n/h_n tending to a vector w in the unit simplex. Within one period,
the probability that j quits alone first is q_n,j+O(h_n^2), simultaneous
first exits have total probability O(h_n^2), and total period absorption is
h_n+O(h_n^2). These bounds are uniform because there are finitely many
players and two phases. Geometric period repetition therefore gives

    U_i(q_n) tends to 1+(Gamma w)_i.                   (4)

Immediate Quit always guarantees1. From D(q_n) tending to zero we conclude
Gamma w>=0. A singleton vector w=e_j would violate this at a negative-cross
observer. Thus the support of w has at least two owners, and every positive
w_i is strictly below one.

For each i with0<w_i<1, the opponent period absorption is
h_n(1-w_n,i)+O(h_n^2). The same singleton calculation, now with player i
using Never, gives the actual limiting response payoff

    1+(Gamma w)_i/(1-w_i).

This is one admissible complete response. Taking limits in the inequality
B_i(q_n)-U_i(q_n)<=D(q_n) yields

    (Gamma w)_i>=(Gamma w)_i/(1-w_i).

Together with Gamma w>=0, this forces (Gamma w)_i=0 whenever w_i>0.
Let S be the support of w. Then Gamma_SS w_S=0. Every principal block of
Gamma of size at least2 is nonsingular: the two-by-two determinants are
-Gamma_ij Gamma_ji<0, the triple determinants for012,013,023,123 are

    6601001/10000000, 32747/5000000,
    5252011/20000000, 12189/500000,

and det Gamma=10327361611/10000000000. Hence w_S=0, contradicting that w
is a probability vector. This excludes the final possible vanishing-gap
sequence and proves the asserted positive infimum d. No explicit numerical
lower bound for d is claimed.

The gap is robust in all sixty original reward coordinates. For any fixed
profile or behavioral replacement, changing the absorbing reward table by
at most eta in sup norm changes its terminal payoff by at most eta; the
literal Never contribution remains zero. Taking response suprema preserves
this bound, so each exploitability changes by at most2eta, uniformly over
all fixed-pair profiles. Every sufficiently small reward perturbation thus
retains a positive gap over this entire architecture, without requiring the
perturbed table to retain zero native participant entries.

In particular these schedules cannot supply uniform-equilibrium witnesses
at arbitrarily small errors. For any fixed quitting profile and any fixed
behavioral deviation, bounded convergence takes finite-horizon average
payoffs to terminal payoffs. A profile that is an epsilon equilibrium for
all sufficiently long horizons is consequently an epsilon terminal Nash
profile against every behavioral replacement. The positive d excludes that
possibility for epsilon<d in this restricted family.


## 9. Complete sure-first and punishment comparison

### 9.1. The true punishment vector

For the actual table r, every participant payoff is at least1. Immediate
Quit therefore guarantees at least1 against EVERY independent opponent
profile, regardless of its calendar. Conversely opponents using Never hold
the player's complete response cap to exactly1: every finite deadline gets
the own singleton1 and Never gets0. Thus each actual punishment value is
EXACTLY1, attained by the opponents' AllNever profile.

This is also a direct lower bound for every continuation cap. The analogous
native punishment values are exactly zero. No minimax interchange, compact
attainment claim, or restricted opponent class is used.

### 9.2. Four complete sure-face classifications

For independent current hazards q, let g_i(q) be native forced-Quit payoff
minus native forced-Continue payoff at continuation zero. Thus g_i is the
independent expectation of the contact corners Delta_i(B), with
Delta_i(empty)=0, Delta_i({j})=-A_ij, the specified pair corners, and
Delta_i(I minus{i})=-1.

A native root at zero continuation obeys

    q_i>0 implies g_i>=0; q_i<1 implies g_i<=0.            (1)

The following is a COMPLETE audit of all opponent support patterns on
each face q_h=1. It classifies the three-player opponents' Nash conditions
first, then checks that the prospective sure owner would withdraw.

#### Sure owner0

Put x=q1,y=q2,z=q3. The three opponent gaps are

    g1=-1+2z(1-y),
    g2=[1+999x-(1001+999x)z]/1000,
    g3=[7-107x+93y(1-x)]/100.

If y>0, g2>=0 implies z<=(1+999x)/(1001+999x)<=1/2.
Then g1<0, so x=0. Now g3>0 forces z=1, a contradiction.
Therefore y=0. The remaining two gaps are 2z-1 and(7-107x)/100.
Neither x nor z can be0 or1, by their mutually contradictory forced signs.
Hence x=7/107,z=1/2. At this point g2=-999/2140<0, as required
for y=0, but

    g0=-13/214<0.

Thus the unique opponent equilibrium on this face cannot make owner0 sure.

#### Sure owner1

Put x=q0,y=q2,z=q3. The opponent gaps are

    g0=-1+2y(1-z),
    g2=[-12xz+2x+2z+3]/5,
    g3=[26(1-x)(1-y)-25]/25.

If z>0, g3>=0 forces x,y<=1/26. Then g0<0 gives x=0,
and g2>0 gives y=1, a contradiction. Therefore z=0. Now g2>0
forces y=1, and g0=1 forces x=1. The unique opponent equilibrium is
(q0,q2,q3)=(1,1,0), where

    g1=-1<0.

#### Sure owner2

Put x=q0,y=q1,z=q3. The opponent gaps are

    g0=6-5y-7z+5yz,
    g1=[3-5x-z+xz]/2,
    g3=-1+2x(1-y).

If x=0, g1>0 forces y=1, g3<0 forces z=0, and g0=1 contradicts
x=0. If x=1, g1=-1 forces y=0, g3=1 forces z=1, and g0=-1
contradicts x=1. Thus 0<x<1 and g0=0. Consequently

    z=(6-5y)/(7-5y) in[1/2,6/7],

so z is mixed and g3=0. This yields x=1/[2(1-y)] and y<1/2.
If y=0, then x=1/2,z=6/7 and g1=1/28>0, a contradiction.
Hence y is mixed too, and g1=0 becomes

    20y^2-30y+1=0.

The only root in (0,1/2) is y=(15-sqrt(205))/20. Therefore the
unique opponent equilibrium is

    q0=(-5+sqrt(205))/18,
    q1=(15-sqrt(205))/20,
    q3=(22-sqrt(205))/9.

At that point

    g2=(170187-12919sqrt(205))/18000<0.

The strict sign follows from
12919^2*205-170187^2=5251000036>0.

#### Sure owner3

Put x=q0,y=q1,z=q2. The opponent gaps are

    g0=[101(1-y)(1-z)-100]/100,
    g1=[-13xz+3x+3z+2]/5,
    g2=-1+2y(1-x).

If x>0, g0>=0 forces y,z<=1/101. Then g2<0 gives z=0,
and g1>0 gives y=1, a contradiction. Thus x=0. Now g1>0
forces y=1, and g2=1 forces z=1. The unique opponent equilibrium is
(q0,q1,q2)=(0,1,1), where

    g3=-1<0.

These four arguments include every zero, mixed, and sure opponent choice.
They prove that there is no native zero-continuation Nash root with a
sure owner.

### 9.3. Complete sure-first exclusion with arbitrary behavioral tails

Suppose an exact actual root with q_h=1 were followed by ANY complete
behavioral continuation. Every other owner i faces certain current
absorption if it Continues, so its current comparison is exactly g_i;
the continuation is irrelevant to that owner. Its root choices therefore
form one of the unique opponent equilibria classified above.

Let b_h be the actual full continuation cap of h. The punishment calculation gives b_h>=1.
Write H_h=product_(j!=h)(1-q_j). Adding one to nonempty native rewards
changes the sure owner's Quit-minus-Continue-cap comparison to

    g_h-H_h(b_h-1)<=g_h.

At the opponent equilibrium on every face, g_h<0. The sure owner therefore
has a profitable complete deviation beginning with Continue. This is a
contradiction. It proves the claimed exclusion of ALL sure-first roots,
including arbitrary mixed opponent supports and arbitrary behavioral tails.


## 10. Complete older raw-class comparison

The exclusions here concern entire parameter-selection sets. They do not
infer noncoverage from a failed solver or a single choice of weights. Every
normalization with zero own native rewards has the form λ_i Z_i on row i,
with λ_i>0; the actual own level is necessarily1. Strict sign obstructions
are unchanged by such scaling. Relabeling merely permutes the unique
favorite matching01|23 and the listed finite partitions.

### 10.1. Stationary, sure-first, and fixed-pair outputs

Sections 7–9 exclude respectively every stationary output, every fixed
disjoint-pair two-phase output, and every sure-first punishment-tail output.
These conclusions apply to all existential choices inside any producer of
those profiles. In particular they cover stationary large-coalition reward
productions regardless of the chosen reward ratios, bounded remainders,
coalition sizes or unspecified sufficiently-large thresholds: the final
produced nonzero vector would satisfy the stationary complementarity already
excluded in Section 7. They do not attempt to guess such thresholds from the
size of a few reward entries.

For two-phase inverse-cone, signed-column and bounded-inverse producers,
Section 8 excludes the actual strategy output for all partitions, all proper
hazards and both phase orders, even when a sufficient raw bound happens to
be weak. Section 9 covers the full induced sure-first game and the true
punishment continuation, so testing stationary repetition alone is not used
to dismiss a punishment-tail producer.

### 10.2. Every nontrivial response-invariant quotient

Partition the four players into any number of nonempty blocks, excluding
the discrete four-singleton partition. There are fourteen choices. On the
block-constant cube substitute q_i=t_B for i∈B in the stationary fields
F_i=(1−H_i)Q_i−P_i. Even after arbitrary positive recipient scaling, literal
response invariance would make any two rows in the same block proportional.
Two coefficient columns with a nonzero determinant disprove this.

The following table supplies such a minor for every partition. Coordinates
of monomial exponents follow the displayed order of blocks. The minor is
coefficient_i(α) coefficient_j(β)−coefficient_i(β) coefficient_j(α).
AppendixE recomputes these rational numbers from the entire literal table.

| Blocks | Rows i,j | α | β | Nonzero minor |
| --- | --- | --- | --- | ---: |
| 01/2/3 | 0,1 | (0,0,1) | (0,1,0) | −1999/5000 |
| 1/02/3 | 0,2 | (0,0,1) | (0,1,0) | 8080001/2000000 |
| 1/2/03 | 0,3 | (0,0,1) | (0,1,0) | −2611/10000 |
| 0/12/3 | 1,2 | (0,0,1) | (0,1,0) | 217/1000 |
| 012/3 | 0,1 | (0,1) | (1,0) | −188/625 |
| 12/03 | 1,2 | (0,1) | (1,0) | 519/10000 |
| 0/2/13 | 1,3 | (0,0,1) | (0,1,0) | −589/5000 |
| 02/13 | 0,2 | (0,1) | (1,0) | 6879/2000 |
| 2/013 | 0,1 | (0,1) | (1,0) | 19/5 |
| 0/1/23 | 2,3 | (0,0,1) | (0,1,0) | 12561/100000 |
| 01/23 | 0,1 | (0,1) | (1,0) | −2563/625 |
| 1/023 | 0,2 | (0,1) | (1,0) | −820719/2000000 |
| 0/123 | 1,2 | (0,1) | (1,0) | −18917/20000 |
| 0123 | 0,1 | (1) | (2) | 3881/250 |

Positive scaling multiplies each minor by the product of its two row factors,
so none can vanish. This checks the entire quotient selection, including the
one-block quotient for which linear coefficients alone would be insufficient.
The actual offset1 cancels identically from F, so these are also the actual
zero-discount response fields in the tracked definition cited in Section 11.

The discrete partition does not lower the dimension. Its complementary
matrix Γ is R0, but its degree is +1, so the degree-not-one exit is
unavailable. Indeed a nonzero w≥0 with Γw≥0 and w_i(Γw)_i=0 would
make Γ_SS singular on any support S of size at least two; all these
principal blocks were checked nonsingular in Section 8.5. Singleton support
violates a negative crossing row. This proves R0. At offset −1 a
complementary solution satisfies Γw=1+y with y≥0 and w_i y_i=0.
Since Γ⁻¹ is strictly positive, w=Γ⁻¹(1+y)>0, so y=0. There is
exactly one regular solution w=Γ⁻¹1, with local degree
sign(det Γ)=+1. This computes the R0 degree. Positive recipient scaling
preserves the argument. The strict matching signs, inverse positivity and
nonzero principal determinants persist nearby, as does this degree.

### 10.3. All positive odds and polynomial row weights

This comparison includes arbitrary positive constant or polynomial weights,
rather than one tested linear program. Choose any odds factors ρ_j>0 and
positive C¹ row factors m_i on the cube. Define

```
ψ_j(u)=ρ_j u_j/[1+(ρ_j−1)u_j],
D_j(u)=1+(ρ_j−1)u_j,
G_i(u)=m_i(u) ∏_{j≠i}D_j(u)² F_i(ψ(u)).
```

The usual positive multiaffine weights, with all sixteen vertex values
positive, are included. Choose either one favorite pair or both, orient each
chosen pair as preferred i and partner k, and let K be the cube with u_i≥u_k
for each oriented pair. The relevant wall guards imply

```
G_i(u)≥G_k(u) whenever u_i=u_k and u∈K.               (W)
```

No such choices exist for the literal center. Here is a direct proof,
independent of any particular sufficient Bernstein representation of(W).
Suppose they existed. Put v_i=2 for preferred owners and v_j=1 otherwise.
For η>0, Brouwer gives a fixed point of the continuous map
u↦projection_K(u+G(u)+ηv). At a tied interior pair, (W) gives a strictly
positive difference between the preferred and partner displacement; an order
constraint cannot support the fixed-point normal in the opposite direction.
At a tied lower cube corner, the preferred displacement is nonpositive and
larger than the partner displacement, so both are nonpositive; at a tied
upper corner, the partner displacement is nonnegative and smaller than the
preferred displacement, so both are nonnegative. At an untied pair the order
constraint is inactive. These normal-cone facts show ordinary coordinate
cube complementarity for G+ηv at the fixed point. Equivalently they follow
by writing the normal of u_k−u_i≤0 as a nonnegative multiple of(−1,1),
plus the coordinate cube normals. The two chosen pairs are disjoint, so the
argument covers their intersection.

Let η tend to zero and take a convergent subsequence. If the limit is nonzero,
positive factors and ψ transfer complementarity to a nonzero q for F,
contrary to Section 7. Suppose instead the fixed points u_η tend to zero.
At zero,

```
DG(0)=−M,       M=diag(m(0)) Γ diag(ρ).
```

Normalize by a_η=max(||u_η||∞,η), obtaining limits w=u_η/a_η and
τ=η/a_η, with w∈K, τ≥0 and max(||w||∞,τ)=1. For small η no upper
cube boundary is active. The coordinate complementarity and first-order
expansion consequently give

```
Mw≥τv,                  w_i[(Mw)_i−τv_i]=0.          (L)
```

If τ=0, a support of size at least two would make the corresponding
principal block of M singular; all such blocks are nonsingular because
those of Γ are, and positive diagonal factors preserve their determinants.
A singleton support contradicts a negative crossing row of M in Mw≥0.
Thus τ cannot be zero.

Choose any oriented pair i,k. Differentiating(W) at zero gives
(Mw')_i≤(Mw')_k for every ordered nonnegative w' tied on that pair.
For an arbitrary w∈K, decrease w_i to w_k to obtain such a w'. Restoring
w_i subtracts M_ki(w_i−w_k)≥0 from the row difference, since the diagonal
is zero and the favorite coefficient M_ki is positive. Therefore
(Mw)_i≤(Mw)_k throughout K. If w_k>0, also w_i>0 and(L) gives the
opposite strict difference τ(v_i−v_k)=τ>0. If w_k=0, row i has only
nonpositive crossing contributions, so (Mw)_i≤0<τv_i, again a contradiction.
The collapsing limit is impossible. This proves the claimed exclusion of
all odds, all positive row factors, all orientations and both selected-pair
counts. Additional positive recipient scalings are absorbed into m.

### 10.4. Direct finite sign, core, and cap obstructions

The following raw requirements also fail for every relabeling and admissible
positive row scale.

1. **Proper premium cores of size at most three.** A premium trap is a
   nonempty set S such that every i∈S has a coalition C⊆S containing i
   with r_i(C)>r_i({i}). Since every J_ij>0, the whole four-player set is
   already a trap, witnessed by any pair containing each owner. Its greatest
   premium core is therefore all four players. Any criterion requiring a
   greatest core of size two or three, including a joining-attractive or
   mixed-sign three-owner core, fails before its further sign tests.
2. **Negative-premium chamber or rotating-pair templates.** Every participant
   pair premium is strictly positive. The passive-triple chamber requires
   negative participant pair premiums, and the rotating-pair templates require
   a directed pair premium −b/2 with b>0. These strict contradictions hold
   under every labeling and persist under small raw perturbations. No
   neighborhood claim here relies on zero participant triple entries.
3. **Signed inverse-column inactive caps.** The inverse Γ⁻¹ is strictly
   positive, forcing all column signs to be positive. The required inactive
   joining caps have the form J_ij≤−B_i with B_i≥0 for a nonempty opposite
   pair. Each J_ij>0 contradicts them, for every schedule and free radius.
4. **Triple collision boxes.** Such a box requires
   c_ij=J_ij−Γ_ij>0 for all six directed pairs in a selected triple.
   Every triple contains a favorite pair and both favorite c entries are−1.
   Thus all four triple choices, all scale parameters, and all relabelings
   fail this necessary guard.
5. **Joint positive passive triples.** Their singleton guard requires two
   distinct recipients in one column to have positive Γ entries. Each column
   of the matching Γ has exactly one positive off-diagonal entry. This is
   impossible for every choice of three-owner block and outside owner.
6. **Finite-calendar participant caps.** Choose any two unmarked owners,
   any ordered partition of the remaining marked owners, and any positive
   marked weights. For a marked i and an unmarked j, the coalition{i,j}
   meets its first marked block only at i. The required weighted participant
   cap would read λ_i J_ij≤0, contrary to strict positivity. This covers
   every ordered partition, marking and positive weight selection before
   any calendar-polytope funding inequality is considered.
7. **Bounded inverse-corner joining caps.** Write B=Γ⁻¹. These bounds require
   inactive pair premiums≤ell_i, where
   ell_i=c_i κ r_min/2, κ≤1/4,
   r_min≤1/(32 U Q), Q≥3c_i, and U bounds every inverse entry above.
   Therefore ell_i≤1/(768 U). Under recipient scale λ, U≥B_ii/λ_i.
   At recipient1, every pair premium is at least λ_1/10, and

   ```
   (1/10)B_11 = 262600550/10327361611 > 1/768.
   ```

   This contradicts the required cap for any role of that recipient and any
   positive scaling, independently of every corner-selection parameter.
8. **Opposite-row order.** On favorite pair01, choosing0 preferred forces
   the row-scale ratio to be at least Γ_13/Γ_03=100 and at most
   Γ_10/Γ_01=1100/1001. Choosing1 preferred forces its reciprocal to be
   at least Γ_02/Γ_12=20 and at most Γ_01/Γ_10=1001/1100. Both are
   impossible. These inequalities are among the literal singleton passive
   comparisons and exclude every two-pair orientation. Section 10.3 also
   excludes the larger one-pair polynomial-weight selection.

### 10.5. Product-low and all trap-leaver selections

A product-low requirement asks that every absorbing independent product root
have some active owner whose forced-Quit payoff does not exceed its own solo
reward. The pure root on pair02 has active premiums J_02=2 and J_20=1/2000,
both strictly positive. It refutes that requirement exactly.

Every two-player set is a premium trap. On trap02, the joining differences
from the other owner's singleton are −A_02=6 and −A_20=1/1000, both
positive. Neither endpoint can be even a weak leaver of this trap. Thus no
support-specific leaver selection works, regardless of its protected-set
choice. A common leaver would have to belong to every trap, whereas every
owner is omitted by some two-player trap. Finally, a weighted trap-leaver
condition requires strictly positive weights on the trap and nonpositive
weighted joining sums on every proper nonempty subset. On trap02 and
coalition{2}, that sum is 6w_0>0. This excludes every weight selection,
including any version with a strict improvement requirement. All these
witnesses retain their strict signs under small raw perturbations and
positive recipient scaling.

### 10.6. No-harm owners and singleton escorts

A no-harm singleton owner j requires Γ_ij≥0 for every recipient i.
Every column here has a negative crossing entry, so no owner qualifies.
A singleton escort edge i→j requires Γ_ij≤0≤Γ_ji. Every unordered
pair has the same strict sign in both directions, so this directed graph
has no edges. Any balanced singleton-cycle certificate would force an
escort cycle of length at least two: after erasing zero phases and merging
consecutive copies of the same owner, each transition must have just those
two opposite weak signs. Thus this excludes all such singleton-cycle
certificates, including repeated-owner or zero-phase presentations.
These strict sign obstructions persist nearby and under positive scaling.

### 10.7. Every literal child, including withdrawal-security rows

Let C be any nonempty proper child set and h an outside owner. A literal
advance-only certificate requires nonnegative weights a_i, i∈C, and,
for every nonempty S⊆C, the necessary future and joining rows

```
−Z_h(S) ≤ Σ_(i∈C) a_i[−Z_i(S)],                         (F)
Z_h(S∪{h})−Z_h(S)
       ≤ Σ_(i∈C) a_i[Z_i(S∪{i})−Z_i(S)].              (J)
```

Own singleton levels are zero in this difference notation. The same formulas
come from actual rewards by subtracting each recipient's own singleton.
They are necessary even when the separate Never row is omitted.

First consider a singleton child{j}. Choose a crossing outsider h. In(J)
at S={j}, the left side is −A_hj>0 and the right side is zero. For a
two-owner child, take S=C and choose the outsider by

```
01→2, 02→3, 03→1, 12→0, 13→2, 23→1.
```

The left side is1, while every summand on the right is zero. For triple
children, the following selected joining rows suffice:

| C | h | S | Necessary row |
| --- | --- | --- | --- |
| 012 | 3 | 02 | 1≤−a_1 |
| 013 | 2 | 01 | 1≤−a_3 |
| 023 | 1 | 23 | 1≤−a_0 |

For C=123,h=0, future rows S=12 and S={2} are

```
0 ≤ −(13/10)a_1−(9/20)a_2−a_3,
4 ≤ (1/5)a_1−(11/10)a_3.
```

Their sum reads 4≤−(11/10)a_1−(9/20)a_2−(21/10)a_3≤0.
This completes all fourteen child choices, including all nonnegative weights.

Stronger deadline certificates add nonnegative withdrawal weights d_i and
replace the right side of(J) by

```
Σ_(i∈C) {a_i[Z_i(S∪{i})−Z_i(S)]+d_i W_i(S)}.         (JW)
```

Here W_i(S)=0 for i∉S. For |S|≥2 and i∈S it is the exact withdrawal
difference Z_i(S\{i})−Z_i(S). For S={i}, it is γ_i−r_i({i}),
where γ_i is the selected actual security floor. All the raw zero-floor,
evaluated-security and untruncated terminal-security versions obey
γ_i≤r_i({i})=1. For the untruncated version this follows directly from
the singleton row in its security linear program; its additional zero floor
is at most zero. Taking their maximum, or truncating it at zero, preserves
the upper bound. Hence singleton withdrawal contributions are nonpositive.
No supplied security strategy or numerical linear-program conclusion is used.

For singleton children the same crossing outsider contradicts(JW). For
crossing two-player children02,03,12,13 use the same full-child joining
rows as above. Both withdrawal coefficients are the corresponding negative
A entries, so they cannot help. For favorite child01, take h=2,S={1}:

```
3/5 ≤ −a_0+d_1(γ_1−1) ≤ 0.
```

For favorite child23, take h=1,S={2}:

```
3/2 ≤ −a_3+d_2(γ_2−1) ≤ 0.
```

For triple children choose the following crossing coalitions instead:

| C | h | S | Necessary row |
| --- | --- | --- | --- |
| 012 | 3 | 02 | 1≤−a_1−6d_0−(1/1000)d_2 |
| 013 | 2 | 13 | 1≤−a_0−(2/5)d_1−(1/25)d_3 |
| 023 | 1 | 03 | 1≤−a_2−(1/100)d_0−(7/100)d_3 |

All right sides are nonpositive. For C=123,h=0 the two future rows
already contradict each other, independently of every withdrawal weight.
Thus even these stronger security-enhanced deadline certificates fail for
every child, every outsider-family selection, and every nonnegative pair
of weight vectors. This includes the advance-only certificates as d=0.

Positive recipient scaling is harmless: divide each outsider inequality by
its positive scale and absorb child scales into its nonnegative weights.
The strict crossing withdrawal and advance coefficients in the selected
rows persist under small raw perturbations. Coefficients that vanish because
an owner already belongs to S vanish identically for every reward table.
The singleton bound γ_i≤r_i({i}) persists while own rewards stay positive.
Finally the summed future-row contradiction has all three advance
coefficients strictly negative and left side4. These facts prove robust
failure without assuming bounded weights or continuity of optimal weights.

### 10.8. Extent of the comparison

These are failures of the stated raw conditions, not claims of nonexistent
equilibria. The new cycle supplies an equilibrium precisely while those
older conditions or produced architectures are unavailable. Source-mode
reductions conditional on a global minimum, a supplied semantic source, or
an existing return certificate do not independently produce UE on every
raw table satisfying only J>0 and Γ⁻¹>0; they supply no alternative coverage
of this entire raw neighborhood. The center-level strict finite obstructions,
quotient minors, and the stationary and fixed-pair positive gaps persist on
a sufficiently small neighborhood. For sure-first roots the robustness also follows from compactness: under a
reward perturbation of size η every continuation cap is at least1−η and at
most a common finite reward bound. A sequence of newly admissible sure roots
would have a limit satisfying one of the excluded original face comparisons.
For positive polynomial weights, the stationary gap and matching singleton
signs exclude every nonzero complementary point nearby, and the argument of
Section 10.3 applies again. No enlargement of a finite profile search is
substituted for these complete comparisons.

## 11. Source correspondence, adapter, and Lean handoff

The exact existing declarations
`isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate` and
`isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate`
in `UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean` consume a finite
cyclic root sequence, its policy recursion, exact local root Nash, and for
every owner a strict opponent-cycle continuation product below one. These
are precisely the data constructed in Sections 2–6. The existing consumer
already permits arbitrary behavioral deviations and produces one fixed
uniform payoff. Citing it gives no Lean seal to the new finite producer.

The polynomial-to-root step corresponds to `IsεQuittingRootNash` in
`UniformEquilibrium/Quitting/Root/FirstBranch.lean`. The stationary comparison
uses the exact scalar identity
`stationaryQuittingGain_complementarity_iff_endpoints` in
`UniformEquilibrium/Quitting/Stationary/Gain.lean`. The quotient obstruction
in Section 10 uses the literal response-invariance definition
`QuittingResponseInvariantOnUnitCube` in
`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`.
The equality between the quotient fields and actual zero-discount fields
follows directly from `quittingDiscountedDisplacement` in
`UniformEquilibrium/Quitting/Stationary/DiscountedDisplacement.lean` and
`quittingDiscountedDisplacement_zero_playerwiseTranslation` in
`UniformEquilibrium/Quitting/Stationary/RewardRowTranslation.lean`.
The discrete quotient's degree calculation corresponds to
`r0Degree_eq_sign_det_of_nonnegative_inverse` in
`MathUE/LinearProgramming/NonnegativeInverseDegree.lean`.

The complete sure-first comparison also excludes
`QuittingSingletonBaseCertificate` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/SingletonBaseSemanticDispatch.lean`:
its owner quits surely, its other owners satisfy the same endpoint
conditions, and its owner floor balance uses the exact punishment value1.
Section 9 proves that none of the four faces can satisfy that balance,
regardless of the carrier used to produce the proposed root.

The literal guards in Sections 10.5–10.6 are the definitions
`HasProductLowQuittingPremium` in
`UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremium.lean`,
`HasSupportSpecificQuittingLeavers` in
`UniformEquilibrium/Quitting/Classification/SupportSpecificQuittingPremiumLeavers.lean`,
`IsCommonQuittingPremiumLeaver` in
`UniformEquilibrium/Quitting/Classification/CommonQuittingPremiumLeaver.lean`,
and `HasWeightedQuittingTrapLeavers` in
`UniformEquilibrium/Quitting/Classification/WeightedQuittingTrapLeavers.lean`.
The no-harm predicate is `QuittingNormalNoHarmSingletonOwner` in
`UniformEquilibrium/Quitting/Classification/LCP/ProjectiveQBarBehavioralDecoder.lean`.
The definitions `IsQuittingSingletonEscortEdge` and
`BalancedSingletonCycleCertificate.exists_escortCycle` in
`UniformEquilibrium/Quitting/Cycles/CyclicSingletonEscort.lean` supply the
precise escort-cycle correspondence, including repeated-owner presentations.

The necessary rows in Section 10.7 are those of
`CappedClockParentRewardCertificate` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockPointwiseDomination.lean`,
`CappedClockParentFutureJoinCertificate` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockPositiveSingletonQuietExtension.lean`,
`DeadlineWithdrawalRewardCertificate` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalRaw.lean`,
`DeadlineSecurityRewardCertificate` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalSecurityMixedRaw.lean`,
and `DeadlineSecurityTerminalRewardCertificate` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalSecurityTerminalDebt.lean`.
The singleton upper bound is
`deadlineWithdrawalSecurityValue_le_singleton` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalSecurityLP.lean`;
the unchanged nonsingleton withdrawal formula is
`deadlineSecurityGainFloorWithRestart` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalRestartPointwiseCore.lean`.
These source files are tracked. No paper-derived theorem is invoked.

The missing formal producer is finite: define the rational sixty-entry
center, the three explicit algebraic triple-root maps, the rational cube,
and their thirty-three-fold composition. Prove the interval enclosure rules
by induction over arithmetic expressions, then the stated finite derivative,
branch, and gap bounds. Apply a complete-metric-space contraction theorem
and reverse the prefix word to construct the cyclic roots. The cycle values
satisfy the existing compiler's policy and root Nash hypotheses algebraically;
positive opposing hazards give its contraction hypothesis. A nearby-reward
version follows from uniform continuity of the finite formulas on the compact
cube and the strict margins. The declaration should conclude existence of
roots from the raw reward inequalities, not place their existence in a
certificate structure assumed by the theorem.

The comparison certificates use exact polynomial algebra and finite tensor
Bernstein subdivision; each leaf can be checked by rational identities and
strict inequalities. Their purpose is the complete old-class comparison,
not an unrestricted negative theorem. Keep the small-origin support analysis
separate from the finite closed-cube cover and from the gap compactification.
No `sorry`, new axiom, unsafe executable assertion, or unproved table-specific
oracle is required. The narrow checks are the new finite algebra/interval
modules and the existing periodic compiler; an integration claim requires its
actual dependency build and trust audit.

## 12. Boundary tests and scope

The positive center and every sufficiently nearby raw table have the produced
proper periodic Nash profile. The certified gaps distinguish all99 active
choices from all33 inactive choices. Every opponent-deleted survival contracts,
so literal Never is covered. The prefix order is reversed for physical play;
that orientation is part of the construction, not an arbitrary convention.

Negative tests are complete over the stationary cube, all fixed disjoint-pair
schedules including zero/sure boundaries, and every sure-first face with an
arbitrary continuation. All-null hazard limits are treated separately and are
not silently identified with limits of positive absorption. The quotient and
raw-guard comparisons in Section 10 quantify over their full selection sets.

There is no claimed global exploitability gap, universal longer-period bound,
classification of all periodic equilibria, or solution of Fin4. No particular
numerical reward-neighborhood radius is asserted. The native offset is used
for terminal comparisons only where opponent-deleted absorption supplies its
validity; the raw perturbation proof works directly with all sixty changed
entries through the formulas of Section 6.


## Appendix A. The complete cycle contraction checker

Save the following complete block as a Python file and run it. Appendix A
uses the standard library; Appendices B and C additionally use SymPy and NumPy
with Python integer object arrays. None reads external proof data.

```python
"""Exact dyadic interval validation of the secure table's 33-stage cap cycle."""
from fractions import Fraction as F
from itertools import combinations
from math import isqrt
import time
BITS=512;D=1<<BITS
class Iv:
 def __init__(self,lo,hi=None,raw=False):
  if raw:self.lo,self.hi=lo,hi;return
  x=F(lo);self.lo=x.numerator*D//x.denominator;self.hi=-((-x.numerator*D)//x.denominator)
 @classmethod
 def box(cls,c,r):
  a=cls(F(c)-F(r));b=cls(F(c)+F(r));return cls(a.lo,b.hi,True)
 def __add__(self,o):
  if isinstance(o,Jet):return NotImplemented
  o=iv(o);return Iv(self.lo+o.lo,self.hi+o.hi,True)
 __radd__=__add__
 def __neg__(self):return Iv(-self.hi,-self.lo,True)
 def __sub__(self,o):return self+-iv(o)
 def __rsub__(self,o):return iv(o)+-self
 def __mul__(self,o):
  if isinstance(o,Jet):return NotImplemented
  o=iv(o);xs=[a*b for a in(self.lo,self.hi)for b in(o.lo,o.hi)]
  return Iv(min(xs)//D,-((-max(xs))//D),True)
 __rmul__=__mul__
 def __truediv__(self,o):
  o=iv(o);assert not o.lo<=0<=o.hi,('zero denominator',o.lo,o.hi)
  pairs=[(a*D,b)for a in(self.lo,self.hi)for b in(o.lo,o.hi)]
  return Iv(min(a//b for a,b in pairs),max(-((-a)//b)for a,b in pairs),True)
 def __rtruediv__(self,o):return iv(o)/self
 def sqrt(self):
  assert self.lo>0
  a=isqrt(self.lo*D);b=isqrt(self.hi*D)
  return Iv(a,b+(b*b<self.hi*D),True)
 def absupper(self):return max(-self.lo,self.hi)
 def lower(self):return float(F(self.lo,D))
 def upper(self):return float(F(self.hi,D))
 def __repr__(self):return str((self.lower(),self.upper()))
def iv(x):return x if isinstance(x,Iv)else Iv(x)
class Jet:
 def __init__(self,v,d=None):self.v=iv(v);self.d=[Iv(0)]*4 if d is None else d
 def __add__(self,o):
  o=jet(o);return Jet(self.v+o.v,[a+b for a,b in zip(self.d,o.d)])
 __radd__=__add__
 def __neg__(self):return Jet(-self.v,[-x for x in self.d])
 def __sub__(self,o):return self+-jet(o)
 def __rsub__(self,o):return jet(o)+-self
 def __mul__(self,o):
  o=jet(o);return Jet(self.v*o.v,[a*o.v+self.v*b for a,b in zip(self.d,o.d)])
 __rmul__=__mul__
 def __truediv__(self,o):
  o=jet(o);v=self.v/o.v
  return Jet(v,[(a-v*b)/o.v for a,b in zip(self.d,o.d)])
 def __rtruediv__(self,o):return jet(o)/self
 def sqrt(self):
  v=self.v.sqrt();return Jet(v,[a/(2*v)for a in self.d])
def jet(x):return x if isinstance(x,Jet)else Jet(x)

A=[[F(x)for x in row]for row in[[0,1,-6,'-.01'],[1,0,'-1.5','-.4'],['-.001','-.6',0,1],['-.07','-.04',1,0]]]
J=[[F(x)for x in row]for row in[[0,'.001',2,'.009'],['.1',0,'1.3','.3'],['.0005','.45',0,'.01'],['.005','.001','.1',0]]]
Z={}
for i in range(4):
 Z[i,1<<i]=F(0)
 for j in range(4):
  if i!=j:Z[i,1<<j]=A[i][j]+J[i][j];Z[i,(1<<i)|(1<<j)]=J[i][j]
for pair,sg in zip(combinations(range(4),2),(1,-1,1,1,-1,-1)):
 mask=sum(1<<j for j in pair);outside=[i for i in range(4)if i not in pair]
 for n,i in enumerate(outside):
  delta=sg*(-1 if n else 1);Z[i,mask]=F(max(0,-delta));Z[i,mask|(1<<i)]=F(max(0,delta))
for i in range(4):Z[i,15^(1<<i)]=F(1);Z[i,15]=F(0)
assert len(Z)==60

def coeff(a,u,v,b):
 delta=Z[a,(1<<a)|(1<<u)|(1<<v)]-Z[a,(1<<u)|(1<<v)]
 return -b[a],b[a]-A[a][u],b[a]-A[a][v],delta+A[a][u]+A[a][v]-b[a]
def mul(a,b):return[a[0]*b[0],a[0]*b[1]+a[1]*b[0],a[1]*b[1]]
def step(b,S):
 i,j,k=map(int,S)
 ci,ai,bi,di=coeff(i,j,k,b);cj,aj,bj,dj=coeff(j,i,k,b);ck,ak,bk,dk=coeff(k,i,j,b)
 nx=[-cj,-bj];dx=[aj,dj];ny=[-ci,-bi];dy=[ai,di]
 terms=[mul(dx,dy),mul(nx,dy),mul(ny,dx),mul(nx,ny)]
 cc=[sum(t[l]*a for t,a in zip(terms,[ck,ak,bk,dk]))for l in range(3)]
 disc=cc[1]*cc[1]-4*cc[2]*cc[0]
 zz=(-cc[1]+disc.sqrt())/(2*cc[2]);q=[Jet(0)]*4
 q[i]=(nx[0]+nx[1]*zz)/(dx[0]+dx[1]*zz);q[j]=(ny[0]+ny[1]*zz)/(dy[0]+dy[1]*zz);q[k]=zz
 out=[];gs=[]
 for a in range(4):
  opp=[l for l in range(4)if l!=a];P=Jet(0);Q=Jet(0);H=Jet(1)
  for l in opp:H*=1-q[l]
  for bits in range(8):
   mask=0;wt=Jet(1)
   for ii,l in enumerate(opp):
    if bits>>ii&1:mask|=1<<l;wt*=q[l]
    else:wt*=1-q[l]
   if mask:P+=wt*Z[a,mask]
   Q+=wt*Z[a,mask|(1<<a)]
  out.append(P+H*b[a]);gs.append(Q-out[-1])
 return out,q,gs
word=['012','023','023']+['123']*30

def compose(center,radius,verbose=False):
 b=[Jet(Iv.box(x,radius),[Iv(int(i==j))for j in range(4)])for i,x in enumerate(center)]
 minq=D;maxq=0;inactive=-10*D;surv=Iv(1);rows=[]
 for t,S in enumerate(word):
  b,q,g=step(b,S)
  for i in map(int,S):
   assert q[i].v.lo>0 and q[i].v.hi<D
   minq=min(minq,q[i].v.lo);maxq=max(maxq,q[i].v.hi)
  assert all(g[int(i)].v.lo <= 0 <= g[int(i)].v.hi for i in S)
  omitted=next(i for i in range(4)if str(i)not in S)
  assert g[omitted].v.hi<0
  inactive=max(inactive,g[omitted].v.hi)
  for i in range(4):surv*=1-q[i].v
  rows.append({'support':S,'cap':[(x.v.lower(),x.v.upper())for x in b],'hazards':[(x.v.lower(),x.v.upper())for x in q],'inactive':g[omitted].v.upper()})
  if verbose:print('phase',t,'width',max((x.v.hi-x.v.lo)/D for x in b),flush=True)
 return b,{'minq':minq,'maxq':maxq,'inactive':inactive,'survival':surv,'rows':rows}

if __name__=='__main__':
 center=[F(x)for x in ['0.746971766391142631747982490611703517164463718609281026818174001524778730596987606012303673930513712347244600812299209278', '0.00018418776079822790285705212474507500368315100349555425139372625053395061379893554378678382430412440164849055871573954391', '0.00131752619879242749630650150229436975123175417602810509401756448580761853697710351614407670114265934720362522779979888247', '0.0000130244289556225569837393244851417510823520742208589393066816037443145447071555352352519034352752099446492393669958639411']];radius=F(1,10**60)
 start=time.time();image,stats=compose(center,radius)
 lip=max(sum(x.absupper()for x in row.d)for row in image)
 assert lip*100<D,('Lipschitz',float(F(lip,D)))
 atcenter,_=compose(center,0)
 residual=max((atcenter[i].v-Iv(center[i])).absupper()for i in range(4))
 assert F(residual,D)<radius/100
 assert F(residual,D)+F(lip,D)*radius<radius
 assert stats['minq']*10000>D
 assert stats['maxq']*10<7*D
 assert stats['inactive']*100<-7*D
 assert stats['survival'].hi*1000<D
 print('PASS: exact dyadic interval contraction; Lipschitz < 1/100; residual < radius/100; radius',radius)
 print('PASS: all99 active hazards >1/10000 and <7/10; all33 omitted gaps <-7/100; joint survival <1/1000.')
 print('actual bounds:',float(F(lip,D)),float(F(residual,D)),stats['survival'],'time',time.time()-start)

```

## Appendix B. The complete stationary closed-cube checker

Save the following complete block as a Python file and run it. Appendix A
uses the standard library; Appendices B and C additionally use SymPy and NumPy
with Python integer object arrays. None reads external proof data.

```python
"""Exact complete stationary exclusion for the secure exceptional full table.

Python 3, SymPy, NumPy. All proof arithmetic is rational or integer.
The table is reconstructed from literal finite data, with actual rewards Z+1.
The analytic origin checks cover all support sizes. Both closed children of
all dyadic splits are checked, covering every zero, mixed and sure cube face.
A budget exhaustion raises an error, never a proof result. The optional
--write-certificate flag writes all leaves; no external data are required.
This is a stationary architecture obstruction, not a UE counterexample.
"""
import argparse
import itertools
import json
from fractions import Fraction
import numpy as np
import sympy as s

I=tuple(range(4))
Q=Fraction
q=s.symbols('q0:4')
FAVORITE=(1,0,3,2)

def table():
    R=s.Rational
    A=s.Matrix([[0,1,-6,-R(1,100)], [1,0,-R(3,2),-R(2,5)],
        [-R(1,1000),-R(3,5),0,1], [-R(7,100),-R(1,25),1,0]])
    J=s.Matrix([[0,R(1,1000),2,R(9,1000)], [R(1,10),0,R(13,10),R(3,10)],
        [R(1,2000),R(9,20),0,R(1,100)], [R(1,200),R(1,1000),R(1,10),0]])
    Gamma=A+J
    z={(i,0):s.S.Zero for i in I}
    for i in I:
        z[i,1<<i]=s.S.Zero
        for j in I:
            if j!=i:
                z[i,1<<j]=Gamma[i,j]
                z[i,(1<<i)|(1<<j)]=J[i,j]
    for pair,sign in zip(itertools.combinations(I,2),(1,-1,1,1,-1,-1)):
        mask=sum(1<<j for j in pair)
        outside=[i for i in I if not mask>>i&1]
        for order,i in enumerate(outside):
            delta=sign*(-1 if order else 1)
            z[i,mask]=s.sympify(max(0,-delta))
            z[i,mask|(1<<i)]=s.sympify(max(0,delta))
    for i in I:
        z[i,15^(1<<i)]=s.S.One
        z[i,15]=s.S.Zero
    assert len(z)==64
    return z

def fields(z):
    H=[];P=[];QQ=[]
    for i in I:
        pp=qq=0
        for mask in range(16):
            if mask>>i&1:continue
            w=s.prod(q[j] if mask>>j&1 else 1-q[j] for j in I if j!=i)
            pp+=z[i,mask]*w
            qq+=z[i,mask|1<<i]*w
        H.append(s.prod(1-q[j] for j in I if j!=i))
        P.append(s.expand(pp));QQ.append(s.expand(qq))
    F=[s.Poly(s.expand((1-H[i])*QQ[i]-P[i]),*q)for i in I]
    g=[s.expand(QQ[i]-P[i])for i in I]
    return H,F,g

def coefficients(polys):
    assert all(poly.degree(q[j])<=2 for poly in polys for j in I)
    raw=[]
    for i in I:
        for alpha in itertools.product(range(3),repeat=4):
            value=sum(v*s.prod(s.binomial(alpha[j],mon[j])/s.binomial(2,mon[j])
                        for j in I) for mon,v in polys[i].terms()
                        if all(mon[j]<=alpha[j] for j in I))
            raw.append(s.sympify(value))
    denominator=int(s.ilcm(*(s.denom(v)for v in raw)))
    arr=np.array([int(v*denominator)for v in raw],dtype=object).reshape(4,3,3,3,3)
    return denominator,arr

def split_coefficients(b,axis):
    # Both child arrays represent their exact polynomials at FOUR TIMES
    # the parent's positive common denominator. Thus all sign tests below
    # use integers only; no interval rounding or tolerance is involved.
    v=np.moveaxis(b,axis+1,-1)
    a0,a1,a2=v[...,0],v[...,1],v[...,2]
    middle=a0+2*a1+a2
    left=np.stack((4*a0,2*(a0+a1),middle),axis=-1)
    right=np.stack((middle,2*(a1+a2),4*a2),axis=-1)
    return np.moveaxis(left,-1,axis+1),np.moveaxis(right,-1,axis+1)

def certify(polys,lo,hi,origin_delta=None,max_nodes=200000,max_depth=120):
    denominator,b=coefficients(polys)
    stack=[(list(lo),list(hi),b,0,'')]
    leaves=[];nodes=0;maxdepth=0
    while stack:
        lo,hi,b,depth,path=stack.pop()
        nodes+=1;maxdepth=max(maxdepth,depth)
        record={'path':path,'lo':list(map(str,lo)),'hi':list(map(str,hi))}
        if origin_delta is not None and max(hi)<=origin_delta:
            record['kind']='origin';leaves.append(record);continue
        witness=None
        for i in I:
            row=b[i].flatten()
            if lo[i]>0 and max(row)<0:
                witness=(i,'negative',int(max(row)));break
            if hi[i]<1 and min(row)>0:
                witness=(i,'positive',int(min(row)));break
        if witness is not None:
            i,sign,bound=witness
            record.update(kind='field',owner=i,sign=sign,numerator=str(bound),
                          denominator=str(denominator*4**depth))
            leaves.append(record);continue
        if depth>=max_depth or nodes>=max_nodes:
            raise RuntimeError('Unexcluded box after budget: '+str({
                'nodes':nodes,'depth':depth,'lo':list(map(str,lo)),
                'hi':list(map(str,hi)),'stack':len(stack)}))
        widths=[hi[i]-lo[i]for i in I]
        maximum=max(widths)
        choices=[i for i in I if widths[i]==maximum]
        axis=choices[depth%len(choices)]
        left,right=split_coefficients(b,axis)
        middle=(lo[axis]+hi[axis])/2
        lower=lo.copy();lower[axis]=middle
        upper=hi.copy();upper[axis]=middle
        # Every split retains BOTH closed children, whose union is the
        # parent. Starting with the whole cube or face proves coverage.
        stack.append((lower,hi,right,depth+1,path+str(axis)+'1'))
        stack.append((lo,upper,left,depth+1,path+str(axis)+'0'))
    assert nodes==2*len(leaves)-1
    return {'nodes':nodes,'depth':maxdepth,'source_denominator':denominator,'leaves':leaves}

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--write-certificate')
    parser.add_argument('--max-nodes',type=int,default=200000)
    parser.add_argument('--max-depth',type=int,default=120)
    parser.add_argument('--origin-only',action='store_true')
    args=parser.parse_args()
    z=table();H,F,g=fields(z)
    Gamma=s.Matrix([[z[i,1<<j] for j in I] for i in I])
    J=s.Matrix([[z[i,(1<<i)|(1<<j)] if i!=j else 0 for j in I] for i in I])
    A=Gamma-J
    assert A.det()==s.Rational(2742627,5000000)
    assert Gamma.det()==s.Rational(10327361611,10000000000)
    assert min(A.inv())==s.Rational(142000,2742627)
    assert min(Gamma.inv())==s.Rational(65494000,10327361611)
    assert all(z[i,1<<i]==0 for i in I)
    assert all(J[i,j]>0 for i in I for j in I if i!=j)
    assert all(z[i,m]>=0 for i in I for m in range(1,16)if m>>i&1)
    for M in (Gamma,A):
        assert all(v>0 for v in M.inv())
        for i in I:
            assert M[i,FAVORITE[i]]>0
            assert all(M[i,j]<0 for j in I if j not in (i,FAVORITE[i]))
    assert all(F[i].coeff_monomial(1)==0 for i in I)
    assert all(F[i].coeff_monomial(q[j])==-Gamma[i,j] for i in I for j in I)
    K=max(sum(abs(v)for mon,v in f.terms()if sum(mon)>=2)for f in F)
    L=s.S.Zero;principal_records=[]
    for n in range(2,5):
        for support in itertools.combinations(I,n):
            principal=Gamma.extract(support,support)
            assert principal.det()!=0
            inverse=principal.inv()
            norm=max(sum(abs(v)for v in inverse.row(i))for i in range(n))
            L=max(L,norm)
            principal_records.append({'support':support,'determinant':str(principal.det()),'inverse_norm':str(norm)})
    # Each singleton support has a strictly positive inactive crossing field.
    for owner in I:
        other=next(i for i in I if i not in (owner,FAVORITE[owner]))
        tt=s.Symbol('t')
        got=F[other].as_expr().subs({q[i]:tt if i==owner else 0 for i in I})
        assert s.expand(got-tt*(J[other,owner]*tt-Gamma[other,owner]))==0
        assert J[other,owner]>0 and Gamma[other,owner]<0
    # The crude maximum principal inverse norm is unnecessary: two-support
    # roots are excluded by exact one-opponent signs, and triple roots by
    # the active owner whose favorite is absent. Only full support needs L.
    inverse=Gamma.inv()
    L=max(sum(abs(v)for v in inverse.row(i))for i in I)
    power=1
    while K*L>=2**power:power+=1
    delta=Q(1,2**power)
    dd=s.Rational(delta.numerator,delta.denominator)
    for pair in itertools.combinations(I,2):
        i,j=pair
        tt=s.Symbol('t')
        got=F[i].as_expr().subs({q[h]:tt if h==j else 0 for h in I})
        assert s.expand(got-tt*(J[i,j]*tt-Gamma[i,j]))==0
        assert Gamma[i,j]<0 or Gamma[i,j]>J[i,j]>0
    triple_records=[]
    for support in itertools.combinations(I,3):
        owner=next(i for i in support if FAVORITE[i] not in support)
        j,k=[h for h in support if h!=owner]
        cross_sum=-Gamma[owner,j]-Gamma[owner,k]
        passive=z[owner,(1<<j)|(1<<k)]
        assert cross_sum>0 and passive>=0
        assert dd*(cross_sum+passive)<cross_sum
        triple_records.append({'support':support,'active_owner':owner,
            'cross_sum':str(cross_sum),'passive_pair':str(passive)})
    assert K*L*s.Rational(delta.numerator,delta.denominator)<1
    assert K==s.Rational(1913,50)
    assert L==s.Rational(59425126500,10327361611)
    assert delta==Q(1,256)
    assert K*L*dd==s.Rational(1136802669945,1321902286208)<1
    print('PASS: all-support origin, K=',K,'L=',L,'delta=',delta,flush=True)
    if args.origin_only:return
    stationary=certify(F,[Q(0)]*4,[Q(1)]*4,delta,args.max_nodes,args.max_depth)
    assert stationary['nodes']==175585
    assert len(stationary['leaves'])==87793 and stationary['depth']==62
    assert sum(leaf['kind']=='origin'for leaf in stationary['leaves'])==1
    print('PASS: entire stationary cube;175585 nodes,87793 leaves,depth62')
    print('PASS: all eleven nontrivial principal singleton blocks are nonsingular')
    print('SCOPE: only stationary prescribed profiles; no unrestricted exploitability gap')
    payload={'native_table':[[str(z[i,m])for m in range(16)]for i in I],
             'K':str(K),'L':str(L),'delta':str(delta),'principal':principal_records,'triple_origin':triple_records,'stationary':stationary}
    if args.write_certificate:
        with open(args.write_certificate,'w')as out:json.dump(payload,out,indent=2);out.write('\n')
        print('Wrote exact certificate',args.write_certificate)

if __name__=='__main__':main()
```

## Appendix C. The complete fixed-pair closed-cube checker

Save the following complete block as a Python file and run it. Appendix A
uses the standard library; Appendices B and C additionally use SymPy and NumPy
with Python integer object arrays. None reads external proof data.

```python
"""Exact proper alternating-pair exclusion for the secure exceptional table.

Python 3, SymPy, NumPy. All proof arithmetic is rational or Python integer.
All sixty rewards and proof rules are supplied here; no data files are read.
Optional --write-certificate PATH records every exact dyadic leaf.
This excludes proper four-owner two-pair Nash, not arbitrary equilibria.
"""
import argparse
import itertools
import json
from fractions import Fraction
import numpy as np
import sympy as s

I=range(4)
A=s.Matrix([[0,1,-6,-s.Rational(1,100)],
 [1,0,-s.Rational(3,2),-s.Rational(2,5)],
 [-s.Rational(1,1000),-s.Rational(3,5),0,1],
 [-s.Rational(7,100),-s.Rational(1,25),1,0]])
J=s.Matrix([[0,s.Rational(1,1000),2,s.Rational(9,1000)],
 [s.Rational(1,10),0,s.Rational(13,10),s.Rational(3,10)],
 [s.Rational(1,2000),s.Rational(9,20),0,s.Rational(1,100)],
 [s.Rational(1,200),s.Rational(1,1000),s.Rational(1,10),0]])
Gamma=A+J
q=s.symbols('q0:4')
SIGNS={(0,1):1,(0,2):-1,(0,3):1,(1,2):1,(1,3):-1,(2,3):-1}

def table():
    z={}
    for i in I:
        for mask in range(1,16):
            opp=[j for j in I if mask>>j&1 and j!=i]
            if not opp:
                value=0
            elif len(opp)==1:
                value=J[i,opp[0]] if mask>>i&1 else Gamma[i,opp[0]]
            elif len(opp)==2:
                outside=[j for j in I if j not in opp]
                delta=SIGNS[tuple(opp)]*(1 if i==outside[0] else -1)
                value=max(0,delta) if mask>>i&1 else max(0,-delta)
            else:
                value=0 if mask>>i&1 else 1
            z[i,mask]=s.Rational(value)
    return z

def fields(z,mate):
    equations=[];gaps=[]
    for i in I:
        j,k=[a for a in I if a not in(i,mate[i])]
        m=mate[i];p=J[i,m];c=-A[i,m]
        passive=z[i,(1<<j)|(1<<k)]
        joining=z[i,(1<<i)|(1<<j)|(1<<k)]
        D=(1-q[j])*(1-q[k])
        C=(Gamma[i,j]*q[j]*(1-q[k])+Gamma[i,k]*q[k]*(1-q[j])
           +passive*q[j]*q[k]+p*q[m]*D)
        Q=J[i,j]*q[j]*(1-q[k])+J[i,k]*q[k]*(1-q[j])+joining*q[j]*q[k]
        equations.append(s.Poly(s.expand((1-q[m])*C-c*q[m]),*q))
        gaps.append(s.Poly(s.expand((1-q[m])*Q-c*q[m]),*q))
    for i in I:
        assert equations[i].total_degree()<=4
        assert equations[i].coeff_monomial(1)==0
        for j in I:
            assert equations[i].coeff_monomial(q[j])==Gamma[i,j]
    assert all(p.degree(variable)<=2 for p in equations+gaps for variable in q)
    return equations,gaps

def coefficients(polys):
    raw=[]
    for p in polys:
        for alpha in itertools.product(range(3),repeat=4):
            raw.append(sum(value*s.prod(s.binomial(alpha[j],mon[j])/s.binomial(2,mon[j])
                           for j in I)for mon,value in p.terms()
                           if all(mon[j]<=alpha[j]for j in I)))
    denominator=int(s.ilcm(*(s.denom(v)for v in raw)))
    arr=np.array([int(v*denominator)for v in raw],dtype=object).reshape(8,3,3,3,3)
    return denominator,arr

def split(b,axis):
    v=np.moveaxis(b,axis+1,-1)
    a0,a1,a2=v[...,0],v[...,1],v[...,2]
    mid=a0+2*a1+a2
    left=np.stack((4*a0,2*(a0+a1),mid),axis=-1)
    right=np.stack((mid,2*(a1+a2),4*a2),axis=-1)
    return np.moveaxis(left,-1,axis+1),np.moveaxis(right,-1,axis+1)

def certify(z,mate):
    equations,gaps=fields(z,mate)
    L=max(sum(abs(v)for v in row)for row in Gamma.inv().tolist())
    K=max(sum(abs(v)for mon,v in p.terms()if sum(mon)>=2)for p in equations)
    delta=Fraction(1,256)
    assert L*K*s.Rational(1,256)<1
    den,b=coefficients(equations+gaps)
    stack=[(b,(Fraction(0),)*4,(Fraction(1),)*4,'')]
    leaves=[];nodes=0;maxdepth=0
    while stack:
        b,lo,hi,path=stack.pop();nodes+=1;maxdepth=max(maxdepth,len(path))
        reason=None;bound=None;index=None
        if max(hi)<=delta:
            reason='analytic_origin'
        else:
            flat=b.reshape(8,-1)
            mins=[min(row)for row in flat];maxs=[max(row)for row in flat]
            for i in I:
                if mins[i]>0:
                    reason,index,bound='equation_positive',i,int(mins[i]);break
                if maxs[i]<0:
                    reason,index,bound='equation_negative',i,int(maxs[i]);break
            if reason is None:
                for i in I:
                    if mins[4+i]>0:
                        reason,index,bound='inactive_gap_positive',i,int(mins[4+i]);break
        if reason is not None:
            leaves.append({'path':path,'reason':reason,'index':index,'integer_bound':bound,
                           'denominator':den*4**len(path),'lo':list(map(str,lo)),
                           'hi':list(map(str,hi))})
            continue
        if len(path)>=100 or nodes>1000000:
            raise RuntimeError('Unresolved box: no proof accepted at a stopping budget')
        axis=max(I,key=lambda i:hi[i]-lo[i]);mid=(lo[axis]+hi[axis])/2
        left,right=split(b,axis)
        lo1=list(lo);lo1[axis]=mid
        hi0=list(hi);hi0[axis]=mid
        stack.append((right,tuple(lo1),hi,path+'1'))
        stack.append((left,lo,tuple(hi0),path+'0'))
    return {'mate':mate,'L':str(L),'K':str(K),'delta':str(delta),
            'nodes':nodes,'maxdepth':maxdepth,'leaves':leaves}

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--write-certificate')
    args=parser.parse_args()
    z=table()
    assert all(z[i,mask]>=0 for i in I for mask in range(1,16)if mask>>i&1)
    assert all(Gamma.extract(S,S).det()!=0 for size in (2,3,4)
               for S in itertools.combinations(I,size))
    assert [Gamma.extract(S,S).det()for S in itertools.combinations(I,3)]==[
        s.Rational(6601001,10000000),s.Rational(32747,5000000),
        s.Rational(5252011,20000000),s.Rational(12189,500000)]
    assert Gamma.det()==s.Rational(10327361611,10000000000)
    friendly=(1,0,3,2)
    assert all(-A[i,friendly[i]]==-1 for i in I)
    records=[certify(z,mate)for mate in ((2,3,0,1),(3,2,1,0))]
    assert [(r['nodes'],len(r['leaves']),r['maxdepth'])for r in records]==[(103,52,32),(689,345,39)]
    if args.write_certificate:
        payload={'native_table':[[str(z[i,mask])for i in I]for mask in range(1,16)],
                 'records':records}
        with open(args.write_certificate,'w')as out:
            json.dump(payload,out,indent=2)
    for r in records:
        print('PASS',r['mate'],r['nodes'],'nodes',len(r['leaves']),'leaves',
              'depth',r['maxdepth'],'LKdelta',s.Rational(r['L'])*s.Rational(r['K'])/256)
    print('PASS all three proper four-owner alternating-pair schedules excluded')

if __name__=='__main__':
    main()
```

## Appendix D. Exact sure-face algebra and matrix data

```python
"""Exact full-table and complete sure-face algebra; no unrestricted-gap claim."""
from itertools import combinations, product
import sympy as s

R=s.Rational
A=s.Matrix([[0,1,-6,-R(1,100)], [1,0,-R(3,2),-R(2,5)],
            [-R(1,1000),-R(3,5),0,1], [-R(7,100),-R(1,25),1,0]])
J=s.Matrix([[0,R(1,1000),2,R(9,1000)], [R(1,10),0,R(13,10),R(3,10)],
            [R(1,2000),R(9,20),0,R(1,100)], [R(1,200),R(1,1000),R(1,10),0]])
Gamma=A+J
assert A.det()==R(2742627,5000000)
assert Gamma.det()==R(10327361611,10000000000)
assert min(A.inv())==R(142000,2742627)
assert min(Gamma.inv())==R(65494000,10327361611)
favorite=[1,0,3,2]
assert all(J[i,j]>0 for i in range(4) for j in range(4) if i!=j)
for M in (A,Gamma):
    assert all(M[i,favorite[i]]>0 for i in range(4))
    assert all(M[i,j]<0 for i in range(4) for j in range(4)
               if j not in (i,favorite[i]))

def table():
    Z={}
    for i in range(4):
        Z[i,1<<i]=s.S.Zero
        for j in range(4):
            if i!=j:
                Z[i,1<<j]=Gamma[i,j]
                Z[i,(1<<i)|(1<<j)]=J[i,j]
    for B, sign in zip(combinations(range(4),2),(1,-1,1,1,-1,-1)):
        C=sum(1<<j for j in B)
        outside=[i for i in range(4) if not C>>i&1]
        for order,i in enumerate(outside):
            delta=sign*(-1 if order else 1)
            Z[i,C]=s.sympify(max(0,-delta))
            Z[i,C|(1<<i)]=s.sympify(max(0,delta))
    for i in range(4):
        Z[i,15^(1<<i)]=s.S.One
        Z[i,15]=s.S.Zero
    return Z

Z=table()
assert len(Z)==60
assert all(value>=0 for (i,C),value in Z.items() if C>>i&1)
q=s.symbols('q0:4');g=[]
for i in range(4):
    opponents=[j for j in range(4) if j!=i]
    gi=s.S.Zero
    for bits in product((0,1),repeat=3):
        C=sum(v<<j for j,v in zip(opponents,bits))
        mass=s.prod(q[j] if v else 1-q[j] for j,v in zip(opponents,bits))
        gi+=mass*(Z[i,C|1<<i]-(Z[i,C] if C else 0))
    g.append(s.expand(gi))

x,y,z=s.symbols('x y z')
faces=[[-1+2*z*(1-y),(1+999*x-(1001+999*x)*z)/1000,
        (7-107*x+93*y*(1-x))/100],
       [-1+2*y*(1-z),(-12*x*z+2*x+2*z+3)/5,
        (26*(1-x)*(1-y)-25)/25],
       [6-5*y-7*z+5*y*z,(3-5*x-z+x*z)/2,-1+2*x*(1-y)],
       [(101*(1-y)*(1-z)-100)/100,(-13*x*z+3*x+3*z+2)/5,
        -1+2*y*(1-x)]]
for owner in range(4):
    opponents=[j for j in range(4) if j!=owner]
    substitution={q[owner]:1}|dict(zip([q[j] for j in opponents],(x,y,z)))
    for j,expected in zip(opponents,faces[owner]):
        assert s.expand(g[j].subs(substitution)-expected)==0

points=[(1,R(7,107),0,R(1,2)), (1,1,1,0),
        ((-5+s.sqrt(205))/18,(15-s.sqrt(205))/20,1,(22-s.sqrt(205))/9),
        (0,1,1,1)]
gaps=[-R(13,214),-1,(170187-12919*s.sqrt(205))/18000,-1]
for owner,point in enumerate(points):
    got=[s.simplify(gi.subs(dict(zip(q,point)))) for gi in g]
    assert s.simplify(got[owner]-gaps[owner])==0
    for i in range(4):
        if i==owner:continue
        if point[i]==0:assert got[i].is_nonpositive
        elif point[i]==1:assert got[i].is_nonnegative
        else:assert got[i]==0
assert 12919**2*205-170187**2==5251000036
assert 14**2<205<15**2
assert s.simplify(faces[2][1].subs({x:1/(2*(1-y)),z:(6-5*y)/(7-5*y)}) -
                  (20*y*y-30*y+1)/(4*(y-1)*(5*y-7))) == 0
print('PASS: sixty native entries, positive J/inverses, exact true punishment, four complete sure-face algebraic classifications.')

```

## Appendix E. Complete quotient, inverse-cap and raw-child arithmetic

```python
import argparse
import itertools
import json
from fractions import Fraction
import numpy as np
import sympy as s

I=tuple(range(4))
Q=Fraction
q=s.symbols('q0:4')
FAVORITE=(1,0,3,2)

def table():
    R=s.Rational
    A=s.Matrix([[0,1,-6,-R(1,100)], [1,0,-R(3,2),-R(2,5)],
        [-R(1,1000),-R(3,5),0,1], [-R(7,100),-R(1,25),1,0]])
    J=s.Matrix([[0,R(1,1000),2,R(9,1000)], [R(1,10),0,R(13,10),R(3,10)],
        [R(1,2000),R(9,20),0,R(1,100)], [R(1,200),R(1,1000),R(1,10),0]])
    Gamma=A+J
    z={(i,0):s.S.Zero for i in I}
    for i in I:
        z[i,1<<i]=s.S.Zero
        for j in I:
            if j!=i:
                z[i,1<<j]=Gamma[i,j]
                z[i,(1<<i)|(1<<j)]=J[i,j]
    for pair,sign in zip(itertools.combinations(I,2),(1,-1,1,1,-1,-1)):
        mask=sum(1<<j for j in pair)
        outside=[i for i in I if not mask>>i&1]
        for order,i in enumerate(outside):
            delta=sign*(-1 if order else 1)
            z[i,mask]=s.sympify(max(0,-delta))
            z[i,mask|(1<<i)]=s.sympify(max(0,delta))
    for i in I:
        z[i,15^(1<<i)]=s.S.One
        z[i,15]=s.S.Zero
    assert len(z)==64
    return z

def fields(z):
    H=[];P=[];QQ=[]
    for i in I:
        pp=qq=0
        for mask in range(16):
            if mask>>i&1:continue
            w=s.prod(q[j] if mask>>j&1 else 1-q[j] for j in I if j!=i)
            pp+=z[i,mask]*w
            qq+=z[i,mask|1<<i]*w
        H.append(s.prod(1-q[j] for j in I if j!=i))
        P.append(s.expand(pp));QQ.append(s.expand(qq))
    F=[s.Poly(s.expand((1-H[i])*QQ[i]-P[i]),*q)for i in I]
    g=[s.expand(QQ[i]-P[i])for i in I]
    return H,F,g

Z=table();_,F,_=fields(Z)
def parts(items):
 if not items:yield[];return
 x,*rest=items
 for p in parts(rest):
  yield[[x]]+[b[:]for b in p]
  for j in range(len(p)):yield[([x]+b if k==j else b[:])for k,b in enumerate(p)]
seen=[]
for p in parts(list(range(4))):
 if len(p)==4:continue
 t=s.symbols('t:'+str(len(p)));sub={q[i]:t[j]for j,b in enumerate(p)for i in b}
 polys=[s.Poly(f.as_expr().subs(sub),*t)for f in F];w=None
 for block in p:
  for i,j in itertools.combinations(block,2):
   monoms=sorted(set(polys[i].monoms())|set(polys[j].monoms()),key=lambda z:(sum(z),z))
   for a,b in itertools.combinations(monoms,2):
    d=polys[i].coeff_monomial(a)*polys[j].coeff_monomial(b)-polys[i].coeff_monomial(b)*polys[j].coeff_monomial(a)
    if d!=0:w=(i,j,a,b,d);break
   if w:break
  if w:break
 assert w;seen.append(p)
 print('|','/'.join(''.join(map(str,b))for b in p),'|',w[0:2],'|',w[2],'|',w[3],'|',w[4],'|')
assert len(seen)==14

B=s.Matrix(4,4,lambda i,j:0 if i==j else Z[i,1<<j]).inv()
assert B[1,1]/10==s.Rational(262600550,10327361611)>s.Rational(1,768)
print("PASS fourteen quotient obstructions and scaled inverse-cap obstruction")

Gamma=s.Matrix(4,4,lambda i,j:0 if i==j else Z[i,1<<j])
assert Gamma.det()==s.Rational(10327361611,10**10)>0
assert min(B)==s.Rational(65494000,10327361611)>0
for size in (2,3,4):
 for support in itertools.combinations(I,size):
  assert Gamma.extract(support,support).det()!=0
A=s.Matrix(4,4,lambda i,j:0 if i==j else Gamma[i,j]-Z[i,(1<<i)|(1<<j)])
assert Z[0,5]>0 and Z[2,5]>0 and -A[0,2]>0 and -A[2,0]>0
assert all(any(Gamma[i,j]<0 for i in I if i!=j) for j in I)
assert all(Gamma[i,j]*Gamma[j,i]>0 for i,j in itertools.combinations(I,2))

def join_row(child,h,mask):
 lhs=Z[h,mask|(1<<h)]-Z[h,mask]
 advance=[Z[i,mask|(1<<i)]-Z[i,mask] for i in child]
 # The exact security-floor singleton contribution is <=0. Substitute its
 # universal upper bound0, which only makes the required row easier.
 withdrawal=[]
 for i in child:
  if not mask>>i&1 or mask==(1<<i):withdrawal.append(s.S.Zero)
  else:withdrawal.append(Z[i,mask^(1<<i)]-Z[i,mask])
 return lhs,advance,withdrawal

checked=0
for mask in range(1,15):
 child=[i for i in I if mask>>i&1]
 if len(child)==1:
  j=child[0];h=next(i for i in I if i!=j and Gamma[i,j]<0);S=mask
 elif len(child)==2:
  h={3:2,5:3,9:1,6:0,10:2,12:1}[mask]
  S={3:2,12:4}.get(mask,mask)
 elif mask==14:
  h=0
  # Sum the two future rows S12 and S2, an exact nonnegative dual.
  lhs=-Z[h,6]-Z[h,4]
  coeff=[-Z[i,6]-Z[i,4] for i in child]
  assert lhs==4 and coeff==[-s.Rational(11,10),-s.Rational(9,20),-s.Rational(21,10)]
  assert lhs>0 and all(c<0 for c in coeff)
  checked+=1;continue
 else:
  h,S={7:(3,5),11:(2,10),13:(1,9)}[mask]
 lhs,advance,withdrawal=join_row(child,h,S)
 assert lhs>0 and all(a<=0 for a in advance) and all(d<=0 for d in withdrawal)
 # Every zero advance coefficient is an exact set-inclusion identity;
 # singleton withdrawal bounds and nonmember zero terms are structural.
 assert all(a<0 or S>>i&1 for i,a in zip(child,advance))
 assert all(d<0 or not S>>i&1 or S==(1<<i) for i,d in zip(child,withdrawal))
 checked+=1
assert checked==14
print("PASS R0 principal blocks, degree sign, product/leaver/sign witnesses, and all14 security-enhanced child duals")
```
