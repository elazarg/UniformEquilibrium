# CODEX_HILBERT — signed four-cycle intersection with the matrix residual

## Status and decisive result

Bounded independent test, ordinary mathematics; no Lean or export changes.
The four-phase architecture with a negative opposite comparison DOES
intersect the full-standard-Q, nonhomogeneous, non-projective-Q-bar Fin4
matrix class. An exact witness is the circulant comparison matrix with
offsets (0,-1,-1,6). Its standard-Q property follows from a strictly positive
inverse, not from finitely many tested right-hand sides.

This is a matrix-residual intersection, not a positive exploitability gap:
the displayed cycle produces UE for every reward table with these singleton
comparisons. The uniform fixture itself already feeds the checked general
equal-hazard tail criterion. A genuinely new producer claim should concern
the signed HETEROGENEOUS extension, not a new semantic compiler or an
unintegrated proof of the uniform fixture.

RENY independently found the same uniform witness while I was checking his
corrected heterogeneous candidate. I verified its exact inverse, LCP
transfer, proper-principal failure, homogeneous exclusion, and source scope.
His frozen heterogeneous Perron note was read but not edited.

## 1. Exact table data and cycle

Let players be 0,1,2,3 cyclically and s_i=r_i({i}) arbitrary. Put
Gamma_ij=r_i({j})-s_i. Take

    Gamma = [ 0  -1  -1   6 ]
            [ 6   0  -1  -1 ]
            [-1   6   0  -1 ]
            [-1  -1   6   0 ].

No nonsingleton reward is restricted. At successive phases 0,1,2,3,
activate only that phase's owner with hazard 1/2 and repeat forever.
Its cycle survival is 1/16. The owner-indifference scalar balance is

    -1 + (1/2)(-1) + (1/4)6 = 0.

For each player i, the four phase surpluses above s_i, in relative offsets
0,1,2,3, are respectively

    (0,0,1,3).

Indeed the singleton Bellman equation for surplus at offset k is
v_k=(1/2)gamma_k+(1/2)v_(k+1), with cyclic indices. Substitution verifies
all four equations. Thus every phase value is at least the singleton
reward, and the owner is indifferent at its phase. Deleted-opponent
survival through a whole cycle is (1/2)^3<1 for each player.

The author's standard fine-subdivision argument therefore controls all
finite pure Quit dates and Never, hence every complete behavioral
deviation. This narrow test is not a second full review of that compiler.

## 2. Exact full standard-Q proof

Let

    B = (1/1200) [ 37 209  13  41 ]
                 [ 41  37 209  13 ]
                 [ 13  41  37 209 ]
                 [209  13  41  37 ].

Direct rational multiplication gives Gamma B=B Gamma=I; det(Gamma)=-1200.
Every entry of B is strictly positive. For every nonzero x>=0,

    x dot (Bx) >= (37/1200) sum_i x_i^2 > 0.

Thus B is strictly copositive and is a textbook standard-Q matrix by the
checked `isStandardQ_of_strictlyCopositive` in
`MathUE/LinearProgramming/CopositiveQCorollaries.lean`, transported by
`isStandardQ_iff_isStandardQMatrix` in
`UniformEquilibrium/Quitting/Classification/LCP/CopositiveQBridge.lean`.

The inverse transfer is elementary and uses the exact convention in
`MatrixClasses.lean`. Fix any original right-hand side q. A standard LCP
solution for B at right-hand side -Bq consists of y>=0 and

    z = -Bq + By >= 0,       y_i z_i = 0.

Multiplying by Gamma gives y=q+Gamma z. Hence z is an original LCP
solution at q, with residual y. Since q was arbitrary, Gamma is standard Q.
No transpose or sign reversal of Gamma has been inserted; only the
transformed right-hand side and exchanged complementary variables occur.

## 3. No homogeneous solution; failure of projective Q-bar

Suppose z>=0, w=Gamma z>=0, and z_iw_i=0. Then z=Bw, so

    0=z dot w=w dot (Bw).

Strict copositivity of B forces w=0, hence z=0. There is therefore no
homogeneous simplex LCP solution on the full matrix.

The opposite principal on {0,2} is

    C = [0 -1; -1 0].

It is not standard Q: at q=(-1,-1), nonnegative z gives q+Cz<0 in both
coordinates. It has no homogeneous simplex solution either, because
Cz=(-z_2,-z_0)>=0 forces z=0. The checked
`isProjectiveQMatrix_iff_standard_or_homogeneous` in `MatrixClasses.lean`
therefore says C is not projective Q. Consequently Gamma is not
projective-Q-bar. The same opposite-principal argument works on {1,3}.

Every row has its distinct successor as a negative witness. The recursive
`normalLayer` definition in `NormalCore.lean` therefore retains every
player at every layer. The full algebraic normal core is all four players.
Combining this with Sections 2–3 gives every matrix field of the production
`ResidualHardClass`: nonempty normal core, no homogeneous solution,
standard-Q normal matrix, and failure of full projective-Q-bar.

This does not supply any no-UE witness or positive-debt minimum. If s_i>=0,
all players are also punishment-normal by P_i<=max(s_i,0)=s_i; that
separate normality notion is not used in the matrix argument.

## 4. The exact existing cyclic interface already accepts the fixture

The narrower `QuittingCyclicSingletonOpenSignData` in
`UniformEquilibrium/Quitting/Cycles/CyclicSingletonOpenSignProducer.lean`
does require later coefficients to be nonnegative, so it rejects gamma_2=-1.
But the SAME FILE already proves the more general theorem
`hasQuittingCanonicalEqualHazardTailData_iff`: for a cyclic singleton
matrix and 0<c<1, balance-polynomial zero and nonnegative canonical tails
are equivalent to canonical tail data.

At c=1/2 and gamma=(0,-1,-1,6), those tails are exactly

    tail = (0,0,2,6).

The payoff surpluses in Section 1 equal (1-c)tail, as required by
`CyclicSingletonTailData.coarse`. Thus the fixture directly supplies
`CyclicSingletonTailData`, whose `.certificate` and
`.isUniformEquilibriumPayoff` in `CyclicSingletonTailProducer.lean`
already handle every nonsingleton reward and unrestricted deviation.

Accordingly the signed fixture is not outside all existing source
consumers. What it establishes is that the architecture itself is NOT
confined to the ordinary-non-Q/projective-Q-bar union, contrary to what
the positive-opposite special case might suggest. Producing balanced tails
from heterogeneous signed raw coefficients may still be a real extension;
this note does not establish that broader producer.

## 5. Discarded finite checks and bounded verdict

Before the uniform witness, the author's corrected heterogeneous rational
matrix with b_i=1,

    g=(-5/2,9/10,4/5,15/8),
    h=(9,11/5,12/5,1/4)

passed all 1296 exact right-hand sides from {-9,-3,-1,1,3,9}^4 by
enumerating complementary supports. Its determinant is 309/80. That
finite test was not and is not a standard-Q proof; it is unnecessary for
the decisive witness above. Earlier index errors and a purported
alternating-right-hand-side obstruction were corrected by the author
before any claim was frozen; neither is used here.

The bounded task's answer is therefore affirmative and exact: allowing
negative opposite comparisons permits a balanced cycle on a genuine
full-standard-Q/non-Q-bar matrix. The old matrix-union subsumption fails
for this enlarged architecture. Existing generic tail consumers already
accept the uniform example, so further producer novelty must be assessed
at the heterogeneous raw-data boundary. No constant optimization or
additional regression search is needed for this conclusion.
