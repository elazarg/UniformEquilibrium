# Raw reward tests force a positive cap on specified absorbing faces

Owner: CODEX_COORDINATOR. Ordinary mathematics, not a Lean result.

## Result and current scope

Two finite weighted reward tests give a uniform lower bound on full
best-response caps in terms of absorption probability. The weights may
vanish. Consequently a tested set of coordinates cannot all have zero cap
in the absorbing semantic carrier, regardless of the other caps or debts.
This supplies a raw-table exclusion of boundary configurations in the
[zero-observer reduction](CODEX_COORDINATOR__ZERO_OBSERVER_BOUNDARY_REDUCTION.md),
including its all-zero endpoint. It does not give UE for every table passing
the tests, exclude every finite penalty plateau, or close the remaining
actual-minimum and other boundary branches. Retained as an internal proved
result under the export gate; no new existence class is claimed.

The mathematical text in commit `76432c60` passed two independent reviews:
[boundary review](../feedback/CODEX_COORDINATOR__WEIGHTED_CAP_ABSORPTION_COERCIVITY__BY_CODEX_BOUNDARY_ZEROS_27.md)
and [adversarial review](../feedback/CODEX_COORDINATOR__WEIGHTED_CAP_ABSORPTION_COERCIVITY__BY_CODEX_CAP_ADVERSARY_28.md).
Subsequent changes here concern this status paragraph only.

Let I have n>=2 players. A bounded native table Z satisfies Z_i({i})=0,
and live and AllNever rewards are zero. Fix M>=1 with |Z_i(A)|<=M.
Complete private stopping laws on the natural dates and Never are independent.
U is prescribed payoff, B_i is the supremum over ALL unilateral complete
law replacements, N_i is the original Never mass, and nu=product_i N_i.
All finite deadlines and Never are included in B; taking their supremum
already covers every behavioral replacement. Put Gamma_ij=Z_i({j}).

Suppose finite raw data z_i>=0, sum_i z_i=1, gamma>0 and kappa>0 satisfy

    sigma_j=sum_i z_i Gamma_ij >= gamma             for every j,
    K_A=sum_i z_i Z_i(A union {i}) >= kappa          for every nonempty A.
                                                               (1)

These are linear inequalities in z at a fixed reward table. They assume
no profile, selected root, continuation, equilibrium or minimum. Necessarily
gamma<=M and kappa<=M. Define

    C=1+2M/kappa,       L=1+5M/kappa,
    D=M*n^2/kappa+C*L,
    delta=min(kappa/2, gamma/(2D))>0.                            (2)

**Theorem.** Every actual profile satisfies, with w=sum_i z_i B_i,

    w>=delta*(1-nu).                                            (3)

If w<=delta, the sharper estimate 1-nu<=2w/gamma holds. Every actual
absorbing profile has w>delta. Hence every point of the closure K_abs of
actual absorbing (U,B) pairs has w>=delta.

Equation (3) also holds on the compact closure H of all actual tuples
(U,B,N,e), retaining original Never masses and pure-Never values e.
The only point of H with w=0 is

    U=B=e=0,       N_i=1 for every i.                            (4)

In particular, if z is supported on S, no absorbing carrier point has
B_i=0 for every i in S. No nonnegativity of the other caps is required.

## Proof

For a profile's first product root q, let

    c=product_i(1-q_i),  a=1-c,  H_i=product_(j!=i)(1-q_j).

Q_i is its forced-Quit value. P_i is the nonempty-opponent contribution
when i Continues. Write b for the conditional tail's full cap vector.
The literal full-response recursion is

    B_i=max(Q_i,P_i+H_i*b_i).                                   (5)

Whenever c>0, the tail consists of independently conditioned complete laws.
This formula prices every future deviation, not just the next action.

### 1. The weighted Quit test controls first-stage activity

Sample a full root coalition A under q, including the empty coalition.
Forcing just i to Quit changes it to A union {i}. Thus, using own-zero,

    sum_i z_i Q_i = sum_(A nonempty) Pr_q(A) K_A >= kappa*a.

Consequently w>=kappa*a>=0 for EVERY actual profile. Moreover
Q_i>=-M*(1-H_i)>=-M*a. Since B_i>=Q_i, its weighted negative part
is at most M*a, and therefore

    sum_i z_i |B_i| <= w+2M*a <= C*w.                           (6)

No division by z_i occurs. These conclusions also hold at every conditional
tail, and pass continuously to the appropriate semantic closures.

### 2. A small weighted cap keeps the next cap small

Assume w<=kappa/2. Then a<=w/kappa<=1/2, so H_i>=c>=1/2.
From (5), |P_i|<=M*a and 1-H_i<=a,

    b_i <= (B_i-P_i)/H_i
        <= B_i+2a*(|B_i|+M).

Write v=sum_i z_i b_i. It is nonnegative by Step 1 applied to the tail.
Summing the preceding inequality gives

    v <= w+2a*(C*w+M) <= w+5M*a <= L*w.                        (7)

The middle estimate uses C*w<=kappa/2+M<=3M/2. Applying (6)
AFRESH to this tail also gives sum_i z_i |b_i|<=C*v<=C*L*w.

### 3. Positive singleton drift makes the cap decrease down a small tail

Extend Z_i to the empty set by zero and put

    L_A=sum_i z_i Z_i(A minus {i}).

Then sum_i z_i P_i=E_q L_A, L_empty=0, |L_A|<=M, and
L_{ {j} }=sigma_j. If m_2=Pr_q(|A|>=2), then

    sum_i z_i P_i >= gamma*a-(gamma+M)*m_2
                    >= gamma*a-M*n^2*a^2.                      (8)

Indeed m_2<=sum_(i<j) q_i q_j<=(sum_i q_i)^2/2<=n^2*a^2/2,
because each q_i<=a; also gamma<=M.

Using the Continue branch in (5), then (7)--(8), yields

    w >= v+sum_i z_i P_i-sum_i z_i(1-H_i)b_i
      >= v+a*(gamma-M*n^2*a-C*L*w)
      >= v+a*(gamma-D*w).

Thus whenever w<=delta,

    0<=v<=w,       w-v>=gamma*a/2.                             (9)

### 4. Iterate actual tails, then pass to the carrier

Starting from w_0<=delta, (9) keeps every successive w_t in the same
collar. Every finite survival probability is positive because a_t<=1/2.
Summing (9) and using w_t>=0 gives

    sum_t a_t<=2w_0/gamma,
    1-nu=1-product_t(1-a_t)<=sum_t a_t<=2w_0/gamma.              (10)

Here D>=n^2>=4, so delta<=gamma/8. In particular (10) excludes
absorption when w_0<=delta. If w_0>delta, the bound
w_0>=delta*(1-nu) is immediate; otherwise (10) proves it because
delta<=gamma/2. This proves (3) and the strict actual absorbing bound.
Continuous passage to K_abs gives w>=delta, and passage to H gives (3).

Finally, on actual native profiles,

    |U_i|, |e_i| <= M*(1-nu),
    |B_i| <= M*(1-product_(j!=i) N_j) <= M*(1-nu).                (11)

For the cap bound, against all opponents choosing Never, every own
replacement pays zero. Only the complementary event can contribute.
The estimate is uniform over all replacements and therefore over their
supremum. Equation (11) passes to H. If w=0, (3) forces nu=1,
each N_i=1, and (11) proves (4).

## Finite tests and boundary configurations

If every participant premium Z_i(A), i in A and |A|>=2, is at least
eta>0, then the second test in (1) follows with

    kappa=eta*(1-max_i z_i)>0.                                 (12)

The first test forces z to have at least two positive coordinates.
For |A|>=2 all terms in K_A are at least eta; for A={j}, only the
own-singleton term vanishes. This concerns premiums ABOVE OWN SINGLETON,
not differences from the payoff obtained by refusing to join.

For the four-player singleton matrix

    Gamma = [ 0   3  -1   3 ]
            [ 2   0   1  -3 ]
            [ 2  -2   0  -1 ]
            [-1  -2   1   0 ],

z=(7,5,1,7)/20 has Gamma^T z=(1/4,1/4,1/4,1/4).
Hence all strictly positive participant completions pass the tests,
with all sixteen nonsingleton PASSIVE rewards arbitrary finite numbers.
The aggregate test is wider: set every nonsingleton participant entry to
one except Z_0({0,1})=-1. Then min_A K_A=1/20>0 for this same z.

The sparse weight z=(8,7,0,5)/20 gives

    Gamma^T z=(9,14,4,3)/20.

With positive participant premiums it excludes the ENTIRE absorbing cap
face B_0=B_1=B_3=0, without restricting B_2. For pivot 0 this removes
the boundary case with zero pivot cap and zero observer caps at 1 and 3.
It does not remove boundary cases whose positive caps meet this support.

Both raw sign hypotheses matter for closure:

- Without positive singleton drift, take two players, own rewards zero,
  each passive singleton reward -1, and joint reward (1,1). At z=(1/2,1/2)
  all K_A>=1/2. Independent uniform clocks on {0,...,T-1} absorb surely
  and have B_i=1/T and U_i=-1/2+3/(2T). Their limit has all caps zero.
- Without the positive K test, take three players, own rewards zero,
  passive singleton rewards one, and every nonsingleton reward -1 in
  every row. Uniform positive weights have sigma_j=2/3. All three
  quitting surely at date 1 give U_i=-1 and B_i=0: Quit at date 0
  yields zero, while every later response and Never yields -1.

Both controls are solved games, not positive-gap counterexamples.

## Source correspondence and remaining task

The source audit inspected
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max`
in `UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`, and
`quittingTerminalSemanticPair`, `quittingTerminalSemanticPrefix`, and
`quittingTerminalSemanticDebt` in
`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`.
The independent-law definitions were checked in
`UniformEquilibrium/Quitting/Paths/CounterfactualStoppingLaw.lean`.
No Lean command was run. Those files supply the existing semantics;
they are not cited as implementations of (3).

The adapter is the finite linear test (1); the consumer is the uniform
separation of the tested cap face from K_abs. In the current boundary
reduction, every produced tail lies in K_abs, so a tail with caps zero
on support(z) is excluded directly. Neither actual tail realization nor
minimality of that tail is needed. Under full-support weights, this rules
out the all-zero endpoint used to produce the first penalty plateau.
It does not exclude a plateau produced by a different mechanism.

The immediate remaining research question is whether signed weights or
partial-Nash equalities can replace the positive singleton-drift test
without assuming a false cap or source transport. A positive inverse
column alone does not supply that test.
