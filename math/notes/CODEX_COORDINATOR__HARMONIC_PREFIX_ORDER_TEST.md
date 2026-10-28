# Complete second-order prefix test at a global harmonic boundary

Owner: CODEX_COORDINATOR. Ordinary mathematics, not checked in Lean.
This gives a finite necessary restriction on the harmonic equality branch
of a genuine full-regret minimum. It supplies no new raw UE class and does
not address the strict harmonic interior. Fin4 remains open.

## Source and exact scope

There are four players with independent private stopping laws on the finite
dates and Never. Terminal rewards r_i(D) are fixed finite real numbers;
Never pays zero. Every unilateral behavioral deviation is allowed. Let C
be the closure of the actual semantic pairs (U,B), where B is the complete
best-response cap. Suppose (U,B) globally minimizes max_i(B_i-U_i), its
value is m>0, all four debts equal m, and

    s_i=r_i({i}), k_i=B_i-s_i>0,
    a_i=1/k_i, A=sum_i a_i,
    m A=1.                                           (1)

The equal-debt and positive-margin hypotheses are the existing global-source
restrictions. Equality in the known harmonic inequality is the additional
branch studied here. Define algebraically

    Gamma_ij=r_i({j})-s_i,
    Z_i(ij)=r_i({i,j})-s_i.

No reward-shift invariance at Never is assumed.

A weak order omega of the four players is an ordered partition into nonempty
blocks. There are 75 such orders. Say i<omega j if i's block precedes j's
block chronologically, and i=omega j if they share a block. For each pair
{i,j}, define

    L_ij(omega)=a_i Gamma_ij-1                  if i<omega j,
               a_j Gamma_ji-1                  if j<omega i,
               a_i[Gamma_ij-Z_i(ij)]
                 +a_j[Gamma_ji-Z_j(ij)]-1      if i=omega j.

Put

    W_omega=sum_(i<j) a_i a_j L_ij(omega).           (2)

**Theorem. Every W_omega is nonnegative.** If any is negative, an explicitly
selected finite prefix with at most four dates, applied to arbitrarily close
actual approximants of (U,B), has full exploitability strictly below m.
This contradicts the actual infimum; no realization of (U,B) is required.

There is also a precise completeness statement. Fix any finite calendar of
prefix dates and one-sided C^2 nonnegative hazards q_(i,t)(eps), with q_(i,t)(0)=0.
If its leading nonzero total hazard is first order in eps and no player's
debt increases to first order, the first-order totals are a common positive
multiple of a. After rescaling eps, the weighted second-order debt variation
is a convex combination of the 75 values W_omega. Every W_omega is attained
by the one-pulse-per-player prefix corresponding to omega. Thus
min_omega W_omega<0 is necessary and sufficient for a strictly negative
weighted second-order variation among this entire finite-calendar family.
When the minimum is zero, third and higher orders remain undecided.

## Proof

For a sufficiently small fixed finite prefix, at every date and for every
player the full cap chooses Continue followed by the downstream cap. At
zero prefix hazards its margin over the immediate Quit branch is k_i>0;
continuity and finitely many roots preserve all these strict margins. The
full response cap, including Never, is therefore being evaluated exactly,
not discarded in the expansion.

For a solo root of owner j and hazard q, prefixing updates, exactly,

    d'_j=(1-q)d_j+q k_j,        k'_j=k_j,
    d'_i=(1-q)d_i,             k'_i=(1-q)k_i+q Gamma_ij (i!=j). (3)

For a simultaneous root use odds z_i=q_i/(1-q_i) and P=product_i(1+z_i).
The exact Continue-branch debt is

    d'_i=P^(-1){d_i+z_i k_i
            +sum_(nonempty S subset players\{i})
                 z_i product_(j in S) z_j [r_i(S)-r_i(S union {i})]} . (4)

Formula (4) is exact even for unequal incoming debts: the terms
d_i(1+z_i)+z_i(U_i-s_i) combine to d_i+z_i k_i. It follows directly from

    d'_i=c_-i d_i+q_i[C_i(U_i)-Q_i].

Prefix the blocks of omega, giving owner i the single hazard eps*a_i at its
block. Formula (3), or expansion of (4), gives

    d_i(eps)=m+eps[k_i a_i-m A]+eps^2 c_i+O(eps^3)
            =m+eps^2 c_i+O(eps^3).                  (5)

The weighted coefficient sum_i a_i c_i is W_omega. Here is the pairwise
calculation, which also fixes the chronology convention. If i's solo root
is earlier than j's, its map is applied after j's map when propagating
backward. Their cross term in sum_k a_k d_k is

    a_i a_j [m A+a_i(Gamma_ij-k_i)-a_j k_j]
       =a_i a_j(a_i Gamma_ij-1).                   (6)

If they quit at the same root, expand (4). The cross term is

    a_i a_j{a_i[Gamma_ij-Z_i(ij)]
             +a_j[Gamma_ji-Z_j(ij)]-m A},          (7)

which is exactly the simultaneous part of (2). Three-owner and four-owner
coalitions enter only at order at least three.

The derivative of the debt vector with respect to an additional
second-order total hazard b is

    (Lb)_i=k_i b_i-m sum_j b_j.                    (8)

Its weighted sum is zero by (1). Conversely its range is the hyperplane
orthogonal to a. Let t=W_omega/A and choose

    b_i=(t-c_i)/k_i.

Then sum_i b_i=t A-W_omega=0 and c_i+(Lb)_i=t for every i. Replacing i's
hazard by eps*a_i+eps^2*b_i is legal for sufficiently small positive eps,
since every a_i>0. If W_omega<0, (5) becomes

    d_i(eps)=m+eps^2 t+O(eps^3)<m

for every i. All complete-cap branch margins still hold. Fixed-prefix
continuity preserves C. Equivalently, choose sufficiently close actual
profiles after fixing eps to obtain actual exploitability below m. This
proves the necessary test.

For completeness, let the general calendar's leading hazards be
q_(i,t)=eps*v_(i,t)+O(eps^2), with v_(i,t)>=0. Set v_i=sum_t v_(i,t) and
V=sum_i v_i. Its first-order debt coefficient is k_i v_i-m V. Their
weighted sum is zero. Thus all coefficients are nonpositive only when
all vanish; nontriviality gives v_i=m V/k_i>0. Rescale to v_i=a_i.

Draw one date T_i independently for each player from probabilities
v_(i,t)/a_i. Every draw gives a weak order omega of the four players.
The second-order expansion is pairwise. The pair (i,j) has its chronological
coefficient (6) if T_i<T_j, the reversed coefficient if T_j<T_i, and its
simultaneous coefficient (7) if T_i=T_j. Its expected coefficient is the
calendar's actual coefficient. Same-owner repetitions only alter that
owner's second-order effective total hazard; by (8) this contributes zero
to the weighted sum. Therefore the total weighted coefficient is exactly
E[W_omega]. Arbitrary second-order hazard corrections also contribute zero
by (8). Each deterministic weak order attains W_omega, completing the
claimed finite reduction. No compactness over calendars is needed.

## Exact weak-order decomposition and a uniform local alternative

The calendar reduction is stronger than the Taylor statement. Let an
arbitrary finite prefix have player i's probability p_i of quitting within
the prefix, and put beta=sum_i p_i. Sample independently a hypothetical
finite date T_i from each player's conditional finite-date law; when p_i=0,
choose T_i arbitrarily since its finite-versus-Never flag is always Never.
Independently sample that player's Bernoulli(p_i) finite-versus-Never flag. These two draws
realize the original independent prefix law. The four hypothetical dates
induce a weak order omega, independently of all finite-versus-Never flags.
Conditional on omega, the literal payoff is the payoff of its ordered-block
prefix with the one hazard p_i for each player.

Consequently the prescribed payoff is exactly an average of the 75
ordered-block payoffs. When beta is small enough, the full cap is also
exactly the corresponding average of Continue-through-prefix caps. The
smallness requirement is uniform over the calendar length: if |r|,|U|,|B|
are bounded by M and beta<1/2, conditioning on survival at any prefix date
makes the remaining finite mass of each opponent at most 2p_j. Therefore
Continue through the remaining prefix differs from B_i by at most 4M beta,
and immediate Quit differs from s_i by at most 4M beta. Taking
beta<min_i k_i/(16M) leaves all cap gaps strictly positive, at every date.
No information about the hypothetical dates is supplied to any player;
the decomposition is an identity for expectations, not a correlated
strategy proposed to the game.

Each ordered-block payoff/cap polynomial has degree at most four in p.
There are just 75 such polynomials. Thus its Taylor remainder constants
through every fixed degree are uniform over ALL finite calendars, even
when the calendar length and relative hazards vary with beta.

In particular, write Wmin=min_omega W_omega. Under (1):

- If Wmin<0, the constructed at-most-four-date prefix strictly lowers every
  debt, so the genuine global source is impossible.
- If Wmin>0, there is beta0>0 such that EVERY nontrivial finite prefix with
  sum_i p_i<beta0 increases at least one full debt above m.
- If Wmin=0, this test is undecided; higher-order terms may matter.

For the second assertion, suppose otherwise that all resulting debts are
at most m. Uniform expansion gives

    k_i p_i-m beta <= O(beta^2).

The four leading terms sum to zero after weights a_i are applied. The
upper bounds and sum_i p_i=beta therefore force

    p_i=beta a_i/A+O(beta^2)

uniformly in the calendar. The weighted linear debt term is identically
zero for every p, since m A=1. The quadratic term at this near-balanced p
is

    sum_i a_i[d'_i-m]
       = beta^2/A^2 E[W_omega]+O(beta^3).

Uniformity follows from the exact finite-polynomial decomposition. For
Wmin>0 this is positive for all sufficiently small beta, contradicting
that each debt is at most m.

For comparison, in the strict harmonic interior m A<1 the same decomposition
immediately yields a uniform local trap with no second-order computation:

    sum_i a_i[d'_i-m]=(1-m A) beta+O(beta^2)>0.

Thus arbitrarily many tiny prefix dates cannot bypass the first-order
obstruction there. This is a limitation of local prefix changes, not of
macroscopic prefixes or of changes to the source's existing laws.

## Boundary and implementation checks

For asynchronous prefixes the test uses only singleton rewards and the 24
strict orders. Simultaneous blocks add the pair rewards and expand the
complete finite list to 75. The result cannot see triple/quadruple rewards
at second order. It does not exclude any source with m sum_i 1/k_i<1.
Nor does nonnegativity of all 75 values prove local or global minimality.

Source inspected, without a Lean command:

- quittingTerminalSemanticPrefix,
  continuous_quittingTerminalSemanticPrefix, and
  quittingTerminalSemanticPrefix_mem_carrier in
  UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean;
- minimumTerminalSemantic_exploitabilitySingletonMargin in
  UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDynamicCostate.lean.

The first-order source is the
[simultaneous small-root test](CODEX_HILBERT__SIMULTANEOUS_SMALL_ROOT_TEST.md).
The new conclusion is the complete 75-order second-order test and its
calendar-independent local alternatives, not a source for harmonic equality.

The useful next question is whether the genuine source forces harmonic
contact after a suitable minimizing selection, or whether the 75 inequalities
combine with other source restrictions to eliminate the equality branch.
Neither implication has been established here. The strict harmonic interior
remains the principal obstacle to this prefix-based approach.
