# Absorption-relative auxiliary regret at a genuine global minimum

Owner: CODEX_COORDINATOR. Ordinary mathematics, not checked in Lean.
This extends the existing one-root global repair to arbitrary finite timing
blocks. It is a necessary source restriction, not a block producer or a UE
class. No export is proposed.

## Statement

Fix four players, independent private stopping laws, terminal rewards
|r_i(D)|<=M with M>0, and original Never payoff zero. Complete behavioral
responses are allowed. Let C be the closure of actual prescribed-payoff/full-
cap pairs (U,B), and suppose

    m=min_(U,B in C) max_i(B_i-U_i)>0.

Fix ANY minimizing pair (U,B). It need not be actual. Put

    epsilon=m^2/(64M), 0<=h_i<=m+epsilon, W=B-h.

For a positive integer L consider the finite normal-form timing game in
which each player chooses a date 0,...,L-1 or Continue. The earliest finite
coalition receives r; if everyone chooses Continue the payoff is the PUBLIC
vector W. This is a single simultaneous product of independent mixed laws.
No optimality at zero-probability histories is imposed.

For ANY such block profile sigma, let y_i be its Continue probability,

    c=product_i y_i, D_i=product_(j!=i)y_j, a=1-c,
    z_i=(complete block response cap)_i-(block prescribed payoff)_i,
    z=max_i z_i.

The complete block menu contains all L dates AND Continue. Then

    z >= a m^2/(64M).                                (1)

The constant is independent of L, sigma and h in the entire displayed box.
In particular, every exact normal-form Nash block is all Continue. This
is stronger in scope than excluding nonzero one-stage Nash roots: arbitrary
calendar length and off-path commitments are included.

## Exact full-cap block ledger

First take an actual finite source mu, write d_i=B_i-U_i and e=max_i d_i>0,
and allow 0<=h_i<=e+epsilon for any epsilon>=0. Form W=B-h. For the block,
let F_i be the maximum payoff from quitting at one of its dates, H_i its
passive payoff when i Continues through the block, and n_i its prescribed
auxiliary payoff. Thus its response cap is

    b_i^block=max(F_i,H_i+D_i W_i), z_i=b_i^block-n_i.

Follow the block and, on its Continue event, a fresh shifted copy of the
source. This is an actual independent profile P. Its prescribed payoff and
FULL original cap are exactly

    U'_i=n_i+c(U_i-W_i)=n_i+c(h_i-d_i),
    B'_i=max(F_i,H_i+D_i B_i).

The latter formula includes every complete tail deviation, not only block
actions or prescribed supports. Since h_i>=0,

    d'_i<=c d_i+(D_i-c)h_i+z_i
         <=D_i e+(D_i-c)epsilon+z.                  (2)

No rootwise Nash assumption or backward equilibrium selection is used.

## Whole-law repair of the remaining owner

Write f_i=1-y_i. If a>0 choose k maximizing f_i. Since a<=sum_i f_i,
f_k>=a/4. For i!=k, D_i<=y_k<=1-a/4, whereas D_k<=1 and D_i-c<=a.
Consequently (2) gives

    d'_k<=e+a epsilon+z,
    d'_i<=(1-a/4)e+a epsilon+z  (i!=k).              (3)

Choose a complete pure best response tau_k against P_-k and replace k's
whole law privately by (1-theta)P_k+theta delta_(tau_k), with

    theta=a e/(32M)<=1/16.

The response exists on the finite complete menu, including its first
post-support date and Never. With opponents fixed the owner's debt is
exactly multiplied by 1-theta. Every other prescribed payoff AND every pure
response payoff change by at most 2M theta; taking the unrestricted maximum
therefore changes its debt by at most 4M theta. The newly exposed late
response after tau_k is included in this bound. Hence the repaired law P''
satisfies

    E(P'')<=e-a e^2/(32M)+a epsilon+z.               (4)

For outsiders, (3) plus 4M theta gives e-ae/8+a epsilon+z, which is at most
the right side of (4) because e<=2M. For k, multiply its first bound in
(3) by 1-theta. If a=0 the block ledger itself gives (4), with theta=0.
All transformations are actual private independent-law constructions.

If mu is a minimizer on controller dates 0,...,K-1,Never, the repaired law
is supported on 0,...,K+L,Never. Thus, writing eta_K for the minimum FULL
exploitability on that controller set,

    eta_(K+L+1)<=eta_K-a eta_K^2/(32M)+a epsilon+z.    (5)

The tester menu for eta_K includes date K and Never.

## Passage to a genuine possibly unattained minimum

Choose finite actual profiles mu_n with semantic pairs tending to (U,B).
Such approximants exist: first approximate the carrier point by actual
laws, then censor sufficiently remote finite mass to Never. The total-
variation coupling bound controls prescribed payoff and EVERY deviation
payoff uniformly, so it controls the full cap as well. Let e_n=E(mu_n);
then e_n>=m and e_n tends to m.

Fix L,sigma,h ONCE, and set W_n=B(mu_n)-h. Its auxiliary block defect z_n
tends to z: finitely many block response expectations and their finite
maximum are continuous in W. Since h_i<=m+epsilon<=e_n+epsilon, (4) gives
actual repaired profiles satisfying

    m<=limsup_n E(P''_n)
       <=m-a m^2/(32M)+a epsilon+z.

Take epsilon=m^2/(64M) and rearrange to obtain (1). The block laws need not
converge; no continuity of an equilibrium correspondence is invoked.

## Infinite auxiliary laws and the exact remaining obligation

The box also has W_i>=s_i=r_i({i}). Indeed, ordinary finite Nash existence
and (1) at L=1 force the all-Continue root to be Nash, which is exactly this
inequality. Consider the auxiliary infinite quitting game whose payoff on
literal AllNever is W, with the same nonempty rewards r. Censor an arbitrary
independent profile's late finite mass to Never. For the censored profile,
all pure dates beyond its support are weakly dominated by Never because
W_i>=s_i, so its finite block menu is complete. Censoring converges in total
variation and preserves all payoffs/caps uniformly under the bound
max(M,max_i|W_i|). Passing (1) to the limit proves the same inequality for
EVERY auxiliary behavioral profile, with a its absorption probability and z
its full auxiliary exploitability. Thus all-Never is its sole exact Nash
profile, and every nontrivial approximate equilibrium pays the uniform
absorption-relative regret rate in (1).

The concrete missing producer is therefore: from the SAME genuine global
source, find h in this box and one finite block with

    a>0, z/a<m^2/(64M).

A block need not be exact Nash; demanding exactness is stronger than needed.
Neither the ledger nor finite Nash existence supplies that block. Ordinary
finite Nash existence can always return all Continue. Minimizing z alone is
therefore uninformative; the candidate objective is the nontrivial ratio
z/a, with its a=0 boundary explicitly controlled.

## Narrow overlap audit

Read in full:

- CODEX_FRECHET_CYCLE__GLOBAL_MAXIMUM_DEBT_CRITICAL_BOX_REPAIR: provides the
  one-stage ledger and whole-law repair constant. The present proof uses
  the same repair; its additional scope is ALL finite timing blocks and
  consequently all behavioral laws of the modified-Never game.
- CODEX_NOETHER_SUPPORT__WHOLE_TIMING_BLOCK_BONUS_COMPETITION: already gives
  exact whole-block cap transport and all-length restrictions at a different
  source, minimum actual output among private-Never-bonus Nash laws. It
  does not assert the present unrestricted MAX source or approximate-block
  absorption-relative bound. Its two-date example correctly shows why
  block Nash cannot be replaced by backward stage Nash.
- CODEX_NOETHER_SUPPORT__NORMALIZED_SOURCE_BLOCK_LOCK_ON_H: already refutes
  activation from local bonus-source facts alone, at stationary-solved H.
- The HAHN finite-clock KKT and NOETHER two-law competitor notes retain
  complete response caps but do not contain this all-block rate.

Named Lean inputs inspected: quittingTerminalSemanticPrefix and
quittingTerminalSemanticPrefix_mem_carrier in
UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean;
quittingTerminalSemanticDebt_prefix_le_auxiliaryNashDefect in
UniformEquilibrium/Quitting/Terminal/AuxiliaryNashDebt.lean. No Lean command
was run. This is a generalization of existing accounting, not a new UE
producer, raw-table exclusion, or claimed independent breakthrough.

## A genuine source obstruction to approximation by finite-menu Nash laws

Ordinary mathematics, not checked in Lean. The argument below rules out
one attempted bridge from the unrestricted minimum to an auxiliary source.

Let Z be a fixed own-zero native Fin4 table with |Z_i(S)|<=M0, M0>0, and
suppose every ACTUAL certainly absorbing independent law has full MAX
exploitability E_Z>=delta>0. Native live play and AllNever pay zero. Choose

    0<lambda<=min(1/(8M0), delta^3/(2048M0^4),
                  sqrt(delta/(4M0^3))),
    r_i(S)=1+lambda Z_i(S) for nonempty S.

Original live play and AllNever remain zero. All four own rewards are one,
and all terminal rewards lie in [7/8,9/8]. Let m be the true unrestricted
minimum of original full MAX regret, attained in the semantic closure.

**Theorem.** m>0, but there is no sequence of finite product laws whose
finite-menu Nash errors tend to zero and whose FULL original regrets tend
to m. Equivalently there are eta0,Delta0>0 such that, at EVERY calendar
length, menu error <=eta0 implies full regret >=m+Delta0. In particular,
exact menu Nash and Nash under vanishing private planned-Never bonuses
cannot approximate the genuine original MAX minimum at this fixed table.

This is a genuine hypothetical counterexample source, not an m=0 example.
The original-to-native reduction in Part III Section 1 of
[the strict-column and all-END reduction](../exports/FIN4_STRICT_INVERSE_COLUMN_AND_ALL_END_MINIMUM_REDUCTION.md)
produces an own-zero table with positive absorbing full-SUM gap A from any
hypothetical original counterexample. Taking delta=A/4 gives the present
MAX premise. The new flattened table is fixed before its own true global
MAX minimum is extracted; no minimizing profiles are transported through
normalization. The all-END source in that reference concerns SUM, which
is not being substituted for MAX here.

### Exact flattening and a positive original gap

For an actual law let rho_i be its Never mass and C=product_i rho_i.
Native finite-deadline payoffs tend to the native Never payoff, since own
singletons are zero. Their supremum therefore already equals the full
native cap. Every finite response ensures absorption, giving exactly

    B_i^r=1+lambda B_i^Z,
    U_i^r=1-C+lambda U_i^Z,
    d_i^r=C+lambda d_i^Z,  E_r=C+lambda E_Z.           (A)

Original Never is dominated by this finite-response supremum: its value
is 1-product_(j!=i)rho_j+lambda N_i^Z<=1+lambda B_i^Z.
Thus (A) includes every behavioral response, even if the cap is unattained.

Move the smallest Never atom rho_k<=C^(1/4) to any finite date. The resulting
actual independent law absorbs surely. Coupling bounds every changed payoff
and every outsider response by 2M0 rho_k, while the owner's cap is unchanged.
Consequently

    E_Z>=delta-4M0 C^(1/4).

Split at C=lambda delta/2. If C is larger, (A) suffices; if smaller, the
chosen lambda makes 4M0 C^(1/4)<=delta/2. Hence

    lambda delta/2<=m<=2lambda M0<=1/4.              (B)

The upper bound uses any certainly absorbing profile and E_Z<=2M0. The
lower bound holds for every actual law and therefore on the semantic closure.

### What a hypothetical menu-Nash approximation would force

Suppose finite laws mu_n have menu error eta_n->0 and E_r(mu_n)->m. Pass
to a full semantic subsequence (U_n,B_n)->(U,B). Its limit is a genuine
MAX minimum. The existing all-player-tie theorem and singleton margin give

    B_i-U_i=m for every i,  U_i>=1.                  (C)

The tracked declaration is `minimumTerminalSemantic_maximumDebt_allPlayersTie`
in `UniformEquilibrium/Diagnostics/Quitting/PositiveMaximumDebtMinimum.lean`.
Its unit reward bound is handled by dividing the present reward table by
1+lambda M0 and scaling back. Its declaration and proof were inspected;
no Lean command was run. The singleton margin is
`minimumTerminalSemantic_exploitabilitySingletonMargin` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDynamicCostate.lean`.

Write F_i^n for the largest response on finite controller dates, N_i^n
for the pure-Never payoff, v_i^n=max(F_i^n,N_i^n), rho_i^n for Never mass,
D_i^n=product_(j!=i)rho_j^n and C_n=product_i rho_i^n. Own rewards one give

    B_i^n=max(v_i^n,N_i^n+D_i^n),
    0<=v_i^n-U_i^n<=eta_n.                          (D)

The second cap branch becomes active since full debt tends to m>0. Also
D_i^n>=d_i^n-eta_n, so every D_i^n and every rho_j^n stays positive uniformly.
The source's own regret average gives

    rho_i^n(v_i^n-N_i^n)<=v_i^n-U_i^n<=eta_n.

Thus U_i^n-N_i^n->0 and D_i^n->m. Because product_i D_i^n=C_n^3,

    q=m^(1/3) in(0,1), rho_i^n->q, C_n->q^4=mq.      (E)

These are actual Never masses, not mass assigned to a weak escaping-clock
limit. Vanishing menu error is enough; no support equality was assumed.

### A single actual replay gives the contradiction

After mu_n, let each player's own Never branch use a fresh independent copy
of that player's law, shifted beyond the old controller. This is an actual
finite product law nu_n. Its payoff and COMPLETE original cap are exactly

    U_i(nu_n)=(1+C_n)U_i^n,
    B_i(nu_n)=max(F_i^n,N_i^n+D_i^n B_i^n).           (F)

The tail cap B_i^n includes its post-support response and Never, so (F)
also retains the new final post-support tester. No common selection coin
or conditional implementation after an infinite calendar is introduced.
In the limit the second branch strictly dominates the first, by (B)--(C).
Its debt converges to

    m[m+(1-q)U_i].

Every nu_n has full regret at least m. Taking the maximum and limit implies

    max_i U_i>=(1-m)/(1-q)=1+q+q^2.

But max_i U_i<=1+lambda M0, so q<=lambda M0 and

    m=q^3<=lambda^3 M0^3<=lambda delta/4,

contradicting (B). The replay laws need not converge. If the claimed uniform
eta0,Delta0 separation failed, selecting both errors <=1/n would give the
forbidden sequence. Vanishing private Never bonuses give vanishing original
menu error and are therefore covered as well.

The full graft accounting in (F) already appears in
`CODEX_TARSKI_PREMIUM__GLOBAL_MINIMUM_NEVER_BRANCH_RETRY_AND_TAIL_BUDGET`.
`CODEX_NOETHER_SUPPORT__FINITE_MENU_NASH_AND_GLOBAL_MAX_MINIMUM_SEPARATION`
already proves a different genuine-source separation for own levels
(1,0,0,0), using zero nonpivot debts. Here every own level is one; flattening
and the replay inequality supply the missing argument. Neither existing
finite Nash existence nor the finite-clock KKT source asserts the false
near-minimum/menu-Nash bridge. The unrestricted minimizing laws still need
a producer that handles their nonvanishing menu error. No absorbing block
with z/a below the preceding rate has been produced, and no Fin4 class is
claimed solved by this source-selection obstruction.
