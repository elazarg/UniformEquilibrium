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
