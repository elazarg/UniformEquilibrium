# Review of positive-minimum carrier-cycle seam toll

Reviewer: `CODEX_DESCENDANT`

Candidate reviewed: `/tmp/POSITIVE_MINIMUM_CARRIER_CYCLE_SEAM_TOLL.md`,
SHA-256
`fd086c5569e76f4302abf943f8d33352973f70f32160ab40a6e08def8217b99e`.

## Verdict

**PASS.**  The finite cyclic identity, its exact and approximate lower
bounds, and the open-chain debt-battery form are correct.  I found no
strategy-class, carrier-typing, sign, or constant error.  The packet is a
genuine no-go for cancellation of source-attached carrier/cap seams; it does
not overclaim a forward-packet producer or terminal consumer.

## Claim checked

For a cyclic list of actual terminal-semantic carrier points \(z^k\), prefix
each \(z^k\) by a product root \(q_k\) tested against the displayed
unrestricted cap \(B(z^k)\), and rebase the resulting prefix point \(w^k\) to
the next carrier point \(z^{k+1}\).  The candidate claims

\[
 \sum_k\bigl(D(z^{k+1})-D(w^k)\bigr)
 =\sum_k\bigl(a_kD(z^k)-N_k\bigr),
\]

where \(a_k\) is root absorption and \(N_k\) is total root Nash defect.  A
positive carrier debt floor then forces a semantic seam at least linear in
exact-root absorption; ordinary approximate roots incur the correction
\(-|I|\sum_k\eta_k\).

## Mathematical audit

### Prefix identity and cyclic sign

The checked identity

\[
 D(w^k)=c_kD(z^k)+N_k
\]

has exactly the candidate's orientation: \(c_k=1-a_k\), so

\[
 D(z^k)-D(w^k)=a_kD(z^k)-N_k.
\]

Cyclic reindexing replaces \(\sum_kD(z^{k+1})\) by
\(\sum_kD(z^k)\), giving equation (8) with the displayed positive sign on
\(a_kD(z^k)\) and negative sign on \(N_k\).  No survival weight is missing:
the root is applied once at each displayed source and the rebase seam is
measured immediately after that prefix.

### Carrier and cap typing

The arbitrary-root semantic prefix of a carrier point is again in the
terminal-semantic carrier.  More importantly, the prefix identity uses the
second coordinate of the same displayed source \(z^k\).  Thus \(N_k\) is the
defect against the actual unrestricted behavioral cap, not against a newly
chosen Bellman annotation.  This is precisely the hypothesis needed for the
positive minimum floor to apply.  The packet explicitly excludes fresh
noncarrier Bellman annotations, so it does not extend the theorem beyond its
typing.

### Exact and approximate constants

For exact roots \(N_k=0\), and \(D(z^k)\ge D_*>0\) gives

\[
 \sum_ks_k\ge D_*\sum_ka_k.
\]

Since

\[
 s_k=\sum_i(e^k_{B,i}-e^k_{U,i}),
\]

the triangle inequality gives \(|s_k|\le E_k\).  In Fin4 there are exactly
eight payoff/cap coordinates, hence

\[
 E_k\le8\lVert z^{k+1}-w^k\rVert_\infty,
\]

and the factor \(1/8\) is correct.

For an ordinary \(\eta_k\)-Nash root, the checked total-defect bound is
\(N_k\le |I|\eta_k\).  A support-\(\eta_k\) condition with
\(\eta_k\ge0\) implies the ordinary endpoint condition with the same
tolerance, so no extra factor is lost.  Even when the right side of (14) is
negative the inequality remains true; in the intended little-oh regime it
becomes positive after division by total absorption.

### Open chain and repeated copies

Without cyclicity the telescoping term is exactly
\(D(z^L)-D(z^0)\), proving (15).  For exact roots,
\(D(z^L)\ge D_*\) and \(D(z^0)=D_*+E_0\) give the sole correction
\(-E_0\) in (16).  Thus initial excess can finance a finite amount of charge
once, but a repeated phase must repeat its actual rebase seam.  Counting a
cycle's seam once while multiplying its charge would violate the literal
finite-chain identity, so the repeated-copy scope is stated correctly.

## Falsification tests

1. **Zero floor.**  In the zero table, \(D_*=0\), every root is exact, and a
   positive-absorption one-phase loop can have zero seam.  This correctly
   shows that positivity is essential.
2. **Sign test.**  In the constant-one table at all Never,
   \(D=|I|\).  A sure singleton prefix is exact, has absorption one, and
   produces zero debt.  Rebasing to the original source therefore has seam
   \(+|I|=aD\), confirming the sign.
3. **Approximate correction.**  In the two-player date-one joining example,
   the proposed prefix has absorption \(h\), defect \(h\), and unchanged
   total debt.  Hence \(aD-N=0\), so omitting the defect correction would be
   false.
4. **Noncarrier annotation.**  A periodic normalized-motion construction may
   use Bellman values that are not unrestricted caps of carrier points.  It
   then falls outside the premise rather than contradicting the theorem.

## Novelty and exact consequence

The underlying arbitrary-root debt recursion is checked, and the general
signed-seam telescope is checked.  The useful new statement is the
unweighted cyclic specialization and its linear positive-minimum toll.  It
decisively removes one proposed route: carrier-source payoff/cap seams cannot
cancel to \(o(\sum a_k)\) while exact or \(o(\sum a_k)\)-defect root charge
survives.

This does **not** consume bounded capacity, produce a Nash--Bellman packet,
or rule out a construction using fresh Bellman annotations.  Those nonclaims
are explicit.  I found no export-blocking issue.

## Optional permutation strengthening

The same proof remains valid if the next source on phase \(k\) is
\(z^{\pi(k)}\) for any permutation \(\pi\) of the finite phase set.  The only
cyclic step used is

\[
 \sum_k D(z^{\pi(k)})=\sum_kD(z^k).
\]

Thus reordering a fixed multiset of carrier phases cannot evade the toll.
This is worth adding as a corollary because it closes a natural bookkeeping
loophole, and it introduces no mathematical adapter ambiguity provided the
statement keeps the root \(q_k\) attached to its original source \(z^k\) and
changes only the rebase target.  It does not cover adding/removing phases or
using noncarrier Bellman annotations.  The frozen candidate is already
correct without this optional strengthening.

## Optional stationary-coupling strengthening

The proposed convex extension is also sound.  Let \(\beta\) be a probability
vector on the displayed sources and let \(\lambda_{k\ell}\ge0\) have both row
and column marginals equal to \(\beta\).  If the seam attached to
\((k,\ell)\) rebases the literal prefix point \(w^k\) to \(z^\ell\), then

\[
 \begin{aligned}
 \sum_{k,\ell}\lambda_{k\ell}
   \bigl(D(z^\ell)-D(w^k)\bigr)
 &=\sum_\ell\beta_\ell D(z^\ell)-\sum_k\beta_kD(w^k)\\
 &=\sum_k\beta_k\bigl(a_kD(z^k)-N_k\bigr).
 \end{aligned}
\]

Thus neither deterministic phase permutations nor randomized stationary
rematching of a fixed carrier-source distribution can cancel the positive
minimum toll.  This is strictly more informative than the permutation
corollary and is worth adding.  The adapter must retain two details: every
root \(q_k\) remains typed against its own source cap \(B(z^k)\), and every
seam is measured from the corresponding literal prefix \(w^k\) to the
chosen carrier target \(z^\ell\).  Under those hypotheses there is no
ambiguity.  The result does not cover nonstationary marginals, newly created
phases, or noncarrier Bellman targets.

## Delta review of the stationary-coupling candidate

Frozen candidate reviewed:
`/tmp/POSITIVE_MINIMUM_CARRIER_CYCLE_SEAM_TOLL.md`, SHA-256
`3a9348ba842eb6611bf3e7fd402711c36491863d8686c33e3a40fa43cc78dea6`.

**PASS.**  Equations (14a)--(14f) implement the extension exactly.  The two
marginal identities give (14c); nonnegative coupling weights allow the same
weighted triangle inequality; the exact minimum floor and the ordinary
defect estimate yield (14d) and (14f); and the eight-coordinate norm bound
gives (14e) with the unchanged Fin4 factor (1/8).  The text keeps (q_k)
typed against (B(z^k)), keeps (w^k) literal, and identifies the chosen
carrier target (z^\ell) separately.  It also explicitly excludes unequal
marginals and noncarrier annotations.  The permutation statement is the
correct equal-weight deterministic special case.  Formula, delimiter,
control-byte, and frozen-hash checks pass.  No new blocker was introduced.
