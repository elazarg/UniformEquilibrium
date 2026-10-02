# Review of one-jump, two-sorted essential APS

Reviewer: CODEX_SPINOZA

Reviewed note:
notes/CODEX_BLINDSPOT__ONE_JUMP_TWO_SORTED_ESSENTIAL_APS.md

Exact reviewed SHA-256:
2710c02fc5c134e9e6036e4537399d8cf03a290b8c68cf088c28e07a2c82d3b7

## Verdict

**PASS.** The two supplied-object compilers are sound against unrestricted
behavioral deviations, including the sure-absorption and Never boundaries.
The unique-live mesh error is a maximum one-row error independent of the
number of mesh rows. The two-player nonconvex jump-image calculation is
exact. The two-sorted construction is clearly marked as an operator proposal,
while only the rank-one one-jump grammar is claimed executable.

## Exact-jump closure

For a uniform-equilibrium payoff \(y\), the cited terminal selection theorem
gives terminal profiles with prescribed payoffs \(u_n\to y\) and complete
behavioral caps \(b_n\) satisfying \(0\le b_n-u_n\le\eta_n\). Thus their
semantic pairs converge to \((y,y)\).

If \(x\) is exact root Nash against \(y\), the checked diagonal prefix
identity gives

\[
 T_x(y,y)=(F_r(x,y),F_r(x,y)).
\]

Continuity of the full semantic prefix therefore sends the selected terminal
profiles to terminal profiles whose payoff approaches the fixed target
\(v=F_r(x,y)\) and whose unrestricted terminal debt approaches zero.
Fixed-target acceptance proves \(v\) is a uniform-equilibrium payoff. This
argument does not divide by survival, so it covers sure absorption. At
all-Continue it reduces to the identity when the singleton endpoint
inequalities make that root exact.

## Proper singleton mesh

The owner identity
\[
 z_i=p s_i+(1-p)y_i=s_i,\qquad 0<p<1
\]
forces \(y_i=s_i\). During the solo-owner mesh, every complete owner response
is bounded by the maximum of quitting for \(s_i\) and reaching the tail cap;
the selected tail semantic error gives the stated \(O(\eta)\) owner debt.

For outsider \(k\), at each row the ideal continuation lies on the segment
from \(y_k\) to \(z_k\), so viability puts it above \(s_k\). Quitting at that
row changes the conditional payoff by at most

\[
 h\,[r_k(\{i,k\})-r_k(\{k\})]+\eta\le2Mh+\eta.
\]

Before absorption the only public history is the all-Continue string.
Therefore an arbitrary behavioral response induces a distribution over its
first quitting row and the event of entering the tail. Its gain is a convex
combination of the pure-row gains and the reached tail gain, not a sum over
rows. Hence the uniform bound is \(2Mh+\eta\), independent of \(N\).
Taking \(h=1-(1-p)^{1/N}\to0\) proves the fixed-target compiler.

The condition \(p<1\) is correctly retained. At \(p=1\), a negative singleton
owner can choose Never for payoff zero, so the purely algebraic terminal
clause need not be executable.

## Reverse order and execution scope

For a finite flow prefix before a jump, jump closure first compiles its source
payoff and the proper segment lemma then compiles the outer flow segment.
This is the correct reverse-order hypothesis. A completed terminal-free
unique-live component has survival zero, so a jump placed after all of it is
unreached. The note does not silently interpret that order as an ordinary
natural-number execution.

The two-sorted operator retains the root/tail witness at jump states and uses
a selected segment, rather than convexifying the jump image. Its greatest
fixed-point executability is explicitly a proposal, not a consequence of the
proved one-jump closure.

## Nonconvexity check

For the two-player table with singleton rewards \((-1,-1)\), joint reward
\((1,1)\), and continuation zero, player 1's Quit-minus-Continue difference
is \(-1+3p_2\), and symmetrically for player 2. Mutual best response gives
exactly

\[
 (p_1,p_2)\in\{(0,0),(1/3,1/3),(1,1)\}.
\]

Their payoffs are respectively \((0,0)\), \((-1/3,-1/3)\), and \((1,1)\).
Thus the jump image is nonconvex even though all three points are viable
uniform-equilibrium payoffs. This refutes only the old convex-progress
adapter; it does not claim the missing convex combinations are not uniform
payoffs.

## Boundary

The note proves closure of a supplied uniform payoff under one exact jump and
under finitely many proper viable singleton segments placed before it. It
does not produce the base component, a coherent unbounded jump selection, a
public correlating device, or a transfinite execution.

## Standalone export-candidate gate

Candidate:
/tmp/CODEX_BLINDSPOT__ONE_JUMP_TWO_SORTED_ESSENTIAL_APS_EXPORT_CANDIDATE.md

Exact candidate SHA-256:
c2cf67c83e9c58e713430010af4598b140aff41c045533517a91e4872654c98b

**REVISE / FAIL exact export bytes.** The two main compiler proofs,
\(2Mh+\eta\) mesh constant, sure-absorption scope, reverse-order
qualification, and nonconvex two-player regression faithfully match the
reviewed source mathematics. There are nevertheless two export-gate defects.

1. The candidate adds a new “Quantitative root bound,” equations (6)--(8),
   which is absent from the exact reviewed source SHA
   2710c02fc5c134e9e6036e4537399d8cf03a290b8c68cf088c28e07a2c82d3b7.
   The estimate appears mathematically correct: perturbing the Continue
   endpoint by \(b_k-y_k\) costs at most
   \(\beta_k(d_k+e_k)\), while the prescribed payoff moves by at most
   \(\alpha e_k\), and \(\alpha\le\beta_k\). But it is additional theorem
   content and is not byte-delta-covered by the completed two reviews.
   Remove it from this packet or obtain substantive independent review of the
   strengthened candidate.
2. The candidate does not meet the mandatory packet format in
   exports/README.md. It records no linked independent reviews and omits the
   required top-level sections Conjecture-facing change, Definitions and
   assumptions, Source correspondence, Boundary tests, Adapter and consumer,
   Lean handoff, and Scope and nonclaims. Some corresponding prose is present
   under differently scoped headings, but the review record, adapter/consumer
   boundary, and Lean handoff are not supplied.

The control-byte scan and documentation checker are clean. No objection
remains to the original frozen note; the failure is confined to the
standalone export artifact and its unreviewed strengthening.
## Exact-final candidate review

Reviewed `/tmp/EXACT_ONE_JUMP_AND_PROPER_SINGLETON_FLOW_CLOSURE.md` at exact
SHA-256
`0f072df795757e082374efb30e21b00e4225b69a3c44ce1207baae327b911b34`.

**PASS.** The previously unreviewed quantitative product-root estimate has
been removed.  The remaining mathematical content is the reviewed exact
one-jump closure, proper viable singleton-flow closure with the
`2Mh + eta` outsider bound independent of the mesh length, the exact
nonconvex two-player root image, and the stated endpoint/order boundaries.
I found no strengthened conclusion or mathematical drift from reviewed
source SHA
`2710c02fc5c134e9e6036e4537399d8cf03a290b8c68cf088c28e07a2c82d3b7`.

Both independent review links and all local source links resolve from the
intended future `exports/` location.  All mandatory export headings are
present, the probability/behavioral strategy scope and supplied-object
nonclaim are explicit, the control-byte scan is clean, and
`../scripts/check_docs.py` passes.  The exact candidate bytes therefore pass
the final gate.
