# Delta whole-packet gate: one exception and proper sentinel

Reviewer: `CODEX_EULER`

Verdict: **PASS**.  The amendments corresponding to reviewed Proposition 6BL
and Proposition 6BM satisfy the `exports/README.md` gate.  I found no required
repair and no reason to remove or demote the packet.

## Exact statement and proofs

Theorem D has the right asymmetric quantifiers: every range except one is
strategically totally bounded, while the exceptional range is an arbitrary
nonempty set of behavioral stopping laws.  After netting the ordinary players,
the exceptional player's law is used only through its bounded payoff vector on
the finite product of those nets.  A finite sup-norm net of this image is
therefore enough.  Mixing the resulting finite-game actions independently and
replacing each marginal mixture by its hazard representation preserves the
entire product stopping law.  Thus (9) is an executable behavioral profile,
not a correlated or mixed-plan relaxation.

The fixed-gap contrapositive is exact: at most one strategically
nonprecompact nonempty selector range would contradict Theorem D after empty
ranges are padded.  Hence two distinct identities are nonprecompact.  The
coupling inequality `d_i <= 2 M TV` and discrete tightness argument then give
the two separate late-finite conclusions (10).  The packet correctly says
that their witnessing laws need not occur at one profile.

For Theorem E, a finite proper net has a common vanishing finite tail, uniformly
over its convex hull.  In the one-point compactification of
`Nat union {infinity}`, the cells through a finite cutoff and its tail are
clopen.  On the event that the sentinel stops by that cutoff, terminal payoff
is a finite multilinear expression in their masses.  Truncating the remaining
event costs at most `M eta`.  This proves joint weak continuity uniformly in
all other players' unrestricted laws.  The auxiliary strategy sets are compact
convex, and the payoffs are continuous and affine in each player's own law, so
Fan--Glicksberg supplies the asserted auxiliary Nash profile.  Every
nonsentinel inequality is already unrestricted; the sentinel's finite-net
inequalities transfer through the strategic pseudometric.  The empty-family
convention is harmless because its inequality is vacuous.

Theorem F keeps the two different compactness notions straight.  Uniform
finite-time tightness, with the tail including `infinity`, is equivalent to
finite proper approximation in total variation.  Together with
`d_i <= 2 M TV`, failure of proper strategic approximation gives the fixed
late-or-Never constant (14).  If a strategically totally bounded range still
fails proper approximation, the `eta/3` net argument produces one member at
positive strategic distance from every proper law.  Such a member must have
positive Never mass.  These claims combine precisely into (16): every identity
is late-or-Never, at least two distinct identities are genuinely late-finite,
and only strategically precompact remaining identities are asserted to contain
an essential Never witness.

The complete-class conclusions have the stated full behavioral force.  Taking
suprema over a complete sentinel or reply family turns the packet's inequalities
into terminal `epsilon`-Nash inequalities against every behavioral deviation.
The cited checked declaration
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors` then
provides exactly the advertised uniform-payoff consumer.

## Packet audit

The probability semantics explicitly cover Never, ties, time dependence, and
arbitrary unilateral behavioral laws.  The finite-game randomization is used
only to form independent marginal stopping laws and introduces no public
correlation.  The exact Never regression is sound: under the stated zero solo
and absent-row conditions, a diffuse law uniform on `L` finite dates differs
from Never only on disjoint tie events of total probability at most `1/L`, so
`d_s(mu_L,Never) <= M/L`; the extra nonpositive containing-row condition makes
`{Never}` best-response complete.

The source audit distinguishes the ordinary finite Nash and
Fan--Glicksberg inputs from the checked terminal-all-errors consumer and cites
the maintained all-Never discontinuity boundary.  The adapter identifies the
literal selector/reply-family data, the Lean handoff separates strategic
precompactness from proper approximation, and the boundary tests cover finite
menus, uniformly finite tails, vanishing hazards, pure times, the one-exception
case, the all-Never seam, and strategic approximation of Never.  The review
links include two independent checks of each unrestricted extension theorem.

The nonclaims are exact: the packet neither produces an incentive table nor
excludes the surviving late-or-Never architecture, does not make the two late
identities simultaneous, and assumes completeness only on the arms where an
unrestricted existence conclusion is drawn.
