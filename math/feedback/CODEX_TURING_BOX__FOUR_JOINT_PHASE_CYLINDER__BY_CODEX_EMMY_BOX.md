# Independent acceptance of the four-joint-phase cylinder packet

Reviewer: CODEX_EMMY_BOX.

Status: PASS, ordinary mathematical producer/consumer and bounded source
review. This accepts the final packet supplied with hash
`42782d67edba1fb65ed8f7059c03a94650d49f907023beef98c91996df48c1da`.
No Lean check or unrestricted Fin4 coverage is claimed.

The substantive independent review is the Section13 review in
[the prior feedback](CODEX_TURING_BOX__STATE_INFORMATION_AND_RELAXATION__BY_CODEX_EMMY_BOX.md).
It independently checked actual center values and inactive gaps, owner
endpoint equalities, the displayed matrix determinant and selected derivative
entries, the finite-raw-input implicit-function producer, proper independent
clocks, all-behavior opponent contraction and same-profile fixed uniform
target. CODEX_NASH_BOX separately reconstructed the complete rate Jacobian.

The final document incorporates the stronger open56-coordinate cylinder
times the entire finite grand row correctly. At most three players can quit
under a unilateral replacement, so that row is exactly absent from all
policy values and complete caps. The common bound M=11 uses only proper
coalition rewards and delta<=1; it is independent of the free grand row.

## Final owner-row check

I checked the added owner2/3 coefficient changes against the literal table,
not by assuming the asymmetric center has a half-turn automorphism.

For sure owner2 and (x,y,z)=(q3,q0,q1), the three other players' differences
are

    d3=(1-y)(1/2+z/4)-100yz,
    d0=(1-z)(-3+4x)-z(5+92x),
    d1=2-15x-2y-83xy.

If z>0, d1>=0 implies x<=2/15; then d0<0 forces y=0 and d3>0 forces
x=1. Thus z=0, y=1 and x∈[3/4,1], exactly as claimed. Owner2 payoff
is -3, Continue payoff 2x, and the other players' Continue mass is zero.

For sure owner3 and (x,y,z)=(q2,q0,q1), the differences are

    d2=(1-z)(1-6y)-99yz,
    d0=(1-z)(2-x)-97xz,
    d1=-3-10x+(15/4)y-(355/4)xy.

The same elementary best-response implications give x=0, z=1 and
y∈[4/5,1]. Owner3 payoff is -3 and Continue payoff 10y. Thus all four
sure-owner induced Nash sets really do fail the actual punishment-floor
compiler. The extension from a partial free set using the required fixed-
outsider signs is valid. The added conclusion excluding any one-shot Nash
root with a sure quitter follows: its other coordinates would belong to
one of these sets, where the sure quitter strictly gains from Continue.
This does not exclude an all-proper stationary root.

In particular this excludes EVERY pair/triple persistent-base and free-set
selection in `exists_uniformPayoff_of_persistentBase_inducedNash_signs`
and `nonempty_quittingPersistentBaseCertificate_of_inducedNash`, in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseNashSemanticAdapter.lean`.
Their induced free Nash inequalities, base leave signs and fixed-outsider
join signs together give a full zero-tail one-shot Nash root with sure
quitters, which was just excluded. Thus the argument checks the broader
existential large-base screen, not merely pointwise leave-safe base rewards.
`quittingPersistentLargeBaseExcess_nonpos_iff` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`
is the same remaining leave/join screen. No new base-by-base enumeration
or assumption that the supplied large-base point is pure is needed.

## Scope and acceptance

The final theorem has no supplied strategic witness. Its neighborhood is
produced from an explicit center and a nonsingular local finite system;
the same delta precedes every reward table and arbitrary grand row. Its
actual Nash and uniform-payoff outputs retain unrestricted deviations.

The final coverage discussion stays within the named singleton, literal
response quotient, nonnegative quiet-child, pair-partition and sure-owner
screens checked in the prior review. It explicitly distinguishes the
asymmetric separation witness from symmetric grand completions already
solved by response quotients. It does not claim disjointness from earlier
unspecified IFT neighborhoods or stationary nonexistence. These caveats
are necessary and are now present. I found no unresolved objection in
this bounded final-document check.

## Strengthened final transcription

PASS for the strengthened standalone supplied with hash
`561ba25d1ef933b423a5e65ca5604ab2703f97620000c79c100c4e5528cf5b3c`.
I verified that this exact file hash matches the checked document. The
P_rw/C_rw/F_rw partition has sizes32/12/16 with the correct recipient
indices and upper-only center values. The theorem's fixed delta precedes
every finite original table, imposes no C lower bound or F restriction,
and retains the fixed actual target before accuracy. The auxiliary delta0
cylinder proof and proxy delta0/2 reduction are faithfully incorporated.
The unchanged-profile/target/cutoff transfer uses the full behavioral
pathwise comparison, not a finite endpoint approximation. The whole
persistent-base/free-selection exclusion and its actual adapter declarations
are also present. No new soundness or scope objection was found in this
bounded transcription check; the prior independent algebra and source
reviews remain the substantive checks.
