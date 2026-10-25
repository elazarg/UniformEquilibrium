# Review of the nonnegative-cap root activity restriction

Reviewer: CODEX_ACTUAL_MINIMUM_ATTACK.

Artifact: [CODEX_UNEQUAL_GLOBAL__NONNEGATIVE_CAP_ROOT_ACTIVITY](../notes/CODEX_UNEQUAL_GLOBAL__NONNEGATIVE_CAP_ROOT_ACTIVITY.md).
Reviewed SHA256:

    60bb0f82ff861bcea332c1af6f78a27da77f1bac8ab2f5954f5693ff0abbb71a

**Mathematical verdict: PASS as an internal full-Nash-root theorem.**
No unresolved mathematical objection remains. This is not an export approval,
a UE theorem, a source-branch exclusion, or a Lean check.

## Exact reviewed scope

For the specified sixty-entry calibration, one positive epsilon0 works for
all independently chosen 0<e,h1,h3<epsilon0. A full exact Nash root between
nonnegative native input and output annotations, with input coordinate C2<=2,
can activate player0 only as a solo root. Such a root has C0=W0=0.
The other input coordinates need not have upper bounds.

The final artifact explicitly uses native annotations: its original root
continuation and output are 1+C and 1+W. This clarification is necessary;
the assertion with unshifted original C and W would be false even for a solo
root. It does not shift the original game's live or Never payoff.

## Proof checks and attempted falsification

I checked every proper support containing0. The two-owner and supports012,
013 contradictions follow from a strictly positive passive singleton payoff
dominating the small participant premium. For023 the three displayed ratio
inequalities have product greater than one. These arguments permit sure
hazards and do not require output nonnegativity.

For full support, output nonnegativity supplies Q1,Q3>=0 and hence
xzw=xyz=0 in a zero-premium limiting sequence. The active endpoint
inequalities then force the limiting x to vanish. Compactness is applied
only to the hazards: the proof never assumes boundedness of C0,C1,C3.

The split according to z_n<1 or z_n=1 is essential and correct. In the
mixed-player2 case, C2<=2 gives the exact inequality
4y+3w-2yw<=2. Together with z<=min(3w,2y), its two cases give strictly
negative row0 gain unless the entire limiting hazard vector vanishes.
In the sure-player2 case, the additional sure/mixed subsequences for owners1
and3 give respectively the incompatible equations 5/3=3/2 or 10=5.
No sure-boundary case is silently treated as an indifference equation.

Finally k=(9,7,0,8) has k*Gamma=(6,11,6,6). The cubic remainder bound
yzw<=s^3/27 gives (R7), which excludes every sufficiently small nonzero
full-support root. Combining this explicit local contradiction with the
compactness argument yields a single positive epsilon0, with no ratio
restriction on the three premiums.

## Source boundary and contribution disclosure

The canonical incoming head has zero observer root regrets, but the pivot
regret can be positive. It also need not have nonnegative caps at every
finite intermediate state. Thus the reviewed full-Nash theorem does not
apply automatically to that head, even after proving eventual nonnegative
caps. In particular neither finite pivot support nor exclusion of an all-zero
endpoint follows from this theorem.

I supplied the final note's exact counterexample to the attempted
observer-Nash extension, and independently recomputed all its outputs:
q=(1/10,0,0,1/10), C=(0,1,1,(1+h3)/9) give zero observer root debts,
nonnegative input/output caps, C2=1, simultaneous0/3 activity, and positive
pivot regret (3-e)/100. This contribution concerns the scope boundary,
not the proof of the full-Nash theorem, which I checked independently.
The example does not claim that C is an actual global-minimum ancestral tail.

I inspected the exact hypotheses of
`quittingRoot_activeHazards_lt_one_of_leave_sums`
(`UniformEquilibrium/Quitting/Classification/BoxedQuittingNashCharges.lean`)
and `exactRootSuccessor_active_eq_singleton_of_support_not_premiumTrap`
(`UniformEquilibrium/Quitting/Classification/QuittingPremiumCoreExactRoot.lean`).
Their hypotheses are not silently supplied to this family; the new proof
is self-contained. The canonical boundary note's observer-only optimality
is explicitly distinguished from full root Nash. No Lean command ran.

The internal note retains useful exact mathematics and a precise failed
source implication. Its current status correctly makes no additional
arbitrary-behavior counterexample exclusion.
