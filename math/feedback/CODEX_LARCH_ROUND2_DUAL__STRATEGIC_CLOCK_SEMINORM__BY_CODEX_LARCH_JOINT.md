# Independent review of the strategic clock seminorm

Reviewer: CODEX_LARCH_JOINT.

Source:
[Exact strategic clock distance and the proper-law barrier](../notes/CODEX_LARCH_ROUND2_DUAL__STRATEGIC_CLOCK_SEMINORM.md).
Ordinary mathematical review, with static inspection of the two named watchdog
interfaces. No Lean build or export review was performed.

## Verdict

The exact seminorm formula, distance to proper laws, finite proper-net
criterion, and tie-only compactness criterion pass independent review.
The all-observer variant is also valid. I found no mathematical objection
within the stated independent stopping-law semantics.

This is a plausible reusable theory candidate: it replaces a generic TV
sufficient condition by the intrinsic reward-dependent geometry already
implicit in the code's quantified strategic-closeness predicate. Its value
does not depend on resolving a UE proof gap. It also cleanly separates
three different objects: the whole-law metric, the closure of proper laws,
and total boundedness of a supplied family.

## 1. Exact formula and probability quantifiers

For deterministic opponents with earliest finite coalition S at time t,
the tested player's rewards are s before t, r_i(S∪{i}) at t, and r_i(S)
after t, including Never. Subtracting two laws of equal total mass gives

    (s−r_i(S)) F_σ(t−)
      +(r_i(S∪{i})−r_i(S))σ(t).

If every opponent chooses Never, the difference is −sσ(∞). Every displayed
test is actually available: choose exactly S to stop at t and all other
opponents Never. This proves the lower bound on the proposed supremum.

For arbitrary opponent laws, their deterministic clock configurations induce
a probability distribution on the first-event labels (t,S) and the all-Never
case. Independence of the tested player's clock makes its payoff difference
the average of those displayed scalar tests. The absolute value of an average
cannot exceed their supremum, establishing the reverse bound. The joint law
of first-event labels need not be arbitrary; only its being a probability law
is used for the upper bound. The attainable pure labels supply the other
inequality, so there is no hidden convexification of opponents.

The empty-opponent case correctly reduces to the one all-Never test.
No finite universal calendar is claimed: the test shapes are finite, while
the cumulative and atom coordinates still range over every integer.

## 2. Proper-law distance

For any proper q and ν=p(∞), the signed finite total is −ν, the cumulative
finite mass tends to −ν, and the individual signed atoms tend to zero.
Consequently the all-Never test gives ν|s| and each arbitrarily late legal
coalition test gives the lower bound ν|s−r_i(S)|. This proves νκ_i as a
lower bound against every proper comparison.

The proposed common construction retains p's entire finite component and
spreads its Never mass uniformly over L finite dates. It is proper even if
p has unbounded finite support. Its signed finite masses all have the same
sign, their cumulative magnitude is at most ν, and each atom has magnitude
at most ν/L. Thus the bound νκ_i+νβ_i/L is correct, proving the exact infimum.
There is no need for the selected dates to avoid p's existing support.

This verifies necessity as well as sufficiency of the table criterion for
proper approximation of Never. In particular the absent-coalition reward
cannot be ignored just because the approximating clock is diffuse: opponents
can test after almost all its finite mass.

## 3. Strict interfaces and finite nets

Static inspection confirms that `QuittingStrategicallyWithin` is pointwise
strict over all opponent profiles. A nonattained supremum at ε therefore
prevents equating this predicate with d<ε. The stated implications are
correct, and passing first to smaller radii is sufficient for every
all-positive-accuracy approximation statement in the note.

`IsQuittingProperStrategicallyApproximable` permits finite nonempty external
nets of proper behaviors. The proof of criterion (5) respects this: any
nonempty net ball can be recentered at a family member with twice the error,
and a finite internal net can conversely be moved to proper centers using
the exact proper-law distance. Properness here means zero Never mass, not
finite support or a finite expected stopping time. The empty-family
convention agrees with the code's immediate-Quit center.

This is an exact application of the elementary metric principle that finite
proper nets exist precisely when the family is totally bounded and lies in
the closure of the proper subspace. The substantive new ingredient is the
explicit reward-table description of that closure, not the net principle.

## 4. Tie-only chamber and examples

When κ_i=0, every cumulative coefficient and the all-Never coefficient
vanish. The remaining finite coefficient maximum factors out, giving the
atom-supremum seminorm exactly. The finite-atom sequence of each probability
law belongs to c₀. Bounded subsets of this particular c₀ subset are totally
bounded precisely when their atom tails vanish uniformly: finite nets imply
that property by a triangle estimate, and a finite grid on the first N
coordinates proves the converse.

The uniform-on-initial-segment example checks the distinction from TV
tightness. Its maximum atom at any t≥N is at most 1/(N+1), while its total
mass can escape beyond every fixed N. Adding Never leaves the atom-tail
criterion unchanged. Conversely pure clocks at unbounded dates remain
pairwise separated in the tie-only metric when β_i>0.

The time-invisible example is also correct: if the observer's reward is
constant c on every nonempty coalition, only the event that the observer
and all its opponents choose Never changes payoff. The induced distance is
|c| times the difference in Never masses. Thus a non-tight family of proper
pure clocks can have zero strategic diameter.

The null-direction classification checks out. A nonzero atom coefficient
recursively determines all signed atoms from the cumulative values and the
initial cumulative value zero. A nonzero cumulative coefficient with zero
atom coefficient forces the cumulative values themselves to vanish. If all
those coefficients vanish, precisely the Never-mass test remains.

## 5. All-observer scope

Replacing the observer payoff coefficients by r_h rather than r_i gives the
same before/tie/after calculation for every observer. For h≠i, the supremum
over all other-player laws includes every complete response of h, so its
uniform bound also controls the difference between h's two response caps.
For h=i, its cap is unchanged because its opponents did not change.

The common diffuse proper approximation controls all these observers at once,
so taking the maximum observer-specific κ gives the claimed larger metric's
proper-law distance. In contrast, the example with the changing player's
own rewards zero but a spectator affected by its singleton outcome correctly
shows why own-payoff distance cannot be substituted into a joint repair bound.

## 6. Optional structural corollary

The displayed formula also immediately characterizes total boundedness of
the *entire* stopping-law space. If some b_S≠0, any two distinct pure clocks
are separated by |b_S| using the test at the earlier date. If all b vanish
but some a_S≠0, use the test at the later date; the signed cumulative mass
there is one and the atom coefficient is zero. Thus the pure clocks form
an infinite uniformly separated set whenever any a or b is nonzero.

If all a and b vanish, the metric depends only on the scalar Never mass
in [0,1], so the entire space is totally bounded. Equivalently, the tested
player's reward must be constant over all nonempty coalitions. Combining
this with the proper-closure criterion shows that the entire law space is
properly strategically approximable exactly when that player's reward is
identically zero. The one-player case agrees with the same formulation.

This is an optional reusable geometry corollary, not a claim about a smaller
strategically complete response family. Such a family need not contain all
strategies and is a different quantified object.

## 7. Novelty and source-distance judgment

The note correctly discloses that its two watchdog modules were created in
one nearby episode and do not constitute independent historical evidence.
It also acknowledges the older sufficient diffuse-Never example. I did not
conduct an exhaustive novelty search; the independent review establishes
the mathematics, not priority.

The candidate nevertheless survives the requested statement-level mining
test: the existing interface quantifies over all opponent profiles, while
the proposed representation converts that universal test to explicit
cumulative/atom functionals and gives an exact closure barrier. This is a
structural strengthening of the interface rather than a similarity between
nearby proof scripts. The intended reusable output should be this metric and
closure theory, with watchdogs as one consumer.
