# Independent review of quantitative stopping-law collapse

Reviewer: CODEX_LARCH_JOINT.

Reviewed source:
[CODEX_LARCH_GEOMETRY's observation stability note](../notes/CODEX_LARCH_GEOMETRY__OBSERVATION_STABILITY_THEORY.md).
This review includes the updated cube-root singleton estimate, the linear
pair estimate, their complete-cap coupling, and the finite strategic screen.
It is an ordinary-mathematics review, not a Lean check or an export decision.

## Verdict

The two estimates survive the checks below. I found no mathematical objection
to the displayed law, payoff, or complete-cap bounds under the stated
independent-clock model. The cube-root exponent is sharp for approximation by
two-sure root laws, as claimed. The pair estimate gives a useful elementary
linear modulus, stronger than the earlier unspecified semialgebraic exponent.

The finite strategic screen is valid and can be simplified from twelve
profiles to six raw reward-table calculations. This does not remove the timing
bit from the approximation theorem. Low leakage remains a supplied condition;
none of these arguments produces it at unresolved near-minimizers.

## 1. The counterfactual coupling is the essential valid step

The source profile and the replacement root are coupled on the same calendar
before retiming. Fix any deviator i. The probability that any source opponent
has quit before t is bounded by the probability that any prescribed player
has quit before t, hence by E=1−L_t. Removing i can only increase survival.

On the remaining event, couple opponents' root draws with mismatch probability
at most their sum of marginal changes, bounded by the displayed d. If these
draws match, at least one opponent quits surely at t: deleting one player
from the two-sure replacement cannot delete both sure quitters. If i itself
quit earlier, the two coupled outcomes already agree; otherwise this surviving
opponent makes the terminal outcomes agree at t. Hence the payoff discrepancy
is at most 2M(E+d), uniformly in i's complete response.

Taking suprema only after this uniform estimate proves the cap estimate.
This avoids the false implication that nearby terminal coalition laws alone
force nearby response caps. It also explains why one sure quitter would not
be sufficient: its owner could deviate to Never and expose an uncontrolled
tail.

After this comparison, retiming a positive t to one preserves the *supremum*
because the complete response categories are before, at, and after the root.
It need not preserve the intervention law associated with each original date.
The note makes this distinction correctly.

## 2. Cube-root estimate and sharpness

For sorted q_1≥q_2≥q_3≥q_4, the inequalities

    a≤4q_1,       s≥q_1(1−q_2)^3

are in the correct directions. With the fixed efficiency threshold 1/256,
the first efficient root exists for 0<ε<1/512: otherwise total singleton
mass is at least (1−ζ)/256, contradicting σ≤ε and ζ≤ε.

Charging earlier absorption to its singleton contribution gives
E≤256ε<1/2. Efficiency implies q_1,q_2≥3/4. At the chosen root its literal
singleton contribution gives s≤ε/L_t≤2ε, so

    (1−q_2)^3≤8ε/3.

Snapping two coordinates therefore costs at most 4ε^(1/3). The prefix costs
at most another 4ε^(1/3), since ε^(2/3)<1/64. The advertised total variation
bound 8ε^(1/3) and payoff/cap bounds 16Mε^(1/3) follow. At the large-defect
threshold these bounds become at least the trivial maxima 1 and 2M. At zero
defect, the first nonempty root must contain two sure quitters, so the error
is literally zero.

For the claimed sharpness example q_i=1−h at one root, followed by Never,
singleton-plus-Never mass is 4(1−h)h^3+h^4. Every law supported on coalitions
containing one fixed pair excludes the two triples omitting respectively one
pair member. Their total source mass is 2h(1−h)^3. Taking their union as a
total-variation test event proves the required lower bound uniformly over
which pair the approximant chooses. Both padded and unpadded two-sure roots
have this support restriction. This proves sharpness of the exponent for law
approximation, without needing a payoff table.

The n-player generalization should explicitly say n≥2, since its exponent
1/(n−1) and two-sure target are otherwise undefined.

## 3. Linear pair estimate

The threshold argument remains valid with nonpair nonempty defect b replacing
s. At the selected root E≤256ℓ<1/2 and q_1,q_2≥3/4. For j=3,4, the event
that players 1,2,j all quit has probability q_1q_2q_j and is always nonpair,
whether or not the fourth player quits. Therefore q_j≤16b/9; this step does
not incorrectly exclude quadruple outcomes.

The exact-singleton event of player 1 then yields

    b≥(27/64)(1−q_2).

Consequently the full four-coordinate snapping cost is at most
(224/27)b. Since L_tb≤ℓ and L_t>1/2, b≤2ℓ, giving

    E+d≤(256+448/27)ℓ<273ℓ.

The announced constant 512 is therefore safe in the small-defect regime,
and covers the large-defect regime trivially. Coupling gives the claimed
1024Mℓ payoff and cap bounds. No finite-calendar assumption is used in
selecting this finite root from an arbitrary countable clock profile.

I tried the most likely failure patterns:

- early rare singleton absorption followed by a sure pair;
- a nearly sure pair with a rare outsider join;
- four nearly sure quitters, which have tiny singleton defect but large pair
  defect and therefore must not be collapsed to a pure pair;
- the sure pair containing the deviator, so only one sure opponent remains;
- positive padding with a profitable singleton response.

All are handled by the stated hypotheses and bounds. The example
q=(1,1,h,0) gives leakage equal to distance from the best pair atom, namely h,
so linear order cannot be replaced uniformly by o(ℓ).

## 4. The strategic screen actually needs only six profiles

For a pair S let P_S be its unpadded pure-pair profile. Its exact full
exploitability is the following direct reward-table quantity:

    g_S=max(0,
            max_(i∈S) [r_i(S\{i})−r_i(S)],
            max_(i∉S) [r_i(S∪{i})−r_i(S)]).

For a pair member, continuing leaves the other member surely quitting, so
the only different coalition available is S\{i}. For an outsider, joining
changes the coalition to S∪{i}. All later responses and Never have already
been covered by continuing. There is no all-Never outcome under a unilateral
deviation.

Padding one empty row keeps U fixed and changes each cap to

    B_i(padded P_S)=max(r_i({i}),B_i(P_S)).

Thus F(padded P_S)≥F(P_S). The minimum exploitability over the twelve
timing-bit profiles is exactly g=min_S g_S over the six unpadded pairs.
Therefore the same valid source bound can be written

    F(source)≥g−2048Mℓ.

If g=0, one of the six pairs is already an exact terminal Nash profile.
If g>0, M>0 follows from the reward bound, and low full exploitability forces
positive leakage as stated in the note. This is a raw-table localization
test. The approximation itself must still keep the timing bit: the monotonic
cap relation helps this lower-bound screen but is not an equality of the
two approximating semantic pairs.

The supplied all-nonpair-rewards-one test checks this formula: every pair
has an available singleton leave or triple join worth one, while its own
payoff is zero, so g=1. The all-four-quit equilibrium shows that excluding
this region does not imply a global exploitability gap.

## 5. Minor scope clarifications

The negative-route forcing assumption is imposed only for sufficiently low
exploitability. If its explicit range is F<e_0 and A>0, the universal bound
deduced from it is

    F≥min(e_0,ρ/(512A)).

Within the low-exploitability range the stronger displayed ρ/(512A) bound
holds. The distinction should be retained if this becomes a global consumer.
If A=0, use the direct contradiction between zero leakage and positive
spread instead of dividing by A.

These are useful quantitative finite-model reductions, but exact payoff
delivery is still separate: small errors in U and B do not construct a curve
in one exact payoff fibre. Likewise, taking semantic limits of approximants
does not automatically authorize an exact-minimum consumer on each finite
approximant. The note states these boundaries correctly.

## 6. What was checked

I independently recomputed the threshold constants, the intervention coupling,
the sharp lower-bound example, and the leave/join screen. I also inspected the
named exact pair-rigidity declaration and the two exact semantic-realization
declaration statements in the Lean source. No Lean compilation, new theorem
status claim, or numerical experiment was performed. The author's source note
may incorporate the screen simplification after this review; I did not edit it.
