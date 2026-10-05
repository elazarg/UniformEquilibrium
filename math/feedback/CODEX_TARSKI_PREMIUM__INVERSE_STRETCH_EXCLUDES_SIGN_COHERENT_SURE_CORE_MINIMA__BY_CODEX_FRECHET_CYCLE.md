# Independent review: inverse stretch at sign-coherent sure-core minima

Reviewer: CODEX_FRECHET_CYCLE.

Reviewed source:
[TARSKI's manuscript](../notes/CODEX_TARSKI_PREMIUM__INVERSE_STRETCH_EXCLUDES_SIGN_COHERENT_SURE_CORE_MINIMA.md),
SHA256 `dfec6e33e1bfcc80cfaf4699a0cfd42ac2a2b3ac694d646caddd8b897e077cdc`.

## Verdict and scope

PASS for the stated limited branch theorem, as ordinary mathematics. I
reconstructed the argument and attempted to falsify its full-cap,
table-transfer, saturation, and finite-support steps without reading
NOETHER's review. No mathematical repair is requested. This is not a
Lean-checked theorem or a resolution of the remaining mixed sure-core arm.

The genuine input is more than a same-table stationary certificate. The
final table must retain provenance from stretching ONE original full-cube
maximizer. An actual, unpadded, at-least-two-sure product root must attain
the unrestricted global MAX infimum at the final table. All four directed
best-action differences must be nonnegative at every supported opponent
configuration. These assumptions force an actual supported pure exact
equilibrium and contradict the positive minimum. For three sure owners,
the optional player's coherence is automatic, so some sure owner's
membership preference must reverse strictly across the optional support.

The positive result consumes this sign-coherent source branch. It neither
proves coherence nor handles the sign-reversing branch, and it does not
eliminate singleton or Never mass from arbitrary minimizing sources.

## 1. Independent reconstruction of the complete responses

Let K contain at least two players who Quit surely at date zero. After
deleting any deviator i, a different member of K still Quits at zero.
Consequently i's full behavioral response payoff is a convex combination
of exactly two values: Quit at zero, or Continue at zero. Every later
finite time and Never has the latter payoff. There is no time before zero.
This holds both at the mixed root and at every pure vertex of its product
support. It also holds at BOTH reward tables, regardless of how the four
own-singleton entries were reselected.

The endpoint coalitions are nonempty. Even when deleting a sure owner
leaves a singleton, that singleton belongs to a DIFFERENT player. Thus all
relevant coordinates belong to the 56 stretched coordinates, never one of
the four reselected own singletons. The actual root, not a payoff lottery,
is the competitor in the original table.

For the source-best action b_i, let β_i be its opposite action's prescribed
probability and c_i(z) its directed original-table edge gap. Under the
pointwise nonnegative hypothesis, b_i remains a best response at both
tables, and independence gives exactly

    d_i(original,q)=β_i E[c_i],
    d_i(final,q)=β_i E[T_α(c_i)].

The full cap maximum, rather than a selected response, is used here. No
maximum over a missing third response is being suppressed.

## 2. Global facts and the comparison between tables

I independently checked the all-player-tie argument rather than assigning
checked status to HILBERT's ordinary-mathematics draft. The checked MAX
singleton margin gives B_i−s_i≥m at a positive global minimum. Since
B_i−U_i≤m, every U_i≥s_i. If owner k has d_k<m, its private solo prefix
of probability h has the exact complete debts displayed in the source:

    d'_k=d_k+h(U_k−s_k),
    d'_j=max((1−h)(s_j−U_j)+h(r_j(kj)−r_j(k)),
              (1−h)d_j),  j≠k.

Taking h positive below the stated three strict bounds makes every branch
less than m. This contradicts the UNRESTRICTED global minimum, not a
fixed-calendar optimum. The actual semantic pair belongs to the carrier;
continuity extends its lower bound to that carrier, as the final source
explicitly explains. No total-debt theorem is imported.

The strict-half argument is also valid with signed own singletons. At an
attained positive minimum, B_i≤1 and the moat imply s_i≤1−m. All Never
has full regret a=max_i(s_i)_+, hence m≤a≤1−m. Equality a=m would make
all Never another global minimum, where a positive maximizing singleton
owner has B_i=s_i, contradicting its moat. Thus m<a≤1−m and m<1/2.

For nonnegative c, the stretch obeys T_α(c)≥c, with equality exactly at
c=0 and c=2. Therefore every original-table debt of q is at most m. The
original full-cube optimum supplies the decisive sandwich

    Ω=η(original)≤E_original(q)≤m=η(final)≤Ω.

This proves both actual global attainment at the original table and
equality of the two objective values. Applying all-player ties again at
the ORIGINAL table is essential: equality of the two maxima alone would
not give equality of all four debts. With that step, every debt equals m
at both tables. Since m>0, every β_i>0, and all supported configurations
have positive probability. Equality of the nonnegative inverse-stretch
losses therefore forces each supported c_i to be 0 or 2.

No coordinate normality is used in this comparison. In particular, the
proof does not transfer the original 60-coordinate normal to the final
four-coordinate fiber source. Fiber maximization supplies the specified
source; only its actual minimum and the inequality m≤Ω enter this step.

## 3. Finite-vertex conclusion and an exact boundary attempt

At a supported pure vertex x, owner i's full debt is exactly 2 on

    A_i={x_i≠b_i and c_i(x_−i)=2},

and is zero otherwise. The product source gives Pr(A_i)=m/2. Hence the
expected integer number of bad owners is 2m<1. Some supported vertex has
no bad owner. It preserves every sure member of K and has full regret
zero at both tables. This is a deterministic supported vertex used as one
actual competitor, not a correlated lottery implemented as independent
play. Every unilateral response absorbs at date zero.

I tested whether the non-strict bound m≤1/2 would suffice. It does not
suffice for the finite counting step. Here is an exact saturated boundary
pattern with sure owners 0,1 and independent fair optional bits x_2,x_3.
Take preferred actions b=(0,0,1,0), directed gaps 0 or 2, and set the
positive-gap configurations as follows:

    c_0=2 exactly when (x_2,x_3)=(1,0);
    c_1=2 exactly when (x_2,x_3)=(1,1);
    c_2=2 exactly when x_3=0;
    c_3=2 exactly when x_2=0.

Each positive edge is implemented by preferred reward +1 and opposite
reward −1; zero edges have both rewards zero. These assignments occupy
disjoint owner-edge coordinate pairs and define a valid signed table.
Set its four own singletons to zero. At the mixed root all four debts
equal 1/2. The four supported optional vertices have debt vectors

    (0,0): (0,0,2,0);   (0,1): (0,0,0,2);
    (1,0): (2,0,0,0);   (1,1): (0,2,0,0).

Thus each vertex has exactly one bad owner and no supported vertex is
Nash. This is NOT a counterexample to the manuscript: all Never is exact
Nash in this table, so the mixed root is not a positive global minimum.
It checks that the manuscript's strict-half/global-minimum step is doing
real work and that saturated positive edges cannot simply be discarded.

## 4. Other falsification attempts and exact computations

- Zero directed edges: these remain exactly zero, so no artificial strict
  improvement is assigned to them. Equality leaves precisely {0,2}.
- Degenerate optional hazards: summation is over actual positive-probability
  configurations. No absent action is divided by its probability, and the
  finite vertex still retains the original sure pair.
- Changed signed own singletons: I changed all four independently in exact
  two-sure root calculations. The unpadded cap comparison is unchanged.
  A silent prefix would invalidate this invariance: an outsider with zero
  membership endpoints can obtain its reselected positive own singleton
  by quitting before the sure pair. The source correctly excludes this.
- Sign reversal: coherence cannot be replaced by a positive average. For
  a directed gap equal to 2 with probability 2/5 and −1/2 with probability
  3/5, its mean is 1/2, while the stretched mean is 1/2−9α/10. Thus undoing
  stretch can INCREASE a positive best-action gap. This is exactly where
  the remaining sign-reversing branch escapes the proof.
- Exact rational computation confirmed the half-boundary table above.
  Its entire relevant table and product law are specified there, so the
  four displayed debt vectors are directly reproducible by membership
  endpoint comparison. This is a formula test, not global source existence.

## 5. Declaration audit, status, and handoff

I inspected the named declarations and their actual hypotheses in:

- `minimumTerminalSemantic_exploitabilitySingletonMargin`, in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDynamicCostate.lean`:
  this is the positive MAX carrier-minimum margin, with no singleton-sign
  premise. It is not the all-player-tie theorem.
- `exists_twoSureProductRoot_realizing_jointCarrierPoint_of_strictMargin`,
  in `UniformEquilibrium/Diagnostics/Quitting/ZeroSingletonBehavioralLawProductBase.lean`:
  zero Never and all singleton masses plus strict cap margins give an
  UNPADDED root-then-Never realization of the whole semantic pair and law.
  Its nonstrict neighboring theorem gives a padded realization and cannot
  replace it in the original-table comparison.
- `quittingTerminalSemanticPair_pureSetRootThenContinuation_eq_of_two_le_card`,
  in `UniformEquilibrium/Quitting/Paths/SureExitSet.lean`: the complete
  pure-vertex cap is independent of every declared continuation.
- `exists_singletonColumnBlockerCertificate_of_fourPlayer_noUniform`, in
  `UniformEquilibrium/Quitting/Classification/LCP/FourPlayerSingletonColumnBlockers.lean`:
  it does supply homogeneous infeasibility and a strict off-diagonal
  blocker in every singleton COLUMN. The manuscript correctly lists this
  as future source data, not a hidden premise in the proved branch.

I also reread the relevant actual stretch construction in the frozen
[singleton-fiber export](../exports/MEMBERSHIP_STRETCH_AND_SINGLETON_FIBER_SOURCE_REDUCTION.md)
and the complete all-player-tie proof in HILBERT's cited note. The bounded
named-source comparison found no checked declaration already expressing
this inverse-stretch branch consumer. This is not an exhaustive priority
claim. The ordinary all-player-tie proof and finite saturation argument
remain mathematical inputs for formalization, not pre-existing Lean seals.

No author note, export, Lean source, or shared index was changed in this
review. The exact remaining task is to consume supported membership sign
reversals using the same actual/global source; this review provides no
permission to replace them by pointwise coherent inequalities.

## Final-byte acceptance

I read every byte of the final mathematical-name candidate
[Inverse membership stretch forces sure-core sign reversal](../formalized/INVERSE_MEMBERSHIP_STRETCH_SURE_CORE_SIGN_REVERSAL.md),
SHA256 `70d9ea22fd61290b1f24fbccdb0df57980a66518e87b7322a61efba810ad5aa7`.
PASS, with no unresolved mathematical objection or requested change.

The reviewed core proof is retained. The explicit final-table definition
of b_i, convex-combination response wording, probability/agency statement,
actual carrier adapter, and handoff do not enlarge its assumptions or
conclusion. In particular, the handoff must retain Section 1's strictly
positive stretch parameter, as its zero-parameter boundary test states.

I separately checked the added successful fixture: with q_2=1/2,
q_3=3/4 and b=(0,0,1,1), all four saturated losing events are exactly
optional configuration 00, of probability 1/8. Thus each source debt is
1/4 and each other supported optional vertex has four zero full debts.
The explicitly stated lack of positive global attainment is correct.
The critical-half and sign-reversal fixtures agree with the independent
checks above. The added two-sure reversal statement follows from failure
of coherence together with the strictly positive averaged best-action gap;
the negative and positive configurations both have positive source weight.

The new adapter invokes the strict-margin, unpadded, whole-semantic-pair
declaration actually inspected above. It does not infer cap preservation
from payoff equality or transport calendar multipliers. The final scope
correctly leaves sign-reversing and nonzero-singleton/Never arms open.
No candidate or export bytes were changed by this final check.
