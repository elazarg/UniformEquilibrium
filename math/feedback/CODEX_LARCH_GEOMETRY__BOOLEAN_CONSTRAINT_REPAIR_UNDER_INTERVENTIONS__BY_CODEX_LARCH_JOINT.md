# Review and strengthening of Boolean strategic constraint repair

Reviewer: CODEX_LARCH_JOINT.

Source:
[Boolean constraint repair](../notes/CODEX_LARCH_GEOMETRY__BOOLEAN_CONSTRAINT_REPAIR_UNDER_INTERVENTIONS.md).
Ordinary mathematical review only; no Lean checks or export.

## Provenance and verdict

I independently reviewed the original fourth-root rounding draft and found
its support, coupling, and threshold arguments valid. During review I proposed
the stronger pair-first argument recorded below, so this is **review plus
mathematical strengthening**, not a claim of independent derivation of the
strengthened proof. An additional reviewer should check that strengthening
before it is described as independently reviewed.

The strengthened candidate is: for every nonempty allowed family H of
four-player coalitions of size at least two, every actual source with defect
d=d_H admits an actual H-supported product root, with zero or one padding row,
satisfying

    TV(source law, model law)≤9d^(1/3),
    |U_i(source)−U_i(model)|≤18Md^(1/3),
    |B_i(source)−B_i(model)|≤18Md^(1/3).

The proof below is elementary and retains the original profile in all cap
comparisons. The cube-root exponent is uniformly optimal over such H because
the allowed family of all nonsingletons already has the sharp example in the
companion geometry note. Sharper families, such as pairs, can still have a
linear modulus.

## 1. Validation of the original rounding argument

Its chosen first efficient root has E≤256d<1/2 and forbidden nonempty
probability b≤2d. For threshold η=(2b)^(1/4), every rounded-support atom had
all four original factors at least η, hence original probability at least
2b. Therefore no forbidden atom survives. The coordinate bounded below by
3/4 remains positive, so the repaired product has some nonempty support.
Because H excludes singletons, the product-support Boolean interval must
have at least two sure coordinates. Its support therefore also excludes
the empty atom. This last conclusion is not assumed merely from omitting
the empty event from b.

The numerical estimate 256d+4(4d)^(1/4)≤5√2 d^(1/4) for d<1/1024 is
correct. The complete cap coupling then works by deletion of at most one
sure quitter, precisely as in the first geometry review.

## 2. Stronger argument: establish the sure core before rounding

Work with 0<d<1/512. The same first efficient root, with b≤a/256, has

    E≤256d<1/2,       b≤2d,       q_1,q_2≥3/4,

where coordinates are sorted decreasingly. All singleton root outcomes are
forbidden. Consequently

    b≥q_1(1−q_2)^3,
    (1−q_2)^3≤(4/3)b≤(8/3)d.

Snap q_1,q_2 to one. This costs at most

    2(8d/3)^(1/3)<3d^(1/3).                         (A)

If b>0, set η=sqrt(32b/9). It is less than 1/4 because b≤a/256≤1/256.
Round only the two remaining coordinates to zero below η and to one above
1−η, leaving the middle values unchanged. Their total modification is at
most 2η. Every atom in the final support contains {1,2}; each of its other
two original factors is at least η. Its probability under the *original*
root was therefore at least

    q_1q_2η²≥(9/16)(32b/9)=2b.

No such atom can be forbidden. This is the key improvement: fixing the high
pair removes two small factors from the forbidden-atom test. The repair does
not compare forbidden probabilities after an uncontrolled first rounding;
it tests the final atoms directly under the original root.

Since b≤2d, the optional-coordinate modification is at most

    2η≤(16/3)sqrt(d)<2d^(1/3),                      (B)

where the final inequality uses d<1/512 and
(16/3)(1/512)^(1/6)=8/(3√2)<2. Also

    E≤256d<4d^(1/3).                                (C)

Together (A)–(C) give total coupling error below 9d^(1/3). When b=0,
there are already two sure quitters and every root atom is allowed; no
rounding is needed. At d=0 use the first positive absorption root directly.
For d≥1/512 choose any pure coalition in H: 9d^(1/3)≥9/8>1 covers the
trivial total variation bound and 18Md^(1/3)>2M covers payoffs and caps.

Thus the proposed 9/18 constants check without numerical approximation.
The same single-deviator coupling and timing-bit retiming used by the original
note apply unchanged to the repaired root.

## 3. Exact models, counterexamples, and consumer

The product-support interval description is correct. Closed parameter cubes
are appropriate for taking model minima: if an optional probability reaches
zero or one, the support shrinks to a subinterval still contained in H.
Therefore the finite union of model cubes is compact and its complete cap
function is a finite maximum of continuous reward polynomials. The model
minimum is attained, not merely an infimum over open support cells.

The stated disconnected family has exactly the two maximal compatible
intervals displayed in the source. A convex lottery between its base pairs
is not a substitute for one of these independent product models.

The singleton counterexample is sound: a sure first quitter hides an opponent
who stops later; deleting that quitter reveals a positive cap absent from
every one-root model supported on its singleton. Thus forbidding singleton
patterns is a strategic robustness condition, not merely a convenient
combinatorial normalization.

Screening needs only the unpadded model cubes because padding preserves U
and can only increase B. If their minimum exploitability is g>0, the updated
bound gives

    E(source)≥g−36Md^(1/3),
    E(source)<g/2  ⇒  d>(g/(72M))³.

The constants here are twice the payoff/cap coordinate estimate, since one
regret is a cap minus a payoff. Positive g implies M>0. If g=0 the compact
model minimum supplies an actual exact terminal Nash profile. A positive g
only localizes low-exploitability sources away from H; no global gap follows
without a separate same-profile forcing theorem.

## Final check status

The original fourth-root statement passes independent review. The cube-root
upgrade, constants, and revised consumer above are a reviewer-proposed proof
sketch; I checked the author's final updated write-up against this argument
and found no discrepancy. It awaits an additional independent check. No arbitrary-source small
defect, actual reached chronology, exact payoff-fibre repair, or Lean result
is asserted.
