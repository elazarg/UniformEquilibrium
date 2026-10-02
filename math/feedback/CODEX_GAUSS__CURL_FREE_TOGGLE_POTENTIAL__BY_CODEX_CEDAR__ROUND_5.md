# Round 5 feedback on the linear-mixing witness

Reviewer: `CODEX_CEDAR`

Reviewed note: `notes/CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL.md`

Scope: Section 22, Proposition 13 only.  I did not review the later
deadlock-core Propositions 14--16 in this round.

Status: `VALID_AFTER_ONE_NUMERICAL_INTERVAL_REPAIR`

## Claim checked

The proposition gives a literal 13-player quitting table whose normalized
singleton matrix has a four-player principal core equal, after reindexing and
positive scaling, to the checked `duplicatedCyclicMatrix`; whose actual
stationary gap vector has a strict transformed face certificate on
`[11/25,14/25]^I`; and which has no Proposition 10 playerwise common-box
certificate, pure sure-exit set, or instant-no-join owner.

I refreshed the board and inspected the named declarations
`duplicatedCyclicMatrix`, `duplicatedCyclicMatrix_standardQ`, and
`duplicatedCyclicMatrix_noHomogeneous`
(`UniformEquilibrium/Quitting/Classification/LCP/StandardQSideExample.lean`),
`exists_uniformEquilibriumPayoff_of_normalCore_card_three`
(`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/AmbientCarrierElimination.lean`),
and `isQuittingInstantNoJoin_of_works`
(`UniformEquilibrium/Quitting/Punishment/InstantPunishment.lean`).

No Lean build was run.  The 13-player reward adapter, reindexing/scaling, and
stationary certificate are ordinary mathematics, not checked Lean facts.

## 1. Singleton matrix and normal core

For a singleton `{j}`, the owner coordinate is exactly one: the `delta` term
vanishes and neither cyclic successor equals the owner.  For `i!=j`, the
continuer coordinate is `1+M0(i,j)/10000`.  Hence the normalized singleton
matrix is exactly `M0/10000`.

Under `(0,3,6,9)=(none,some 0,some 1,some 2)`, the distinguished principal
matrix is

```text
[ 0  0 -1  2
  0  0 -1  2
  2  2  0 -1
 -1 -1  2  0 ],
```

which is literally `duplicatedCyclicMatrix`.  Every dummy row has all
off-diagonal entries `1`, so all nine dummies leave the first normal layer.
Every distinguished row has a distinct nonpositive witness within `D`, and
this remains true after the dummies disappear.  Thus the normal core is
exactly `D`, of cardinality four.

Reindexing and multiplication by `1/10000>0` preserve textbook standard Q:
for right-hand side `q`, apply the original solution at `10000q`.  They also
preserve homogeneous feasibility/nonfeasibility because the residual is
multiplied by a positive scalar.  The named checked facts therefore give the
claimed standard-Q and nonhomogeneous classifications.  The table is outside
the named normal-core-cardinality-three producer.

## 2. Conditional singleton mass and the one repair

For twelve opponent odds `x_j=p_j/(1-p_j)`, the conditional singleton mass is

`rho=(sum_j x_j)/(product_j(1+x_j)-1)`.

Its partial derivative numerator is

`Q(1-sum_(k!=j)x_k)-1`,

with `Q=product_(k!=j)(1+x_k)`.  Since each other odd is at least `11/14`, the
derivative is strictly negative.  Thus `rho` is maximized at
`p_j=11/25`, giving exactly

`(132/25)(14/25)^11/(1-(14/25)^12)
 =16198260678656/1804483359485313 <1/100`.

There is one literal error in the note.  The interval of singleton continuer
rewards is not

`[9999/10000,5001/5000]`.

The distinguished matrix contains the entry `-3`, so the correct interval is

`[9997/10000,5001/5000]`.

This does not affect `0<=V_i<=(5001/5000)rho`, nor any transformed face bound.
The only later use of the incorrect lower endpoint is the large-box weighted
monotonicity estimate.  Its corrected version remains strict:

`11(9997/10000)(1/10)=109967/100000
   >5001/5000>=w_j`.

Thus Proposition 13 survives, but the two occurrences of `9999/10000` should
be replaced before export or reuse.

## 3. Exact transformed face certificate

The Quit endpoint is

`R_i=1-p_(i+1)-p_(i+2)+delta(1-c_i)`

because the extra `delta` is paid exactly when at least one opponent Quits.
Writing `E_i=delta(1-c_i)-V_i`, `h_j=1/2-p_j`, and
`(Ch)_i=h_(i+1)+h_(i+2)` gives `G=Ch+E`.

For the 13-cycle, `C=P(I+P)` and

`(I+P)^(-1)=(1/2)(I-P+P^2-...+P^12)`.

The identity is exact because multiplying by `I+P` gives `I+P^13=2I`.
Every row of `A=C^(-1)` has `l1` norm `13/2`, and `A1=(1/2)1`.

Using `c_i<=(14/25)^12` and the verified singleton bound gives

```text
|AE|_infty
 <= 1/2000+(13/2)((1/1000)(14/25)^12+(5001/5000)rho)
 =324686827387488922420336785993591 /
  5515671263857722282409667968750000
 <59/1000.
```

The exact slack to `59/1000` is the positive fraction printed in the note.
Since `h_j=3/50` and `-3/50` on the two faces, `AG=h+AE` has strict inward
margin greater than `1/1000`.  Proposition 11's invertibility/Brouwer theorem
therefore supplies an interior zero of `G`.  Its named stationary endpoint
consumer covers all unilateral behavioral deviations once this ordinary
reward adapter is supplied.

## 4. No playerwise common-box certificate

The displayed-box falsifiers check.  On an actual blocker upper face, setting
the other blocker low makes the affine term zero and the exact
`rho_special` calculation makes `E_i>0`; setting the other blocker high makes
the affine term `-3/25`, while `E_i<=1/1000`, so the gap is negative.  A
nonblocker face allows both actual blockers low or both high; the affine terms
`3/25` and `-3/25` dominate the global error bounds.

The extension to every common box also survives:

- Neither cyclic successor of any distinguished player is distinguished, and
  dummy rows are constant off the diagonal.  Hence the two blocker singleton
  rewards agree.  Swapping blocker probabilities between `alpha` and `beta`
  leaves both the affine term and `E_i` unchanged, producing equal values on
  the alleged opposite faces and ruling out strict signs.
- For a nonblocker coordinate and `beta<1/11`, the symmetric diagonal gap
  `f_i(t)` is strictly increasing.  The derivative estimate
  `dot rho>1210000000000/385311670611>3`, together with the positive row-average
  singleton reward, gives `f_i'(t)>1`.  Therefore a positive lower face and
  negative upper face are impossible.
- For `beta>=1/11`, holding the other eleven opponents at `beta` gives
  `S>=109967/100000>w_j` after the corrected lower endpoint.  The exact odds
  derivative shows that increasing the proposed nonblocker coordinate
  decreases `V_i` and increases `delta(1-c_i)`, while leaving the affine term
  fixed.  The gap increases from lower to upper face, again contradicting the
  required orientation.
- `p_i` does not enter `G_i` at all.

Thus every possible gap/coordinate matching fails on every common box, not
only on the displayed rational box.

## 5. Sure-exit and instant-punishment exclusions

The empty set fails because every own solo reward is one.  A singleton
`{o}` fails by choosing `j` whose two successors avoid `o`: joining pays
`1001/1000`, while its singleton continuer payoff is at most `5001/5000`.

For `|S|>=2`, an outsider can profitably join unless both successors are in
`S`; a member with both successors in `S` gets `-999/1000` and profits by
leaving.  Stable membership words would therefore satisfy

`0 -> 11` and `1 -> not 11`.

Any zero begins the forced word `0110`, hence the word is 3-periodic; the
all-one word violates the member condition.  Since `3` does not divide `13`,
no word closes.  This exhausts every pure sure-exit set.

The same strict singleton joining deviation excludes
`IsQuittingInstantNoJoin` for every owner.  The named necessity theorem
`isQuittingInstantNoJoin_of_works` therefore excludes the checked instant
punishment route.

The table is not cardinally symmetric or circulant: its normalized singleton
matrix has a distinguished four-player core and dummy rows.  It is not a
core-cardinality-three case.  These are strict named exclusions, not a claim
against every repository producer.

## 6. Correct novelty status

The exact three-owner cycle `(3,6,9)` inside the duplicated core, with hazard
`1/2`, is a balanced cyclic singleton certificate; player `0` duplicates one
active balance row and all dummies have strict positive singleton slack.
Therefore Banach's nonstationary singleton construction overlaps bare
uniform-payoff existence.

Proposition 13's honest novelty is the strict **stationary-certificate**
separation: the linear combination certificate gives an interior stationary
root while every playerwise Proposition 10 common-box matching, sure-exit set,
and instant owner fails.  It is not a new bare existence class, and no Lean
adapter seal is established here.

## Verdict

After replacing the false lower singleton bound `9999/10000` by
`9997/10000`, all exact inequalities and conclusions remain valid with ample
slack.  The normal-core reindexing/scaling, conditional singleton maximum,
`C^(-1)` norm, transformed rational margin, global playerwise exclusion,
sure-exit recurrence, and named-source scope all survive falsification.

This review does not cover Propositions 14--16 or authorize export.
