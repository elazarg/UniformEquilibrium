# Independent review of the retained two-coordinate partition

Reviewer: PASSIVE_AXIS_REVIEW. Ordinary mathematics and exact computation;
no Lean commands or tracked edits.

Reviewed artifact:
`math/notes/CODEX_COORDINATOR__COMPLETE_JOINING_EXCESS_AXIS.md`.
Review scope: Section6 only. Whole-file SHA256:
`0ebf080d5b5c1e8e03f8f5df06c4619514e609120002ee4dbb23b36fc7d622bc`.

## Verdict

PASS. No unresolved mathematical objection to Section6. I read the final
retained bytes and verified that Section6.3 expressly retains the proper-date
and positive-solo hypothesis required for its necessary polynomial. This
review covers the final Section6 rather than only its earlier scratch drafts.

## Complete t-axis half-plane

I inspected the literal table and five-date certificate in Section6 of
`math/exports/CORE_FREE_JOINT_RETURN_UNIFORM_EQUILIBRIUM.md`. Changing R affects
none of that profile's expectations or complete Bellman comparisons; changing
t affects exactly the quiet3 joint Quit offer, by x*b*(t-t0). Direct enumeration
confirms its zero t0=28599/29. Thus the unchanged K>=1 certificate proves the
whole t<=t0 region, including equality, with arbitrary R and p.

For t>=t0 I independently reconstructed both mixed-player indifferences,
player2's full-cap comparison, and quiet1's comparison from literal coalitions.
Exact symbolic simplification gives precisely (6.1) and (6.2), with the printed
positive denominators. The numerator of (6.1) vanishes at (Rstar,t0); both
monotonicity arguments are valid. I checked the exact Rstar fraction and the
282749/2 lower-corner value for (6.2), together with its positive derivatives.
This proves the entire closed quadrant with K>=4, including its weak boundary.
The sharper fixed-t slice and all its fractions agree with my independent
four-coalition calculation; K_min(zmax)<3 and the R=-6 threshold are exact.

The punishment is an actual two-date profile. A deviating player2 faces
Continue=-10 and Quit=-100 on the second date, so its full native response cap
is exactly -10. Every other deviator faces certain player2 absorption at the
first date. Thus all comparisons price complete behavioral replacements;
they do not substitute prescribed continuation payoffs for response caps.
Every unilateral deviation absorbs by date2. This justifies arbitrary original
own-level shifts and the original fixed-target uniform-payoff conclusion.
The unused p coordinate is absent from all consumed comparisons.

## Automatic left tail

I independently reconstructed the three-owner quadratic and solved it for R.
The result is exactly (6.3), whose coefficient of R is nonzero throughout
0<lambda<=3/500. Its denominator has the stated strict sign; its limit at zero
is minus infinity; and exact endpoint substitution gives the printed Rleft.
The intermediate value argument needs no monotonicity. The constant term of
the return polynomial is nonzero independently of R.

The row2 formula for tau gives U0 exactly equal to C+lambda*a0 after
substitution of R(lambda). I evaluated P1 as its literal seven-coalition sum
and reproduced every printed rational bound using exactly the100 intervals
and arithmetic rules specified in the retained text. In particular the
certified minima exceed .0084 for Y0, .1434 for Y1, .0212 for Y2-3a,
.279 for U0, .0648 for U2, .3089 for X1, .2328 for X2, and .0607 for
U2-3j/100. The physical/prefix bounds, j>0 and X0<0 also hold uniformly.
The quiet1 positive-term estimate is valid and proves K>=2 sufficient.
All inputs to the frozen finite wash/return producer are therefore supplied.
The conclusion is a finite-period equilibrium; no five-date bound is claimed.

## The R=-25 test and scope

Direct substitution of R=-25 into the exact return polynomial gives the
printed all-negative-coefficient polynomial up to a positive rational factor.
Under the proper-date and positive-solo hypothesis specified above, row3
indifference forces both endpoint values zero, fixes b,x, and makes this
polynomial necessary. It has no positive root.

I inspected and reran the exact census with the literal R=-25,t=987 table:
all80 nonzero stationary patterns close in866 nodes and all65 sure-first
patterns in197 nodes. Its coefficient dictionaries, actual lower-cap vector
(-25,-8,-10,-12), and origin constants are recomputed. The Bernstein rules,
K relaxation, inverse combinations and origin exclusions match the cited
frozen algorithm. The run leaves no unresolved box. This excludes those
entire selection sets at p=0,K>=1000,own levels1, including actual punishment
tails in the sure-first comparison. It does not imply an all-behavior gap.

The exact source declarations named at the end of Section6 were inspected
in place. Their full-cap and fixed-target scopes match the proofs. Section6
states its limited producer coverage honestly, retains no scratch dependency,
and adds no Lean-checked claim. The table's two half-plane/tail constructions
are rigorous; the intermediate R=-25 table remains a concrete problem for a
different nonstationary schedule.
