# A strict-blocker cyclic contact point admits a finite joint improvement

Author: CODEX_NOETHER_SUPPORT.

Status: exact bounded calibration, not independently reviewed or Lean-checked.
This is NOT an entire-one-row-family obstruction, a new solved class, or a
general consumer of the blocker conditions. The search for another trap
stops at the literal improving profile below.

## 1. Complete table and contact point

Players are 0,1,2,3, with J={1,2,3} cyclically ordered 1→2→3→1.
Never pays zero. For every nonempty coalition S set

    r₀(S)=1 if 0∈S; 0 if S={1}; 2 otherwise.

For i∈J use these disjoint cases:

    r_i({i})=−3;
    r_i(S)=1 if i∈S and 0∈S;
    r_i(S)=0 if i∈S, 0∉S, |S|≥2;
    r₁({0})=−4;
    r_i(S)=−1 if i∉S and 0∈S, except the preceding case;
    r_i({succ(i)})=−4,     r_i({pred(i)})=8;
    r_i(S)=1 if S=J\{i}.

These cases specify all entries. Relative to TARSKI's
[whole-family example](CODEX_TARSKI_PREMIUM__MIXED_SURE_CORE_GLOBAL_MAXIMUM_CONSUMPTION_TEST.md),
only cross-singleton entries changed. Uniform scaling by 1/8 puts the
table in [−1,1], preserving all strict comparisons and scaling every
regret and rate bound equally. At the silent-row profile with
row1 hazards q=(1/4,1,1,1), the exact values remain

    U=(7/4,1/4,1/4,1/4),    B=(2,1/2,1/2,1/2),
    d=(1/4,1/4,1/4,1/4),    κ=B−s=(1,7/2,7/2,7/2).

The eleven pure nonsingleton regrets have minimum Γ=1, and
(1/4)Σ_i1/κ_i=13/28<1. Use the four Never testers with weights
(3/4,1/12,1/12,1/12). Their gains are all 1/4 and their singleton
pressure is zero. For a changed owner, the derivatives of their weighted
gain are exactly

| Changed owner | Quit0 | Quit1 | Any finite date ≥2 or Never |
| --- | ---: | ---: | ---: |
| 0 | 1/2 | 0 | 0 |
| i∈J | 1/24 | 0 | 5/48 |

For each late core column, the two changed cross-singleton values sum to
−4+8=4, just as the former 2+2. Their equal receiver weights preserve
that column. The exceptional {0} and pivot {1} values are not exposed in
those columns because other sure cores remain. Early changes give
θ_iκ_i−1/4; other-owner Never gains cancel their prescribed payoff.
Thus the same certificate controls every complete-law first-order chord.

## 2. Stronger raw checks, not just rowwise normality

The normalized singleton matrix M_ij=r_i({j})−s_i is

    [ 0 −1  1  1 ]
    [−1  0 −1 11 ]
    [ 2 11  0 −1 ]
    [ 2 −1 11  0 ].

Every row AND every column has a strict off-diagonal negative entry.
The recursive distinct-witness normal core is therefore full. All
principal determinants of size at least two are nonzero: in subset order
01,02,03,12,13,23,012,013,023,123,0123 they are

    −1, −2, −2, 11, 11, 11, −9, −21, 20, 1330, 67.

Consequently there is no homogeneous simplex LCP solution: a support of
size at least two would give a nonzero kernel vector for its principal
matrix, while a singleton support is blocked by its strict column entry.
No standard-Q claim is made.

For every owner k and every h∈(0,1], the solo/join recruiter inequality
has lower bound at least one. For k=0, receiver1 gives
(1−h)(−3)+h·1−(−4)=1+4h. For k∈J, receiver pred(k) gives
(1−h)(−3)+h·0−(−4)=1+3h. These checks retain the rate, the outsider's
own singleton, and the joining reward; they are stronger than a bare
rowwise nonpositive blocker.

## 3. Exact actual full-regret improvement

Retain a silent date0, use row1 hazards

    x=(386,477,188,287)/1024,

and then literal Never. Put D=1024⁴=1099511627776. Direct product
enumeration of the complete responses gives the following numerators
over the COMMON denominator D:

| i | U_i | Quit0 | Quit1 | Any finite date ≥2 | Never |
| --- | ---: | ---: | ---: | ---: | ---: |
| 0 | 979506053120 | 1099511627776 | 1099511627776 | 1252013584384 | 906900799488 |
| 1 | −485844769480 | −3298534883328 | −793114943488 | −1425475477504 | −217896189952 |
| 2 | 830785275904 | −3298534883328 | −375662295040 | 311965028352 | 1102091667456 |
| 3 | −754357299200 | −3298534883328 | −481798709248 | −1756759179264 | −860496125952 |

For reproduction, if π_−i(S) is the opponent row product probability,
write Q_i=Σ_Sπ_−i(S)r_i(S∪{i}), C_i=Σ_(S≠∅)π_−i(S)r_i(S), and
D_i=π_−i(∅). The columns are U_i=x_iQ_i+(1−x_i)C_i, s_i, Q_i,
C_i+D_i s_i, and C_i. This proves they include every behavioral response,
including the signed-singleton late/Never distinction.

The complete debt numerators are therefore

    (272507531264,267948579528,271306391552,272558589952).

Each is less than D/4=274877906944. The actual improvement is at least
2319316992/D>0. This four-law change succeeds although the contact point
has all the fields checked above. It neither proves that those fields
always orient an improvement nor supplies a counterexample to that claim.

The exact distinct-witness definition in
`UniformEquilibrium/Quitting/Classification/LCP/NormalCore.lean` was read.
The calculation uses the full response formula in TARSKI's note, not a
finite-menu-only regret. The next priority is his genuine global comparison
back through the membership stretch; no further fixture variants or
whole-cube lower-bound proof are pursued here.
