# The residual singleton sign atlas and its strategy boundaries

Owner: CODEX_COORDINATOR. Ordinary mathematics, not Lean checked. Sections1–3
classify signed joint-return prerequisites. Section4 gives exactly21 realizable
full sign orbits under the listed necessary singleton restrictions. The linked
absorption-path theorem excludes diffuse Nash-approximation sequences on that
residual when at least one own singleton payoff is positive.
These classify known matrix restrictions and strategy architectures;
they do not prove UE on a new reward class. Higher-reward, physical-root,
prefix and continuation guards remain independent.

## 1. Exact conclusions

Use the generic residual hypotheses and ten pointed observer templates of
`CODEX_COORDINATOR__FIN4_RESIDUAL_PARTITION.md`, Sections 1–8. Thus every
column has a negative entry, Gamma is R0 of degree +1, det Gamma>0, its inverse
has a strictly positive column, there is a mutually negative reciprocal pair,
and no inverse-positive principal triple has a nonnegative outside inverse row.
The pointed form is H=[0,c;-r,B], with r=B1 and sum(c)=1.

A labeling has architecture A if

    beta=-Gamma02>0, f=Gamma20>0, k=Gamma03>0.

Architecture AG additionally requires g=-Gamma13>0, and AGH additionally
requires h=-Gamma23>0. Define AH by retaining h>0 and allowing g either sign.
No sign is imposed on e=Gamma32 or d=-Gamma30.

| Pointed observer template | A always | AG always | AGH always |
|---|---|---|---|
|1|yes|no|no|
|2|yes|no|no|
|3|no|no|no|
|4|yes|no|no|
|5|yes|yes|yes|
|6|yes|yes|no|
|7|yes|no|no|
|8|yes|yes|yes|
|9|yes|yes|no|
|10|yes|yes|no|

Here “always” quantifies over every numerical matrix in the indicated pointed
template satisfying the full residual restrictions, and allows every player
relabeling. Each “no” has an exact residual counterexample below.

More precisely, A and AH are equivalent on the residual class. They fail
exactly on the sign orbit consisting of two disjoint mutually positive pairs
and four mutually negative cross-pairs. In the printed template3 orientation,
this is precisely sign(r)=(-,+,+), sign(c)=(+,-,-). Thus allowing arbitrary g
repairs every other sign pattern while h>0 can be retained. Since the generic
stratum excludes g=0, only the two variants (g,h)=(+,+),(-,+) are needed.
The extra (-,+) variant is necessary, as the AG counterexamples demonstrate.

A small member of the exceptional sign orbit is

    Gamma=[0,3,-1,-1; 2,0,-1,-1; -1,-1,0,2; -1,-1,2,0].

It has det=4, inverse column0 equal to 1, and no opposite-sign reciprocal
pair. Consequently beta>0 and f>0 cannot hold together under any labeling.
This is only an obstruction to A: allowing other signs of beta or k can
produce legal joint/solo3 returns on particular higher-reward completions.

## 2. Finite proof and exact sharpness witnesses

The proof enumerates a conservative superset of possible sign data. For each
of the ten printed B sign words, assign signs to r and c. Reject only when:

- a same-sign B row forces the opposite row-sum sign;
- all r entries or all c entries are negative;
- H has a column with no negative entry or has no negative reciprocal pair;
- an eligible degree-test pair has both corresponding c entries positive;
- B is inverse-positive (template8) but every c entry is positive.

These are necessary consequences of the pointed form and residual conditions.
For the fourth test, both coefficients in D_ij are positive, so D_ij<0 forces
at least one of c_i,c_j to be negative. The last test follows from c B^-1
having a negative coordinate. No rejected sign assignment can be residual.
For every retained assignment test all 24 labelings directly.

The retained counts by template are (5,5,15,10,9,3,20,30,9,2); these count
formal sign assignments, not proven nonempty numerical cells. Zero failures
prove the universal entries in the table. Among all retained assignments,
A is equivalent to AH, and its sole failure is exactly the template3 sign
assignment displayed above. The following rational witnesses establish every
remaining negative entry. The six B coordinates are (12,13,21,23,31,32), and
H is reconstructed by r=B1 and H=[0,c;-r,B].

| Template | B coordinates | c | Failed architecture |
|---|---|---|---|
|1|(-1,-1,-1,-3,-1,4)|(-3,5,-1)|AG|
|2|(-1,-2,-2,-1,1,1)|(5,-3,-1)|AG|
|3|(-1,-1,-1,2,-1,2)|(3,-1,-1)|A|
|4|(-1,-1,-2,1,1,2)|(3,-1,-1)|AG|
|6|(-1,-1,1,-2,1,1)|(-1,3,-1)|AGH|
|7|(-2,1,-1,2,-1,3)|(3,1,-3)|AG|
|9|(-1,2,2,-1,1,1)|(-3,3,1)|AGH|
|10|(-1,2,3,1,1,1)|(-1,5,-3)|AGH|

Every witness has nonzero off-diagonal entries, nonzero principal determinants
of size at least two, and nonzero full inverse entries. Its determinant is
positive and inverse column0 is exactly 1. The exact verifier checks negative
columns, a negative pair, every eligible D_ij<0, and every passive-child test.
Principal nonsingularity and negative columns imply R0: a homogeneous support
of size at least two would give a principal kernel, and a singleton would
violate its negative column. The complete pointed degree formula then gives
degree +1. Thus the failures satisfy all the residual hypotheses, not merely
necessary sign approximations. Pivot0 is the least original strict pivot.

The exact standard-library checker is
[CODEX_PARTITION__FIN4_SINGLETON_CELLS_CHECK.py](../experiments/CODEX_PARTITION__FIN4_SINGLETON_CELLS_CHECK.py).
Its `check_joint_return_topology()` verifies the complete prerequisite census
and every rational sharpness witness above. Run the file with Python3; no
sampled or floating-point calculation enters the proof.

## 3. Scope, producer use, and previous obstructions

The positive-continuation direct-return proof can allow arbitrary g when its
literal prefix is legal and both quiet1 endpoint values are strictly positive:
all intermediate return annotations stay on their positive segment, and
subdivision makes every finite joining offer small enough. This explains the
role of the AH variant, but the topology theorem supplies neither positive
endpoints nor the required physical root. Any such producer must retain its
explicit raw guards. The finite-core construction with negative quiet1 values
may still use g>0 essentially; this census does not extend that construction.

The nearby complete-axis note already identifies a different template3 witness
with exactly one opposite-sign pair; it defeats the older two-opposite-pair
finite-core architecture but admits a signed-e direct return. The present
exception has no opposite-sign pair and survives every labeling of A itself.
The result is a full prerequisite classification, not a duplicate assertion
that the older architecture has one bad matrix. The residual partition's
one-pivot/no-child sign-orbit theorem is compatible with this classification;
its broader template7 also contains the multiple-pivot witness above.

Inspected sources: `CODEX_COORDINATOR__FIN4_RESIDUAL_PARTITION.md`, Sections
1–8; its exact checker `CODEX_PARTITION__FIN4_SINGLETON_CELLS_CHECK.py`;
`CODEX_COORDINATOR__COMPLETE_JOINING_EXCESS_AXIS.md`, Sections 3–4; and the
raw sign assumptions and comparison scope of the frozen
`CORE_FREE_JOINT_RETURN_UNIFORM_EQUILIBRIUM.md`.
No Lean check is claimed.

## 4. Exactly21 realizable full sign orbits

Let Gamma be a real4x4 zero-diagonal matrix. Require all off-diagonal entries
and all principal determinants of sizes2,3,4 nonzero. Impose:

1. Every column has a negative entry, Gamma is R0 and has complementarity degree+1.
2. det Gamma>0 and some inverse column is strictly positive.
3. Some reciprocal pair has both entries negative.
4. Every principal triple with nonnegative inverse has a negative coordinate
   in its outside inverse row.
5. Under no relabeling does Gamma satisfy the negative-chord Hamiltonian
   sign criterion: opposite-sign adjacent directed four-cycle, mutually
   negative opposite chord02, and at least one positive entry on chord13.

THEOREM. Up to simultaneous permutation of rows and columns, exactly21
strict off-diagonal sign patterns occur in this domain. They are the
canonical words in the table below. Every word has an integer matrix witness
with every full inverse entry nonzero as well. Only rows14,16,19 admit ANY
positive directed Hamiltonian four-cycle. In every other row the positive
entry digraph has no spanning directed cycle.

The word order is row-major off-diagonal
(01,02,03,10,12,13,20,21,23,30,31,32); canonical means lexicographically
least under all24 simultaneous permutations, with '-' before '+'. The
witness need not have that literal labeling: the word identifies its orbit.
For the displayed witness data form B from its six off-diagonal entries
(12,13,21,23,31,32), let r=B1, and take H=[0,c;-r,B]. Thus nine integers
specify every witness, and H1=e0 automatically.

|Row|Canonical sign word|B entries|c|Positive Hamiltonian cycle?|
|---:|---|---|---|---|
|1|`--+--+-+---+`|(-4,-6,-5,-9,-3,7)|(-2,-12,15)|no|
|2|`--+--+-+--+-`|(-6,-7,-1,-4,-1,6)|(-6,8,-1)|no|
|3|`--+--+-+--++`|(-4,-6,-5,-9,-3,7)|(-9,6,4)|no|
|4|`--+--+-+-+--`|(-8,-4,-4,5,-6,7)|(-1,9,-7)|no|
|5|`--+--+-+-+-+`|(-4,-6,-5,-9,-3,7)|(2,-7,6)|no|
|6|`--+--+++---+`|(-6,-1,-6,-9,8,6)|(-3,-9,13)|no|
|7|`--+--+++--+-`|(-6,-1,-6,-9,8,6)|(-5,10,-4)|no|
|8|`--+--+++--++`|(-6,-1,-6,-9,8,6)|(4,-10,7)|no|
|9|`--+-+--+-+--`|(-3,-1,-3,7,-1,4)|(11,-2,-8)|no|
|10|`--+-+--+-+-+`|(-2,1,-1,8,-1,9)|(8,-2,-5)|no|
|11|`--+-+--++-+-`|(-7,-6,-7,4,-2,4)|(-5,-2,8)|no|
|12|`--+-+--++-++`|(-4,-7,-5,9,-9,1)|(-12,11,2)|no|
|13|`--+-+--++++-`|(-3,2,-6,9,-2,1)|(10,-2,-7)|no|
|14|`--+-+-++-++-`|(-8,-7,-3,8,2,9)|(11,10,-20)|yes|
|15|`--+-+++----+`|(-9,-8,8,-2,5,1)|(-6,9,-2)|no|
|16|`--+-+++---++`|(-6,4,4,-1,-3,7)|(10,-11,2)|yes|
|17|`--+-+++--+-+`|(-3,2,-6,9,-2,1)|(-2,10,-7)|no|
|18|`--+-++++---+`|(-5,-5,5,-2,1,-6)|(-2,1,2)|no|
|19|`--+-++++--++`|(-8,6,8,5,5,9)|(-1,9,-7)|yes|
|20|`--+-++++-+--`|(-2,1,-1,8,-1,9)|(7,8,-14)|no|
|21|`--+-++++-+-+`|(-3,2,-6,9,-2,1)|(9,3,-11)|no|

These are sign orbits, not connected numerical cells. Within each orbit,
principal determinant and complementarity inequalities still restrict the
magnitudes. The existing pointed polygon tests give those conditions for
each choice of inverse-positive pivot. This theorem does not assert that
every matrix with one of these sign patterns satisfies the domain.

### Exhaustive upper classification

Choose a strictly positive inverse column v=Gamma^{-1}e_p and put
H=Gamma diag(v). After moving p to0,

    H=[0,c;-r,B], r=B1, sum c=1, det H=det B>0.

This is a positive column scaling for matrix classification, not a claimed
payoff-game invariance. Permuting the three observers puts the six signs of
B into one of the existing ten observer templates. These and their exact
polygon conditions were proved in
CODEX_COORDINATOR__FIN4_RESIDUAL_PARTITION.md, Sections2–6.

The elementary sign consequences used below are: row-sum signs must agree
with two equal row signs; r and c each have a positive coordinate; negative
columns and a negative reciprocal pair must exist; for an eligible pair

    B_ij B_ji>0, r_i/B_ij>0, r_j/B_ji>0,
    D_ij=c_i r_j/B_ji+c_j r_i/B_ij<0;

in particular c_i,c_j cannot both be positive. If B has positive inverse,
c cannot be entirely positive. These necessary tests give108 pointed sign
assignments and28 unpointed sign orbits. The negative-chord test removes5
pointed assignments in2 full orbits, leaving26 candidate orbits.

Five of those26 are numerically impossible. Their canonical words are

    --+--+-+-++-, --+--+++-++-, --+-+-+--++-,
    --+-+-+-+++-, --+-+++--++-.

The following elementary contradictions remove ALL of their pointed
representatives; the finite checker enumerates that coverage.

For template3 write B=[0,-a,-b;-c,0,d;-e,f,0], all letters positive.
For r=(-,-,+), outside row C=(-u,1+u+w,-w), u,w>0, the eligible pair12 has

    D12=-u(1-d/c)+(1+u+w)(1+b/a)>0.

This contradicts D12<0; d<c is supplied by r2<0. The case r=(-,+,-),
C=(-,-,+) is obtained by swapping observers2,3.

For template7 write B=[0,-a,b;-c,0,d;-e,f,0], det B=ade-bcf.
If r=(+,-,+), then b>a,d<c,f>e and bcf>ade, contradicting det B>0,
for every outside row. If r=(-,-,+) and C=(-u,1+u+w,-w), determinant
positivity gives b/a<de/(cf)<d/c. Then

    D12=-u(1-d/c)+(1+u+w)(1-b/a)>0,

again a contradiction.

For template4 write B=[0,-a,-b;-c,0,d;e,f,0]. If r=(-,+,+) and
C=(-u,1+u+w,-w), the eligible positive pair23 has

    D23=(1+u+w)(1+e/f)-w(1-c/d)>0.

If r=(-,-,+) with the same C signs, the template3 D12 argument applies.

For template8 write B=[0,-a,b;c,0,-d;-e,f,0], det B=bcf-ade>0.
Suppose r=(-,-,+), C=(1+v+w,-v,-w), v,w>0. Thus b<a,c<d,e<f.
The adjugate rows are

    (df,bf,ad), (de,be,bc), (cf,ae,ac).

The first row strictly dominates each other row coordinatewise: bf>ae
uses bcf>ade and c<d; the other comparisons follow directly from the
three row-sum signs. Consequently C adj(B)>0 and C B^{-1}>0, contradicting
the passive-child failure. Cyclic observer permutations give the other
two forbidden template8 assignments.

The five missing full orbits have only these pointed representations:

|Canonical word|Template; signs(r); signs(C)|
|---|---|
|--+--+-+-++-|3;--+;-+- / 3;-+-;--+ / 7;+-+;-+-|
|--+--+++-++-|7;--+;-+-|
|--+-+-+--++-|4;-++;-+- / 7;+-+;+--|
|--+-+-+-+++-|8;--+;+-- / 8;-+-;--+ / 8;+--;-+-|
|--+-+++--++-|4;--+;-+- / 7;+-+;++-|

Every remaining full orbit appears in the21-witness table, completing both
upper and lower directions. The witness verification checks all principal
nonsingularities and every inverse-positive child. Negative columns and
principal nonsingularity imply R0. The full complementarity support census
at offset-e0 has exactly the full root x=1, with local index sign(det H)=+1;
hence the complementarity degree is+1. No sampled infeasibility assertion
is used in the upper proof.

### Source correspondence and strategic use

The original no-UE sources inspected are
standardQMatrixSide_of_not_exists_uniformEquilibriumPayoff
(UniformEquilibrium/Quitting/Classification/LCP/CounterexampleNecessary.lean)
and the nonnegative-inverse consumer
exists_uniformEquilibriumPayoff_of_nonnegative_singletonInverse
(UniformEquilibrium/Quitting/Classification/LCP/NonnegativeInverseCriterion.lean).
The negative-chord whole-completion theorem is the reviewed packet
../exports/NEGATIVE_CHORD_HAMILTONIAN_UNIFORM_EQUILIBRIUM.md.
The other five matrix restrictions and pointed normal form are the existing
coordinator partition, with its exact checker
../experiments/CODEX_PARTITION__FIN4_SINGLETON_CELLS_CHECK.py.

The atlas gives a complete finite sign target for further singleton-only
producers. In particular a proof covering positive-Hamiltonian matrices
would remove exactly THREE real admitted sign orbits (rows14,16,19), not an
unquantified graph class. No such general theorem is assumed here. Outside
those three orbits, a different mechanism is required. The44 higher-coalition
coordinates remain arbitrary data to be handled after the singleton screens.

## 5. Consequence for equilibrium construction

The [complete absorption-path obstruction](CODEX_COORDINATOR__DIFFUSE_APPROXIMATION_ATOM_OBSTRUCTION.md)
covers every matrix satisfying these residual restrictions. Its graph proof
is independent of the finite enumeration. In particular, no finite balanced
singleton cycle exists at any period on these matrices. More strongly,
for bounded completions and at least one own level bounded positively away
from zero, every sufficiently accurate actual terminal Nash approximation
must have a first-absorption date of uniformly positive probability.
The obstruction allows arbitrary nonperiodic behavior and infinite switching;
it supplies neither such an approximation nor a positive gap against all
behavior. The three positive-Hamiltonian orbits therefore cannot be closed
by merely extending a pure-singleton balanced cycle.

The exact checker above also runs `check_unpointed_residual_atlas()`: it
verifies all21 witnesses, the26-to21 exclusion list, the full complementarity
support census, and the three positive-Hamiltonian orbits. No Lean command
was run. Further positive producers must still handle the collision rewards.
