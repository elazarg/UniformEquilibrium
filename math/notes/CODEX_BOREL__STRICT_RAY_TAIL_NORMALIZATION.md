# Strict maximal-prefix rays: tail-normalized cap flow

Author: `CODEX_BOREL`

## Status

The tail-normalization calculation below is proved in ordinary mathematics.
It rules out one tempting shortcut: the finite-hazard ray does not by itself
produce either the homogeneous singleton LCP or the projective-Q-bar
contradiction suggested by a one-step normalization.  The exact limiting
object contains two different hazard distributions (the present root and the
whole remaining tail) and a collision matrix term.

No terminal approximation, admissible return, renewable descent, or positive
gap table is produced.  This is therefore an internal boundary note, not an
export candidate under the breakthrough-only question.

There is now one further ordinary-mathematics advance.  Subject to the
standard equilibrium-index theorem for finite normal-form games, a genuinely
shrinking **maximal** exact-root ray cannot have a two-player binding set at
all.  This includes roots supported on both binding players and the degenerate
one-clock segment.  Thus a **proper** binding face in the strict Fin4 ray must
have cardinality `3`.  A full binding set `A = Fin 4` remains possible in the
ballistic or partial-current-support regimes; the earlier tail-normal theorem
excludes it only in the diffuse/full-current-support regime.  The proof is
given in Section 0 below.  It has not been checked in Lean; the project
presently has no finite-game equilibrium-index library.

An independent mathematical audit by `CODEX_NOETHER` validated this exclusion
conditional on that component-index theorem and caught a localization wording
issue: maximality bounds every equilibrium's absorption, and absorption in
turn bounds every marginal hazard.  The proof below now states that direction
explicitly.

The older regression in "Delta: exact nonalignment regression" remains useful
only as a regression against arguments that ignore maximality.  Exhaustive
support enumeration found many absorption-one equilibria for its stated
completion, so its displayed shrinking root is not maximal.  It does not
refute the cardinal-two exclusion below.

## Question

In the strict arm of
`questions/FIN4_RENEWABLE_ORIENTATION_OR_COUNTEREXAMPLE.md`, the canonical
maximal exact-prefix ray has finite total absorption and converges to a cap at
which all Continue is the unique exact root.  Can normalization by the
remaining absorption budget force either the checked homogeneous singleton
LCP contradiction or the hard residual's non-projective-Q-bar contradiction?

## Sources inspected

The bounded source set was:

- `QuittingMaximalCapSemanticPrefixRayStall` and its summability declarations
  in `Research/Quitting/MaximalCapSemanticPrefixReturn.lean`;
- `quittingMaximalCapSemanticPrefixOrbit_succ`, exact-root maximality, and
  coordinate debt scaling in
  `Research/Quitting/MaximalCapSemanticPrefixOrbit.lean`;
- `normalizedSoloMatrix_eq_soloReward_sub` in
  `UniformEquilibrium/Quitting/Classification/PreemptionGateDictionary.lean`;
- `ResidualHardClass` and the projective-Q-bar definition in
  `UniformEquilibrium/Quitting/Classification/LCP/Gate.lean` and
  `MatrixClasses.lean`; and
- the exact prefix formulas and remote-bubble normal form in
  `notes/CODEX_POINCARE__PREMARK_BUBBLE_CAP_HOLONOMY.md`; and
- the finite-game equilibrium-correspondence topology of Kohlberg--Mertens,
  *On the strategic stability of equilibria*, Econometrica 54 (1986), as
  recalled in Section 5 of Simon (2007).  The project transcription is
  `Literature/Simon2007.lean`, declaration `KohlbergMertensStatement`; it is a
  literature statement marked `sorry`, not a checked project theorem.  The
  precise corollary used below is the standard component-index sum theorem.

## 0. Maximality excludes a two-player binding face

### Finite-game index input

We use the standard equilibrium-index theorem for a finite normal-form game:
the indices of all Nash-equilibrium components sum to `+1`.  A strict pure
equilibrium has index `+1`; the completely mixed equilibrium of a strict
two-action coordination game has index `-1`; and component index is invariant
under a sufficiently small payoff perturbation on an isolating neighbourhood.
Equivalently, these facts follow from the proper homotopy of the finite-game
equilibrium correspondence in the Kohlberg--Mertens structure theorem.  This
is an ordinary finite-game theorem, not a Lean declaration used elsewhere in
the note.

The normalization is the usual one: the index of an isolated equilibrium
component is the local Brouwer degree of a Nash best-response displacement map
on an isolating neighbourhood, normalized so that a strict pure equilibrium
has degree `+1`.  With this convention the global degree, hence the sum over
all components, is `+1`.  In a two-action coordination game the derivative at
the interior mixed equilibrium has two positive off-diagonal response slopes
and negative determinant, so its local degree is `-1`.  For a nonisolated
component its index is the sum of the indices of the equilibria produced by
any sufficiently small regular perturbation inside the same isolating
neighbourhood.  These are exactly the three index facts used below; no
stability refinement is invoked.

### Proposition (no maximal shrinking ray on a two-player binding face)

Retain the hypotheses of the tail-normalized theorem and suppose the limiting
binding set is

\[
 A=\{i,j\}.
\]

Assume `q_k` is, as in the canonical ray, a maximum-absorption exact Nash root
against `b_k`, and that its absorption is positive and tends to zero.  Then
these hypotheses are inconsistent.

#### Uniform localization

For every outsider `ell notin A`,

\[
 \bar b_\ell>s_\ell.
\]

The endpoint differences depend continuously on the product root and
`b_k -> bar b`.  Hence there are a fixed neighbourhood `U` of all Continue
and a cutoff `K` such that every outsider strictly prefers Continue at every
root in `U` for `k >= K`.  Shrink `U`, if necessary, so that every root in
`U` has absorption below `1/2`.

For large `k`, `q_k` belongs to `U`.  Maximality now has a much stronger
consequence than local optimality.  For every Nash root `x` of the binary root
game against `b_k`,

\[
 \operatorname{Abs}(x)\le \operatorname{Abs}(q_k)\longrightarrow0,
 \qquad
 \max_h x_h\le \operatorname{Abs}(x).
\]

Hence, for any prescribed fixed neighbourhood of all Continue, the *entire*
Nash set lies in that neighbourhood for all sufficiently large `k`; in
particular it lies in `U`.  Thus the complete Nash set is the Nash set of the
two-player restriction to `A`, inside `U`.

Put

\[
 \delta_{k,h}=b_{k,h}-s_h\ge0\qquad(h\in A).
\]

When only `i,j` may Quit, the exact Quit-minus-Continue differences are

\[
 g_i(x_j)=-(1-x_j)\delta_{k,i}+x_jJ_{ij},
 \qquad
 g_j(x_i)=-(1-x_i)\delta_{k,j}+x_iJ_{ji}.
 \tag{A1}
\]

### Case 1: both binding players have positive hazard

Exact mixing in (A1) gives

\[
 (1-x_j)\delta_{k,i}=x_jJ_{ij},\qquad
 (1-x_i)\delta_{k,j}=x_iJ_{ji}.
 \tag{A2}
\]

Hence both collision increments are nonnegative.  Neither can vanish.  For
example, if `J_ij=0`, then `delta_(k,i)=0`; increasing `j`'s own hazard a
little preserves `i`'s equality, does not change `j`'s own endpoint
comparison, and preserves every outsider's strict Continue inequality.  This
would be another exact root with larger absorption, contradicting maximality.
Thus

\[
 J_{ij}>0,\qquad J_{ji}>0,
 \tag{A3}
\]

and both `delta` coordinates are positive.  All Continue is consequently a
strict equilibrium of the local two-player game, of index `+1`.  Equations
(A1)--(A3) give exactly one other equilibrium in `U`, the completely mixed
coordination equilibrium `q_k`; it is regular and has index `-1`.  The local
Nash set therefore has total index zero.

But maximality put the *entire* Nash set inside `U`, whereas every finite game
has total equilibrium index `+1`.  Contradiction.

### Case 2: exactly one binding player has positive hazard

Say `q_k` is a solo root at `i`.  Exact interiority pins

\[
 \delta_{k,i}=0.
\]

Player `i` is indifferent for every value of its own hazard.  Maximality
therefore increases that hazard until the other binding player `j` reaches
indifference.  Outsiders remain uniformly strict in `U`.  Thus, writing the
maximal hazard as `x_k`,

\[
 J_{ji}>0,
 \qquad
 (1-x_k)\delta_{k,j}=x_kJ_{ji},
 \tag{A4}
\]

and every solo root with owner hazard in `[0,x_k]` is exact.

The reverse collision increment is also strictly positive.  At the limiting
cap both `i` and `j` are pinned to their singleton rewards.  If `J_ij<0`, then
a sufficiently small solo root at `j` is exact: `j` is indifferent, `i`
strictly Continues, and the two outsiders still strictly Continue.  If
`J_ij=0`, the same is true with `i` indifferent.  Either case contradicts the
strict-ray hypothesis that all Continue is the unique exact root at the
limiting cap.  Hence

\[
 J_{ij}>0. \tag{A5}
\]

Inside `U`, the complete equilibrium set is now the closed segment

\[
 \{(x_i,x_j):0\le x_i\le x_k,\ x_j=0\}. \tag{A6}
\]

Its component index is zero.  To see this without assigning an index directly
to a continuum, raise `b_(k,i)` by an arbitrarily small positive amount while
keeping the isolating boundary of `U` free of equilibria.  The segment (A6)
then becomes precisely two equilibria in `U`: strict all Continue, of index
`+1`, and the regular mixed coordination equilibrium determined by (A1), of
index `-1`.  Invariance of component index under this perturbation gives
index zero for (A6).

Again maximality says that (A6) is the entire Nash set, contradicting total
index `+1`.

There is no third case: a non-all-Continue root supported in `A` has one or
two positive hazards.  This proves the proposition.

### Exact solo recurrence (useful audit of Case 2)

The one-clock case also has a closed cap recurrence.  Let

\[
 M_{ji}=r_j(\{i\})-s_j,
 \qquad K_{ji}=J_{ji}+M_{ji}=r_j(\{i,j\})-s_j.
\]

At the maximal threshold (A4), prefixing gives

\[
 \delta_{k+1,j}
 =(1-x_k)\delta_{k,j}+x_kM_{ji}
 =x_kK_{ji},
 \qquad
 x_k=\frac{\delta_{k,j}}{\delta_{k,j}+J_{ji}}.
 \tag{A7}
\]

A positive shrinking summable ray would therefore require

\[
 0<K_{ji}<J_{ji},\qquad M_{ji}<0. \tag{A8}
\]

This is the exact preemption/blocker geometry one sees before the equilibrium
index contradiction is imposed.  Equations (A7)--(A8) are consistent as a
local recurrence; what is impossible is that its endpoint segment exhausts
the Nash set while remaining the maximum-absorption root.

### Consequence and remaining boundary

On `Fin 4`, the strict-ray theorem had already excluded a singleton binding
set.  The proposition above excludes the two-player set.  Hence every
genuinely shrinking non-eventually-constant strict maximal ray has

\[
 \boxed{|A|=3\ \text{or}\ A=\operatorname{Fin}4.}
\]

More precisely, every **proper** binding set has cardinality three.  If
`A = Fin 4`, the exported tail-normal theorem rules out only the diffuse case
with full current-root support, by the full-core no-homogeneous theorem.
Ballistic full binding and diffuse partial-current-support full binding are not
excluded by the present argument.

This is not yet a consumer of the strict inert arm.  On a three-player binding
face the local equilibrium component can have index `+1`; algebraically this
is the projective-Q/degree alternative.  The hard residual supplies a
nonprojective principal of size two or three, but current source provenance
does not identify that selected principal with `A`.  The exact remaining
question is therefore whether the unique outsider to `A`, the forced remote
pair, and the hard-principal helper/cycle dispatch force such an alignment or
yield a terminal consumer directly.  Independently, the full-binding
ballistic/partial-support arm still requires the collision/projective-Q
consumer that the one-step normalization failed to provide.

## Delta: exact nonalignment regression

The finite hard principal cannot be identified with the limiting binding
support from the presently retained data.  The following rational reward
coordinates give a small algebraic regression.  This is not a positive-gap
table and does not assert that the displayed local ray is the atlas's global
maximal-selector ray.  It shows that the exact forced-pair signs, the
ballistic tail equations, and a separately checked residual-hard singleton
matrix are mutually consistent with different player sets.

There is a cleaner cardinal-three version which also respects the cap-side
signs `M Lambda <= 0` and `J lambda >= 0`.  Keep the paired singleton matrix
(R1), and put

\[
 A=\{0,2,3\},\qquad B=\{1,2\},\qquad C=\{0,3\}.
 \tag{R0}
\]

Here `A` is the strict-ray binding face, `B` is a separately displayed hard
principal, and `C` is the forced pair.  The principal `B` has

\[
 M_{1,2}=M_{2,1}=-1,
\]

with outside positive helpers `0` and `3`, since

\[
 M_{1,0}=M_{2,3}=3.
\]

Take

\[
 \lambda=\Lambda=(4/5,0,1/10,1/10),\qquad \rho=1/2.
 \tag{R0a}
\]

On `A`, the singleton flow is

\[
 (M\Lambda)_0=-1/5,\qquad
 (M\Lambda)_2=(M\Lambda)_3=-1/2.
 \tag{R0b}
\]

Choose the relevant collision increments as

\[
 J_{0,2}=J_{0,3}=2,
 \quad J_{2,0}=J_{3,0}=5/4,
 \quad J_{2,3}=J_{3,2}=0.
 \tag{R0c}
\]

Then

\[
 (J\lambda)_0=2/5,\qquad
 (J\lambda)_2=(J\lambda)_3=1,
\]

and therefore, coordinatewise on `A`,

\[
 M\Lambda+\rho J\lambda=0. \tag{R0d}
\]

These are literal rational reward coordinates.  With own singleton rewards
zero and `r_i({j})=M_ij`, define

\[
 r_i(\{i,j\})=r_i(\{j\})+J_{ij}
\]

for the displayed ordered pairs.  In particular, on the forced pair
`C={0,3}`,

\[
 J_{3,0}=5/4>0,\qquad J_{0,3}=2>0.
\]

Set the passive coordinate `r_1(C)=0` and the triple coordinate
`r_1({0,1,3})=1`; player `1` is then a strict outside payer at `C`.  Thus the
forced-pair orientation, a fixed outside payer, the sign-correct ballistic
normal form on `A`, and the exact card-two hard crossing on the *different*
principal `B` coexist in one rational table.

This regression asserts neither positive global minimum nor existence of a
maximal exact ray realizing the limiting data.  Its purpose is narrower and
exact: maximality or source provenance must do real work to identify the
binding face with the hard principal.  The finite `M/J` equations and the
forced-pair labels alone do not do so.

Use players `0,1,2,3` and the zero-diagonal singleton matrix

\[
 M=\begin{pmatrix}
 0&3&-1&-1\\
 3&0&-1&-1\\
 -1&-1&0&3\\
 -1&-1&3&0
 \end{pmatrix}.
 \tag{R1}
\]

Take every own singleton reward to be zero and put
`r_i({j})=M_{ij}`.  This is the checked paired-singleton matrix.  The existing
exact calculation in
`UniformEquilibrium/Quitting/Examples/BlockPair/`
`FourPlayerPairedSingletonResidualHard.lean` proves that it has full normal
core, is standard-Q, has no homogeneous simplex solution, and fails
projective Q-bar already on

\[
 B=\{0,2\}.
 \tag{R2}
\]

Now choose the different active/forced pair

\[
 A=C=\{0,3\}.
\]

Specify the only relevant nonsingleton coordinates by

\[
 r_0(C)=r_3(C)=1,qquad r_1(C)=0,qquad r_2(C)=1,
 \tag{R3}
\]

and

\[
 r_1(\{0,1,3\})=1.
 \tag{R4}
\]

All other nonsingleton coordinates may, for example, be set equal to `-2`.
For singleton owner `3` and forced outsider `0`, (R1)--(R3) give

\[
 J_{0,3}=r_0(\{0,3\})-r_0(\{3\})=2>0.
 \tag{R5}
\]

At the pure pair `C`, players `0` and `3` have zero toggle defect, player
`1` has the strict join defect

\[
 r_1(\{0,1,3\})-r_1(C)=1,
 \tag{R6}
\]

and player `2` has zero defect.  Thus `1` is an exact fixed payer of the
kind retained by the forced-pair packet, while the forced owner `0` is
strictly stable after joining.

There is also an explicit infinite exact-root cap orbit on the different
support `A`.  Start at the pure-pair cap

\[
 b_{0,0}=b_{0,3}=1,qquad b_{0,1}=b_{0,2}=1.
\]

Recursively put

\[
 x_k=\frac{b_k}{b_k+2},\qquad
 q_{k,0}=q_{k,3}=x_k,qquad q_{k,1}=q_{k,2}=0,
 \tag{R7}
\]

where `b_k=b_{k,0}=b_{k,3}`.  For either active player, Quit and Continue
against the other active hazard are

\[
 Q=x_k,qquad C=(1-x_k)b_k-x_k.
\]

Thus (R7) is exact for the active coordinates and its successor cap is

\[
 b_{k+1}=x_k=\frac{b_k}{b_k+2},qquad
 b_k=\frac1{2^{k+1}-1}.
 \tag{R8}
\]

For player `1`, if its current cap is `c_k`, the same root gives

\[
 Q_1=-4x_k+5x_k^2<0,qquad
 C_1=(1-x_k)^2c_k+2x_k(1-x_k)>0,
 \tag{R9}
\]

starting from `c_0=1`.  Player `2` has `Q_2=-4x_k+2x_k^2<0` and
`C_2=1`.  Hence both passive coordinates strictly Continue at every
displayed root.  This verifies an actual infinite exact cap-root orbit, not
only a formal first-order vector.

Its normalized hazards satisfy

\[
 \lambda_k=\Lambda=(1/2,0,0,1/2),qquad
 \rho_k=\frac{\varepsilon_k}{T_k}\longrightarrow\frac12.
\]

Since `M_{0,3}=M_{3,0}=-1` and
`J_{0,3}=J_{3,0}=2`, the ballistic equations are exactly

\[
 (M\Lambda)_i+\frac12(J\Lambda)_i=0
 \qquad(i\in A).
 \tag{R10}
\]

But `A={0,3}` and the checked bad principal `B={0,2}` are different.  In
particular their mere intersection at player `0` supplies no contradiction.
This also explains why the forced-pair payer need not help: here the payer is
`1`, outside the active support, and its positive defect is a triple-coalition
coordinate absent from both `M_A` and `J_A`.

The regression deliberately stops short of proving that `q_k` is the
maximum-absorption exact root among *all* four-player exact roots at `b_k`.
That is the one extra assertion which a maximality-based alignment theorem
would have to use.  Neither the current maximality field nor the hard
principal dispatch presently compares the selected root's support with a
nonprojective principal.  Consequently a valid continuation of this route
must prove that new comparison; it cannot infer it from the ballistic
equations or from forced-pair incidence.

## 1. Exact orbit notation

Let

\[
 z_k=(u_k,b_k),\qquad z_{k+1}=T_{q_k}z_k,
\]

where `q_k` is an exact product Nash root against the cap `b_k`.  Put

\[
 x_{k,i}=\Pr_{q_k}(i\text{ Quits}),\qquad
 \varepsilon_k=\sum_i x_{k,i},\qquad
 a_k=1-\prod_i(1-x_{k,i}).
\]

Whenever `epsilon_k > 0`, put

\[
 \lambda_{k,i}=x_{k,i}/\varepsilon_k.
\]

The vector `lambda_k` is in the simplex.  The elementary union bounds give

\[
 a_k\le\varepsilon_k\le |I|a_k.                 \tag{1}
\]

The strict ray has `sum a_k < infinity`, so it also has

\[
 \sum_k\varepsilon_k<\infty,
 \qquad \varepsilon_k\longrightarrow0.          \tag{2}
\]

If a maximal root is all Continue at one time, the autonomous orbit is
constant thereafter.  The analysis below concerns the other case, after
discarding finitely many indices, where `epsilon_k > 0` and every coordinate
of `q_k` is strictly below one.

## 2. The cap vector converges

Let `R` bound the absolute terminal rewards.  The cap coordinates are also
bounded by `R`.  Because `q_k` is exact Nash and `x_{k,i}<1`, the prescribed
root mixture used to form the successor cap has the Continue endpoint value:

\[
 b_{k+1,i}=C_i(q_{k,-i};b_{k,i}).                \tag{3}
\]

Indeed, if `x_{k,i}=0`, the prescribed action is Continue; if it is positive,
both endpoints are in support and are equal.

The event on which (3) differs from `b_{k,i}` is opponent absorption, so

\[
 |b_{k+1,i}-b_{k,i}|\le 2R a_k.                 \tag{4}
\]

Thus every cap coordinate has absolutely summable increments.  Write

\[
 b_k\longrightarrow \bar b.                     \tag{5}
\]

The limiting all-Continue Nash condition gives

\[
 \bar b_i\ge s_i:=r_i(\{i\}).                   \tag{6}
\]

Let

\[
 A:=\{i:\bar b_i=s_i\}.                         \tag{7}
\]

If `i` is outside `A`, then `s_i-bar b_i<0`.  Endpoint continuity and exact
Nash imply

\[
 x_{k,i}=0\quad\text{eventually}.                \tag{8}
\]

Thus all sufficiently late hazard is supported on the binding set `A`.

The binding set cannot have cardinality one on a genuinely infinite maximal
ray.  If `A={i}`, then eventually only `i` has positive hazard.  Exact mixing
forces `b_{k,i}=s_i`.  Every other player has the strict limiting Continue
margin `bar b_j-s_j>0`; by continuity, there is one fixed `eta>0` such that
the root in which only `i` Quits with probability `eta` is exact Nash against
every sufficiently late `b_k`.  This contradicts maximality because the
selected maximal absorption tends to zero.  Therefore

\[
 \boxed{|A|\ge2}                                      \tag{8a}
\]

unless the ray becomes exactly constant after finitely many steps.  On
`Fin 4`, every proper binding support consequently has size two or three.

## 3. The two first-order matrices

For distinct players define

\[
 M_{ij}=r_i(\{j\})-r_i(\{i\}),                  \tag{9}
\]

the checked normalized solo matrix, and

\[
 J_{ij}=r_i(\{i,j\})-r_i(\{j\}).                \tag{10}
\]

Put zero on both diagonals.  Uniformly on bounded caps, product expansion of
the Continue endpoint in (3) gives, for `i in A`,

\[
 \frac{b_{k+1,i}-b_{k,i}}{\varepsilon_k}
   =(M\lambda_k)_i+O(\varepsilon_k).             \tag{11}
\]

The Quit-minus-Continue endpoint difference similarly gives

\[
 Q_i-C_i
 =s_i-b_{k,i}+\varepsilon_k(J\lambda_k)_i
   +O(\varepsilon_k^2).                          \tag{12}
\]

Consequently

\[
 w_{k,i}:=
 \frac{b_{k,i}-s_i}{\varepsilon_k}
 -(J\lambda_k)_i+O(\varepsilon_k)\ge0,
 \qquad
 \lambda_{k,i}w_{k,i}=0.                        \tag{13}
\]

The term `J` is the collision-membership matrix, not the solo matrix.  This
is the first place where a direct one-step invocation of `no_homogeneous`
fails.

## 4. Normalize by the whole remaining hazard

Define

\[
 T_k:=\sum_{h\ge k}\varepsilon_h,
 \qquad
 \rho_k:=\varepsilon_k/T_k,
\]

and the tail hazard barycenter

\[
 \Lambda_k:=\frac1{T_k}
   \sum_{h\ge k}\varepsilon_h\lambda_h.         \tag{14}
\]

It is a simplex vector supported on `A`.  Summing (11) and using

\[
 \frac{\sum_{h\ge k}\varepsilon_h^2}{T_k}
 \le \sup_{h\ge k}\varepsilon_h\longrightarrow0
\]

gives the exact tail-normalized cap flow

\[
 \boxed{
 \frac{\bar b_i-b_{k,i}}{T_k}
  =(M\Lambda_k)_i+o(1)
 }
 \qquad(i\in A).                                \tag{15}
\]

Substituting `b_k-s=-(bar b-b_k)` into (13), and multiplying by `rho_k`,
gives

\[
 \boxed{
 - (M\Lambda_k)_i
 -\rho_k(J\lambda_k)_i+o(1)\ge0,
 }
                                                            \tag{16}
\]

with equality asymptotically on every coordinate receiving positive mass
from `lambda_k`.

This is the actual limiting complementarity object.  It has:

1. the present-root direction `lambda_k`;
2. the remaining-tail average `Lambda_k`; and
3. the collision correction `rho_k J lambda_k`.

Replacing all three by one vector is an additional theorem, not a harmless
normalization.

## 5. Diffuse and ballistic tails

Take a subsequence on which

\[
 \lambda_k\to\lambda,
 \qquad \Lambda_k\to\Lambda,
 \qquad \rho_k\to\rho.
\]

### Diffuse case: `rho=0`

Equation (16) becomes

\[
 -(M\Lambda)_i\ge0,
 \qquad
 \lambda_i(M\Lambda)_i=0                       \tag{17}
\]

on `A`.  This is not, in general, a homogeneous singleton-LCP solution:
the nonnegative weight is `Lambda`, while complementarity is tested by the
possibly different vector `lambda`, and the residual has the opposite sign.

There is one useful genuine exclusion.  If the current-root limit has full
support on `A`, then (17) forces

\[
 (M\Lambda)_i=0\qquad(i\in A).                  \tag{18}
\]

Thus `Lambda` is a normalized kernel vector of the principal matrix on `A`.
If `A=I`, this contradicts the hard residual's checked
`no_homogeneous` field.  For a proper `A`, it only produces a homogeneous
solution of one principal submatrix, which is compatible with failure of
projective Q-bar elsewhere.

### Ballistic case: `rho>0`

The limiting relation is

\[
 -M\Lambda-\rho J\lambda\ge0,
 \qquad
 \lambda_i(M\Lambda+\rho J\lambda)_i=0.         \tag{19}
\]

Moreover the barycenters obey the exact renewal identity

\[
 \Lambda_k=\rho_k\lambda_k+(1-\rho_k)\Lambda_{k+1}.\tag{20}
\]

Even when consecutive subsequences converge, (19)--(20) are a discounted
collision holonomy, not a projective LCP for `M` with a freely prescribed
right-hand side.  The fact that the full solo matrix is not projective Q-bar
therefore does not contradict this object.

## 6. The all-Never jump does not acquire a sign

For the pure terminal coalition `C` at the remote end of the ray, put

\[
 h_i(C)=
 \max\{r_i(C\cup\{i\}),r_i(C\setminus\{i\})\}-r_i(C),
 \qquad H_C=\sum_i h_i(C).
\]

If `alpha>0` is limiting common survival, exact cap-prefix scaling gives

\[
 d_i(\bar z)=\alpha h_i(C),
 \qquad L=D(\bar z)=\alpha H_C.                  \tag{21}
\]

The literal all-Never profile has debt

\[
 D_N=\sum_i(s_i)_+.
\]

Hence the complete jump is simply

\[
 \boxed{D_N-L=\sum_i(s_i)_+-\alpha H_C.}        \tag{22}
\]

Neither (17) nor (19) controls this sign.  In particular, binding
`bar b_i=s_i` is not a sign condition on `s_i`, and coordinates outside `A`
are precisely those on which the all-Never cap can add an uncontrolled
positive part.

## 7. Exact remaining boundary

Tail normalization can consume two special cases:

1. a returned block whose cap seam is little-oh of its total hazard enters
   the existing periodic/returned-block compiler; and
2. a diffuse full-binding, full-support root direction contradicts the hard
   homogeneous screen by (18).

The general strict ray can avoid both through a proper binding support or a
ballistic collision holonomy.  To finish the strict arm, one still needs an
actual source theorem proving one of:

- the forced-pair provenance makes the binding/root support full;
- the proper-support or ballistic object enters the particular bad principal
  witnessing failure of projective Q-bar;
- a horizontal paid sibling cancels the vector cap flow in (15), producing a
  returned block; or
- the all-Never jump (22) is below the positive global minimum.

None of these implications follows from the presently exposed strict-ray
fields.  The important correction is that the hoped-for diffuse/ballistic
split does not automatically contradict the two hard matrix fields.

### Why the known three-player theorem does not immediately consume proper
support

When `A` is proper, late outer roots use only the two or three players in
`A`.  This does not by itself reduce the quitting game to those players.
Players outside `A` may still:

- Quit in the remote pure coalition `C`;
- carry positive coordinates of the transported debt
  `alpha h(C)`; and
- have best responses which pass through the active prefix and alter the
  remote coalition, or stop at a pre-mark date.

Replacing them by Never changes the bubble payoff and the unrestricted caps
seen by `A`.  Conversely, a uniform equilibrium of the active subgame need
not reproduce the fixed bubble law or the passive players' target payoffs.
The strict inequalities `bar b_i>s_i` only rule out an immediate solo Quit
near all Continue; they do not control collision or preemption deviations at
later active dates.  A cardinal-reduction consumer therefore needs a genuine
payoff/law alignment or punishment adapter, not just (8).
