# Audit of `FACE_ENLARGE.md`

Reviewer: Codex Faraday

## Verdict

The proposed `FaceTangent` enlargement does not enlarge projective
`Q̄`: the zero-diagonal tightening argument is correct, and the stronger
matrix-class identity

\[
  \operatorname{Completely}S_0(M)
  \iff \operatorname{IsProjectiveQBarMatrix}(M)
\]

is correct under the repository's exact projective-LCP convention.  The
strict minimax blocker, full-support outside-helper inequalities, conditional
collision tax, small-h leakage estimates, and terminal-law scalar identity
are also correct after the boundary repairs stated below.

This does **not** yet enlarge the solved quitting-game class or construct the
periodic chronology required by `COMP.md`.  It gives a useful dual normal form
for every failed principal face and a strong verifier for any proposed
small-h realization.  The missing step remains source-matched production of
the requisite chronology.

No packet in the draft currently passes `exports/README.md`: the
matrix-class equality removes one proposed enlargement but does not close a
named conjecture-facing arm, while the blocker package has no arbitrary-data
chronology producer.  The elementary statements and the adapter below are
good `MathUE`/`Research` formalization candidates.

## Claims audited

I checked the following claims independently.

1. Zero-diagonal `S_0` tightening.
2. Complete `S_0`, semimonotone `E_0`, and projective `Q̄` equivalence.
3. The strict minimax blocker.
4. The full-support packet's outside-helper inequalities.
5. The increasing-face itinerary.
6. The conditional collision tax and small-h leakage bounds.
7. The terminal-law scalar identity.
8. The relation of these statements to the first-order periodic realization
   still missing in `COMP.md`.

## Repository declarations inspected

* `IsProjectiveQMatrix`,
  `isProjectiveQMatrix_iff_standard_or_homogeneous`, and
  `IsProjectiveQBarMatrix` in
  `UniformEquilibrium/Quitting/Classification/LCP/MatrixClasses.lean`.
* `PrincipalQDirection` and `exists_principalQDirection` in
  `UniformEquilibrium/Quitting/AbsorptionPath/PrincipalQDirection.lean`.
* `NonnegativeBoundaryDirection` and
  `exists_nonnegativeBoundaryDirection` in
  `UniformEquilibrium/Quitting/AbsorptionPath/PrincipalQBoundaryDirection.lean`.
* `FinFourQuantitativeFullSupportHardResidual` and its arbitrary-table
  producer in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`.
* `QuittingNormalizedSingletonSourcePacket` in
  `UniformEquilibrium/Quitting/Classification/ThreePlayer/AnalyticPacket.lean`.
* `TightFaceSeparatorData`, `local_bellmanDrift_pairing_le`,
  `path_pairing_lowerBound`, and `path_halfMargin_lowerBound` in
  `UniformEquilibrium/Quitting/Chronology/TightFaceCollisionEscape.lean`.
* The actual path adapters in
  `UniformEquilibrium/Diagnostics/Quitting/Chronology/TightFaceCollisionEscapeAdapters.lean`.
* The already checked card-two/card-three helper dispatch in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportHardPrincipalDispatch.lean`.

## 1. Zero-diagonal tightening is correct

Let `A` have zero diagonal and suppose `x >= 0`, `x != 0`, and `Ax >= 0`.
Choose such an `x` with support of minimum cardinality and normalize only at
the end.

If some coordinate of `Ax` is zero, the conclusion already holds.  Otherwise
`Ax > 0` coordinatewise.  Choose `j` in the support and replace `x` by
`x-t e_j`.  Rows with `A_ij <= 0` do not decrease.  Rows with `A_ij > 0`
remain feasible until `t = (Ax)_i/A_ij`; row `j` imposes no constraint because
`A_jj=0`.  Increase `t` until either a residual first reaches zero or `x_j`
reaches zero.  In the second case the new vector is still nonzero: support one
would already make `(Ax)_j=0`, contrary to `Ax>0`.  If no residual is tight,
support has decreased, contradicting minimality.

Thus the draft's equivalence (1) is valid.  Notice that the tight residual
need not correspond to a positive coordinate of the direction.  This is
nevertheless exactly what the repository's `PrincipalQDirection` asks for;
it is not a homogeneous complementary LCP solution.

## 2. Matrix-class identity and source audit

Use the standard definitions

\[
S_0(A)\iff \exists x\ge0,\ x\ne0,\ Ax\ge0
\]

and

\[
E_0(A)\iff
  \forall,0\ne x\ge0\ \exists i:\ x_i>0\text{ and }(Ax)_i\ge0.
\]

The classical equivalence is

\[
E_0(A)\iff
  \text{every nonempty principal submatrix of }A\text{ is }S_0.
\]

This is Theorem 3.1(4) of M. J. Tsatsomeros and M. Wendler,
*Semimonotone matrices*, Linear Algebra and its Applications 578 (2019),
207--224, DOI `10.1016/j.laa.2019.05.009`.  Their terminology says that `A`
and all proper principal submatrices are `S_0`, which is the same statement.

For the LCP step, Pang's theorem is

\[
 E_0\cap R_0\subseteq Q.
\]

The original source is J.-S. Pang, *On Q-matrices*, Mathematical Programming
17 (1979), 243--247, DOI `10.1007/BF01588247`.  The exact attribution and
statement are independently confirmed in the publisher abstract of
T. Parthasarathy, G. Ravindran, and S. Kumar,
*On Semimonotone Matrices, R0-Matrices and Q-Matrices*, JOTA 195 (2022),
131--147, DOI `10.1007/s10957-022-02066-3`.

The convention translation is exact:

* If `A` is projective `Q`, solve its projective LCP at `q=-1`.  If `c` is
  cemetery mass and `z` singleton mass, then `Az-c 1 >= 0`.  The total-mass
  equation and the residual inequality rule out `z=0`; hence `A` is `S_0`.
* Conversely, suppose every principal submatrix `A` is `S_0`.  Then it is
  `E_0`.  If it is `R_0`, Pang gives standard `Q`.  If it is not `R_0`, a
  nonzero solution of `LCP(A,0)` normalizes to the repository's
  `HasHomogeneousSimplexSolution`.  The checked theorem
  `isProjectiveQMatrix_iff_standard_or_homogeneous` finishes the step.

Applying this to every nonempty principal submatrix proves equation (2) for
all finite real matrices, without a diagonal hypothesis.  Combining it with
the tightening lemma proves the claimed zero-diagonal `FaceTangent`
equivalence, provided `FaceTangent` is defined exactly as existence of a
`PrincipalQDirection` on every nonempty face.

The 2019 DOI alone is not an adequate citation for the Pang step; the final
note should cite the two results separately.

## 3. Strict blocker and rationality

For a nonempty face `P`, finite zero-sum minimax gives

\[
 \max_{\lambda\in\Delta(P)}\min_i(M_P\lambda)_i
 =\min_{y\in\Delta(P)}\max_j(y^TM_P)_j.
\]

Compactness gives optimizers.  Therefore failure of `S_0` is equivalent to a
strict blocker

\[
 y\in\Delta(P),\qquad M_P^Ty\le-\eta\mathbf1,qquad \eta>0.
\]

The two alternatives are exclusive because
`y^T M_P lambda` cannot be simultaneously nonnegative and at most `-eta`.
For rational `M`, a rational optimum exists by rational linear programming.
These are elementary finite-dimensional facts.

The quitting-game split can be stated more strongly than in the draft.  The
checked theorem
`exists_uniformEquilibriumPayoff_of_projectiveQBar_snell` consumes ambient
projective `Q̄` without assuming all players are punishment normal.  Hence
every finite quitting table has a uniform payoff or its normalized singleton
matrix has a strict blocker on some principal face.  In the maintained Fin4
hard residual, the checked principal-size reduction permits choosing a face
of cardinality two or three.

## 4. Full-support helper calculation is correct

Full packet support pins every target coordinate to the corresponding own
singleton payoff.  The packet's mixture inequality is therefore precisely

\[
 Mp\ge0.
\]

Testing this inequality against a blocker and separating internal and
external columns gives

\[
 \sum_{j\notin P}p_j y^TM_{P,j}\ge\eta p(P).
\]

Thus `P` is proper and some outside owner satisfies

\[
 y^TM_{P,j}\ge \eta\frac{p(P)}{p(P^c)}>0.
\]

Since `y` is a probability vector, some blocked row has the same lower bound.
Equations (10)--(12) are correct.  With packet mass floor `m_0`, one also gets
the coarser source-independent bound

\[
 y^TM_{P,j}\ge \eta |P|m_0
\]

for some outside `j`.  On a three-player Fin4 face, `j` is the unique fourth
player.

The chain obtained by repeatedly adjoining a selected helper is a valid
finite **table-level** itinerary and reaches a good face after at most
`|I\P|` additions, because the full face is good.  It is not yet a dynamic
rank: an arbitrary behavioral chronology may later drop a previously added
owner.  Any well-founded use must construct nested supports or prove that
support loss is separately consumed.

## 5. Collision tax and small-h leakage

The conditional implication

\[
 M_Px+c\ge-\delta\mathbf1
 \quad\Longrightarrow\quad
 y^Tc\ge\eta\sum_{j\in P}x_j-\delta
\]

is correct.  So is the outside-leakage estimate, provided its full premise is
written explicitly as

\[
 M_Pq_P+M_{P,P^c}q_{P^c}+c\ge-\delta\mathbf1,
 \qquad y^Tc\le Ch^2.
\]

Then

\[
 \eta s\le B_Po+Ch^2+\delta.
\]

The two displayed consequences require the boundary qualifications
`C>0` and, for the ratio statement, `h>0`.  If `C=0`, the first conclusion
strengthens to `h=0` under its other hypotheses.

For a reward coordinate bound `R`, normalized singleton matrix entries have
absolute value at most `2R`; hence `B_P<=2R`.  The draft's leakage fraction can
therefore be made uniform as

\[
 \frac{o}{h}\ge\frac{\eta}{2(2R+\eta)}.
\]

## 6. Stronger checked adapter to existing chronology machinery

The blocker has a direct repository interpretation that the draft does not
name.  Extend `y` by zero outside `P`, let

\[
 b_i=r_i(\{i\}),
\]

and use `boundary=b`, `owners=P`, `covector=y`, and `margin=eta`.  For every
`j in P`,

\[
 \langle y,b-r(\{j\})\rangle
   =-y^TM_{P,j}\ge\eta.
\]

This is exactly a `TightFaceSeparatorData reward`.  Consequently all checked
theorems in `TightFaceCollisionEscape.lean` apply to any literal exact
punishment-floor path which remains near `b` and whose quitting support lies
in `P`.  Such a path either pays the strict covector charge or incurs the
explicit macroscopic collision tax.  The adapters in
`TightFaceCollisionEscapeAdapters.lean` then convert the appropriate path
hypotheses to semantic debt excursion statements.

This is a stronger and cleaner formal target than introducing a parallel
collision-tax API:

```lean
theorem PrincipalStrictBlocker.toTightFaceSeparatorData
theorem FinFourQuantitativeFullSupportHardResidual.exists_strictBlockerSeparator
```

It is still a supplied-path consumer.  The hard residual does not produce a
source-matched exact path near the solo boundary with support in the blocked
face.

## 7. Terminal-law scalar identity

Define the missing Never case explicitly:

\[
 \kappa_y(S)=\sum_{i\in P}y_i(r_i(S)-b_i),\qquad
 \kappa_y(\infty)=-\sum_{i\in P}y_i b_i.
\]

For any complete terminal law `mu`, including its Never atom,

\[
 \sum_S\mu(S)\kappa_y(S)=y^T(u_P-b_P).
\]

Active singleton terms are at most `-eta`, so moving them to the other side
gives equation (22).  The identity is exact.

It reduces the payoff information needed to certify blocker-charged exit in
one **already supplied** law to the scalar anchor
`y^T(u_P-b_P)`.  It does not by itself align a product root, a reached time,
or a Bellman successor, and therefore should not be described as solving
source matching in full.

## 8. Relationship to `COMP.md`

`COMP.md` still needs an ordered small-`h` periodic chronology whose local
Bellman/debt residuals sum to `O(h^2)` and whose joint and generated-secant
survival products contract by `Omega(h)`.

The blocker is a useful necessary-condition engine for any such attempt.  If
a phase uses `Omega(h)` internal singleton hazard on a bad face, only
`O(h^2)` collision correction, and `O(h^2)` local seam error, then it must use
`Omega(h)` outside hazard.  A realization supported entirely on that bad face
is impossible for sufficiently small `h`.  On Fin4 the helper chain says that
at most two monotone support enlargements reach the full good face.

This does not construct the periodic data.  In particular:

* the common-host and complementary-pair coalitions in `COMP.md` are literal
  same-row endpoint states, not automatically the active principal face of a
  small-h singleton clock;
* the packet-selected outside column is table-level data and is not attached
  to the same literal tail or endpoint cycle;
* adding outside hazard can create first-order Bellman effects in every
  payoff coordinate and can destroy the required `O(h^2)` period cancellation;
* the generated-secant contraction remains to be proved; and
* supports are not automatically nested along an actual chronology.

Thus `FACE_ENLARGE.md` sharpens the admissible shape of the missing producer:

\[
 \text{bad internal face}
 \Longrightarrow
 \text{first-order outside leakage or macroscopic collision},
\]

but it does not supply the source-matched first-order periodic realization.

## 9. Unsupported final step in the draft

The proposed causal theorem (24) is a legitimate next target, not a proved
consequence of the preceding equations.  Existing causal atom theorems do not
show that the routed collision has positive blocker pairing or activates the
blocker-selected helper.  Moreover, if the face changes, its optimizer `y`
may change, so blocker-weighted collision terms do not automatically
telescope.  Likewise, `|I\P|` cannot decrease infinitely only if the actual
construction keeps the enlarged supports nested.

Accordingly, the sentences claiming that uncharged cycling is excluded and
that rank can change only finitely often must be made conditional on a new
source-matched consumer proving those monotonicity and sign properties.

## Export-gate assessment

### Does not yet qualify

* `FaceTangent iff projective Q̄`: correct and useful, but it only refutes one
  proposed API-level class enlargement.  It does not close a named live arm or
  remove an exhaustive conjecture route.
* Strict blocker/outside helper/collision tax: correct supplied-data
  mathematics, but no arbitrary-game chronology producer reaches the checked
  consumer.
* The proposed causal blocker alternative (24): not proved.

### Worth formalizing outside `exports/`

* Zero-diagonal tightening.
* Completely-`S_0`/projective-`Q̄` equivalence, after importing or proving the
  Pang/Karamardian LCP theorem.
* Finite strict blocker alternative and rational certificate.
* Full-support outside-helper inequalities.
* `PrincipalStrictBlocker.toTightFaceSeparatorData`.
* The repaired small-h leakage inequalities and scalar terminal-law identity.

These declarations would make the matrix no-go and the exact local producer
obligation durable without overstating conjecture progress.
