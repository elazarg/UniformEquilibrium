# Strict principal blockers as tight-face chronology data

Current status: proved in ordinary mathematics.  The source strict blocker is
not yet produced by checked Lean, and no source-matched exact path is produced
here.  This note isolates a direct adapter to existing checked consumers.

## Question

Let `reward` be a finite quitting table, let

\[
M_{ij}=r_i(\{j\})-r_i(\{i\})
\]

be its normalized singleton matrix, and let `P` be nonempty.  Suppose there
are `y in Delta(P)` and `eta>0` such that

\[
  y^TM_{P,j}\le-\eta\qquad(j\in P).
\]

Does this finite matrix certificate instantiate a checked chronological
consumer without introducing a new collision interface?

## Adapter theorem

Extend `y` by zero outside `P` and put `b_i=r_i({i})`.  Define

```text
boundary = b
owners   = P
covector = extended y
margin   = eta.
```

For every `j in P`,

\[
\begin{aligned}
\langle y,b-r(\{j\})\rangle
 &=\sum_{i\in P}y_i\bigl(r_i(\{i\})-r_i(\{j\})\bigr)\\
 &=-y^TM_{P,j}\\
 &\ge\eta.
\end{aligned}
\]

Therefore these data define a `TightFaceSeparatorData reward` exactly as used
by
`UniformEquilibrium/Quitting/Chronology/TightFaceCollisionEscape.lean`.

## Checked consumers reached conditionally

For every supplied exact punishment-floor prefix whose quitting support stays
inside `P` and whose payoff annotations stay within the structure's local
radius of `b`, the checked declarations

* `TightFaceSeparatorData.local_bellmanDrift_pairing_le`,
* `TightFaceSeparatorData.path_pairing_lowerBound`, and
* `TightFaceSeparatorData.path_halfMargin_lowerBound`

give the exact strict-covector charge versus literal collision-mass account.
The semantic adapters in
`UniformEquilibrium/Diagnostics/Quitting/Chronology/TightFaceCollisionEscapeAdapters.lean`
then apply under their explicit source and minimum-debt hypotheses.

## Fin4 hard-residual source

Ordinary matrix theory gives

\[
\operatorname{Completely}S_0(M)
\iff \operatorname{IsProjectiveQBarMatrix}(M).
\]

Hence a Fin4 hard residual's nonprojective principal admits a strict blocker.
The checked size reduction permits a blocked face of cardinality two or
three.  Its quantitatively full-support packet also gives an outside owner
`j` with

\[
y^TM_{P,j}\ge\eta\frac{p(P)}{p(P^c)}>0.
\]

These facts produce the separator and table-level helper on the same reward
table.  They do not attach either one to an actual minimum-law row.

## Relationship to the periodic producer

Any small-h realization with internal hazard `s`, outside hazard `o`,
quadratic collision correction, and local inward error `delta` obeys

\[
\eta s\le B_Po+Ch^2+\delta.
\]

Thus an `Omega(h)` clock confined to the blocked face is incompatible with
`O(h^2)` collision and seam errors.  A valid periodic realization must leak
`Omega(h)` hazard outside the face or use a macroscopic collision.

This is a verifier, not the missing producer.  Open: construct the outside
leakage on the literal endpoint-cycle source while preserving first-order
period cancellation, punishment floors, and generated-secant contraction; or
convert the macroscopic collision to an established semantic endpoint.

## Source audit

Declarations inspected:

* `IsProjectiveQBarMatrix` and
  `isProjectiveQMatrix_iff_standard_or_homogeneous` in
  `UniformEquilibrium/Quitting/Classification/LCP/MatrixClasses.lean`;
* `PrincipalQDirection` in
  `UniformEquilibrium/Quitting/AbsorptionPath/PrincipalQDirection.lean`;
* `TightFaceSeparatorData` and its path estimates in
  `UniformEquilibrium/Quitting/Chronology/TightFaceCollisionEscape.lean`;
* `FinFourQuantitativeFullSupportHardResidual` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`.

Literature inputs:

* Tsatsomeros--Wendler, *Semimonotone matrices*, LAA 578 (2019),
  Theorem 3.1(4), DOI `10.1016/j.laa.2019.05.009`;
* Pang, *On Q-matrices*, Mathematical Programming 17 (1979), 243--247,
  DOI `10.1007/BF01588247`.

The exact review of the matrix identity and boundary qualifications is in
[`../feedback/FACE_ENLARGE__BY_CODEX_FARADAY.md`](../feedback/FACE_ENLARGE__BY_CODEX_FARADAY.md).
