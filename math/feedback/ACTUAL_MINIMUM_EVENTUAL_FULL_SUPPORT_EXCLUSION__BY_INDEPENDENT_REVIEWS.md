# Independent reviews of eventual full-support exclusion

The reviews below approve the exact bytes of
[the proof packet](../exports/ACTUAL_MINIMUM_EVENTUAL_FULL_SUPPORT_EXCLUSION.md),
including its conditional export scope. This is ordinary mathematics; no new
Lean check or solution of Fin4 is claimed.

# Independent final review: actual full-support minimum exclusion

Reviewer: finite_pivot_contacts. Decision: PASS for mathematical soundness,
self-containment, the stated actual-source scope, and the exceptional
conditional export gate. There is no unresolved mathematical objection.

This decision applies exactly to
`ACTUAL_MINIMUM_EVENTUAL_FULL_SUPPORT_EXCLUSION.md`, SHA256

    effa2d307a38dbfd07a58d1a5f194b785ccea07e719717ecb9d92bb02596f6d4

I read the complete final mathematical packet and its embedded verifier.
The review is independent of its construction. No Lean command was run and
no Lean-checked status, integration, or completed source-to-UE chain is claimed.

## Exact approved conclusion

Fix an invertible hollow Gamma, a pivot p with Gamma^-1 e_p strictly
positive, and J=Gamma D, where the four diagonal entries of D are distinct
and belong to (0,1/2). On an open neighborhood in all24 Gamma/J reward
coordinates, with the remaining32 native rewards arbitrary finite numbers,
each full table has a positive small-penalty bound. For every penalty below
that bound, an actual observer-constrained global minimum with positive
original Never masses and ALL-END cannot be eventually full support after
deleting completely empty dates, unless only finitely many nonempty dates
remain. Thus an infinitely active such minimum has proper support at
infinitely many nonempty dates.

The penalty bound is table-dependent. No common bound over unbounded passive
rewards is asserted. In the source application the penalty must be chosen
before selecting a minimum afresh. A source with infinitely many proper-
support dates, finitely many active dates, or no actual realizing law remains
outside the exclusion. No new UE existence class or complete Fin4 solution
is claimed.

## Finite actual-law adapter

I checked the actual-law and finite-variation steps independently, including
their sensitivity to earlier pivot cap contacts.

1. Positive original Never ensures positive survival through every finite
   head. ALL-END and observer optimality therefore pass to literal tails.
   At a positive observer hazard, the conditional Quit value equals Never.
2. Removing all-empty dates preserves payoff, Never offers and marginal
   Never. The compressed deadline set is a subset of the old set, while
   Never still attains the old cap, so full caps are preserved exactly.
3. The uniform collision expansions e=Gamma f+O(|f|^2) and
   Q=Jq+O(|f|^2), together with ||Gamma^-1 J||<1, forbid all four contacts
   in a sufficiently small nonzero conditional tail. Full support already
   gives three observer contacts, so all late pivot comparisons are strict.
4. The four-date homogeneous constraint kernel is the controllability
   kernel for A=I-J^-1 Gamma and b=J^-1 e_p. At the structured locus this is
   a diagonal Vandermonde problem with every entry of b nonzero. Hence the
   four-date16-by16 Jacobian is invertible; five dates give19 independent
   constraints on20 hazard variables.
5. Fixing all four entrance Never offers fixes the entire entrance cap
   vector on the feasible window. Observer entrance prescribed payoffs also
   remain fixed. Literal backward full-cap recursion then preserves all
   earlier caps, including every old pivot contact. Actual positive hazards
   and late strict pivot gaps supply the two-sided feasible neighborhood.
6. Whole-objective variation is a positive joint head-survival factor times
   variation of -u+r nu at the entrance. Five-date finite stationarity
   supplies unique multipliers. Freezing either endpoint and using the
   four-date uniqueness gives Y_i^+=(Y_i-Z_i)/(1-q_i), including the proper
   division of later contact multipliers by joint root survival.
7. Four-date inverse continuity gives Y->e_p+r w and Z->0. This constructs
   the convergent actual adjoint sequence without an infinite-dimensional
   KKT assumption or a selected consistent multiplier sequence.

## General first jet and preserved form

I independently derived the cancellation at r=0 before reviewing the final
generalized statement. At Y=e_p, the exact identity

    E_p-U=q_p(P_p-Q_p)+H_p e_p^+-c u^+

removes all passive-pair second derivatives from the seven-control first
jet. The successor and stationarity first jets in equations(11)--(12) are
correct, including the instruction to take partial derivatives with future
values fixed before substitution. Thus all first-jet tests at r=0 depend
only on the24 Gamma/J coordinates; the other32 rewards influence nonlinear
neighborhoods and small positive penalty bounds but not this calculation.

For general, possibly nonsymmetric Gamma, putting
x=Gamma^-1 delta e and z=Gamma^T delta Y-1 delta d gives exactly the
recurrences(13), scalar control solve(14), and pivot block(15).
The pivot block has trace2, determinant1, and a nonzero Jordan off-diagonal.
The six remaining nonunit modes are beta_i and beta_i^-1 for i!=p, where
beta_i=-D_i/(1-D_i). The characteristic polynomial and three-dimensional
fixed eigenspace follow without relying on the symmetric numerical fixture.

The zero-observation argument is also general. Four successive zero hazards
force constant x and scalar g; the four remaining scalar relations form the
Vandermonde system with coefficients v_i(beta_i-1). All are nonzero. Hence
the four-block observation stack has rank7 with kernel precisely the fixed
tangent space. This supplies the normal observability needed later.

I checked the sign in the differential contact cancellation and the factor
nu=c nu^+. They yield preservation of

    alpha=(d(-u+r nu)+Y dot de)/nu.

Its exterior derivative is nondegenerate in the displayed coordinates, so
the map is symplectic and locally invertible. The explicit fixed manifold
has dimension3. Six eigenvalues remain separated from1; symplectic parity
forces the algebraic unit multiplicity to stay4 along that manifold and
under the allowed perturbations. Quotienting the fixed tangent gives one
simple normal eigenvalue identically1. This is an exact property, not a
limit-only spectral assertion. All required rank and spectral tests are
open; the stated order of choosing the raw neighborhood and then the
table-dependent penalty bound is valid.

## Nonlinear asymptotic argument

I reviewed the complete standalone dynamical proof, including its elementary
asymptotic integration step rather than appealing to a named theorem.

The finite observation stack controls normal distance uniformly near the
fixed manifold, because the observation map vanishes on that manifold and
its selected normal minor is invertible. Nonnegative summable actual
hazards therefore imply summable normal coordinates and summable changes
in the tangent coordinates. Passing to a smooth normal eigenbasis gives a
diagonal recurrence plus an absolutely summable perturbation; it does not
incorrectly assume that the drift of diagonal eigenvalues is summable.

For each diagonal mode the forward, backward, and unit-coordinate Green
operators map summable forcing to a sequence tending to zero. The backward
kernel includes the first inverse factor. A small tail norm gives the
claimed contraction and produces a full basis of solutions with the exact
diagonal product asymptotics. Uniform absolute-value gaps make the largest
nonzero mode dominant. Convergence excludes the unstable modes and the
identically-unit mode. Every remaining stable multiplier is negative, so
observability forces an eventually alternating observed coordinate,
contradicting nonnegative hazards. The result is eventual equality with the
limiting fixed point, not merely an unproved qualitative approach to the
fixed manifold.

The nonlinear boundary counterexample correctly shows why unit eigenvalue
persistence is necessary. The unobserved-mode and alternating-observation
tests correctly delimit the other assumptions.

## Exact calculations and positive actual-law boundary

The embedded SymPy program is byte-identical to the program I previously
extracted and executed successfully for all four pivots. Its SHA256 is

    7f903c8eacd672b7fb8d45da4d3c7c8038b96a1d02f6ad745bdda76ea154a281

All exact assertions passed: inverse positivity, finite-window ranks and
determinants, control determinants, characteristic polynomials, unit kernels,
observation rank, the displayed nonzero observation minor, and the stable
eigenmode observations. The exact rational calculation supplements the
general proof; it is not used to infer its quantifiers.

I independently checked the final28-line actual-law construction. For
a=[I-(1-rho)D]^-1 v and E=Gamma a/(1-rho), the identity
Gamma a-(1-rho)Ja=e_p gives the required observer linear contacts and
strict pivot linear gaps. Four-date invertibility produces the exact
positive small block. Concatenating geometrically decreasing amplitudes
matches the assigned boundary offers exactly and makes hazards summable.
The vanishing assigned tails identify actual Never responses; every finite
deadline lies below those responses, and observer deadline atoms tie them.
Thus actual caps equal Never and every observer debt is zero. No prescribed
successor payoff or continuation realization was assumed. E need not be
positive, and the packet appropriately makes no such claim. Global
minimality and a positive absorbing gap are not claimed for this boundary.

This construction establishes that the support/contact geometry itself is
realizable throughout the structured locus. Global minimality is the
essential obstruction supplied by the new theorem.

## Source scope, overlap, and conditional exception

I inspected the exact stopping-law/behavioral payoff and cap declarations
named in the packet in StoppingLawOperationalDistance.lean, the literal
root identities quittingTerminalSemanticPair_rootThenContinuation in
TerminalSemanticPair.lean and
quittingContinuationBestResponseValue_rootThenContinuation_eq_max in
TerminalDebtPrefix.lean, and the stated total semantic-debt equivalence in
PositiveMinimumSemanticDebt.lean. Their statements agree with the source
correspondence. In particular, the total-debt equivalence does not itself
produce the actual observer-constrained minimum used here.

The packet explicitly leaves actual attainment and selection in the actual
source case as inputs. An arbitrary compact semantic point is insufficient
for the summability and actual-tail arguments. No successful repair,
controller, return orbit, or equilibrium strategy is assumed to obtain the
conclusion. All finite comparison laws and adjoint multipliers are produced.

I affirm the exceptional conditional admission required by exports/README.md.
The independently important contribution is a complete exclusion of the
eventual-full-support geometry for actual minima on an open raw-table region,
with arbitrary other rewards. It removes both the previous mass-saturation
exception and earlier finite pivot contacts for that geometry. Its source
restriction is strictly stronger than the previously available necessary
conditions: the mass-saturation equality is not used, and throughout the
structured locus every eligible W in the earlier sufficient positive-energy
criterion fails in the v direction. This rules out the complete existential
curvature certificate there, rather than one selected certificate.

The approval is for this conditional actual-source restriction, not for
eliminating the whole actual source branch, a new reward-table UE class,
unrestricted realization, or a completed source-to-UE chain. Sparse and
finite calendars and the nonrealized arm remain open. The raw examples are
not certified to evade every existing UE theorem. Those limitations are
accurately stated and do not undermine the new restriction on the named
actual-minimum obligation.

The full proof, exact boundary data, and verifier are included in the packet.
No mathematical step depends on an external conference note. The suggested
Lean handoff targets ordinary finite maps, literal game semantics, and the
proved dynamical lemma; it does not encode the desired conclusion as an
assumed strategy or structure field.

# Review of the complete full-support actual-minimum exclusion

Reviewer: global_mixed_endpoint. Reviewed complete candidate
ACTUAL_MINIMUM_EVENTUAL_FULL_SUPPORT_EXCLUSION.md at SHA256

    effa2d307a38dbfd07a58d1a5f194b785ccea07e719717ecb9d92bb02596f6d4.

Verdict: PASS for mathematical soundness, the stated source scope, and
restricted conditional export admission. No unresolved mathematical
objection remains. I independently checked the game adapter and dynamical
argument, and independently derived the zero-penalty cancellation and
structured-locus first jet during review; those derivations helped broaden
the assembled statement. This record should accompany the other independent
review, not be represented as the only external review of that generalization.
No Lean command or tracked edit occurred.

## Actual-law adapter and finite stationarity

Deleting only empty dates is justified by ALL-END: retained deadline values
and Never are preserved, so removing unused responses cannot change the full
cap. Payoff and original Never coordinates are preserved as well. The new
actual profile remains a minimum over the same observer-optimal comparison
class. This handles arbitrarily many empty dates without adding small hazards.

The expansions e=Gamma f+O(F^2) and Q=Jq+O(F^2) hold uniformly over timing
laws for the fixed finite table, since every exceptional event requires two
finite opponent times or two current quitters. At a structured pair,
||Gamma^-1 J||_infinity=max D_i<1, persistently nearby. All four contacts
would therefore imply F<=kappa F+O(F^2), impossible for small positive F.
At full support the three observer contacts already hold, so every late
pivot contact is excluded. This does not require earlier pivot strictness.

The four-date constraint Jacobian is invertible because its kernel is the
four-control endpoint recurrence with the nonzero Vandermonde determinant.
The five-date constraint gradients have rank19 by the same recurrence with
five controls and endpoint rank4. The one-dimensional finite fiber consists
of actual observer-optimal ALL-END comparison profiles on a sufficiently
small two-sided neighborhood. Fixing ALL entrance caps preserves earlier
pivot caps even if some earlier deadlines are tied. Thus no differentiability
of a moving global maximum is being assumed.

Constrained stationarity and multiplier uniqueness are genuinely finite-
dimensional. Restricting the five-date identity by freezing its last root
gives the first four-date tuple. Freezing its first root instead changes the
entrance multiplier to (Y_i-Z_i)H_i/c=(Y_i-Z_i)/(1-q_i), after dividing the
objective and later-contact multipliers by c. Four-date uniqueness proves
the exact gluing formula. At zero data the unique entrance multiplier is
e_p+r Gamma^-T 1 and the contact multipliers vanish. Continuity of the
fixed inverse Jacobian proves convergence of the actual glued state.

## Adjoint map, preserved form, and persistent unit eigenvalue

The seven equations in the packet are the first-root restrictions of the
finite multiplier identities. Partial q derivatives are correctly taken
with future values fixed before substituting their formulas. The actual
state and controls converge to the local inverse-function base point, so
uniqueness of that branch makes the actual sequence an orbit of T.

I checked the sign in the differential cancellation. Differentiating the
observer contact gives (Q_q-E_q)dq=H de^+. Stationarity replaces the dq
coefficient in dz+Y de by -Z(Q_q-E_q); thus the remaining coefficient is
(Y-Z)H=cY^+. This proves the exact one-form preservation, including the
original Never scaling. The coordinates(z,e;1/nu,Y/nu) are invertible for
nu>0 and give a nondegenerate canonical exterior derivative.

The fixed manifold equation(10) follows directly from q=Z=0 and
e=t e_p. Its matrix is invertible near zero, providing three genuine fixed
tangent directions. The structured first jet has unit algebraic multiplicity4
and other eigenvalues separated from1. Symplectic parity and persistence of
those three fixed directions force exact multiplicity4 along the nearby
fixed manifold. Quotienting by its three tangent directions leaves one simple
normal eigenvalue identically1. This is stronger than a base-point numerical
eigenvalue check and is essential.

## General raw certificate and independent exact checks

My separate first-jet derivation agrees with(11)--(12). At r=0, the Hessian
of P_p cancels between the Y=e_p contribution and prescribed pivot payoff.
The remaining control q block is

    -h J_p-(J_p-Gamma_p)^T h^T,

the Z block is (J-Gamma)_observers^T, and the state part is
Gamma^T delta Y+h delta e_p-1 delta d. Every passive pair and higher reward
is absent. Thus the24-coordinate neighborhood can be chosen independently
of all32 unrestricted coordinates. The small positive penalty threshold may
depend on the table, exactly as the statement permits.

For J=Gamma D, I independently obtained the same x,z,g reduction. Formula(14)
uniquely solves the controls because v_p(1-2D_p) is nonzero. The pivot block
has trace2 and determinant1, with a nonzero rank-one nilpotent difference
from identity. The triangular ordering gives the full characteristic
polynomial, and the fixed space is exactly x=t v,z=-t h with free d,nu.

The four-block observation proof is exact: four zero hazard vectors make
x and g constant, and the four pivot observations form a Vandermonde system
in the four distinct beta_i, with nonzero coefficients v_i(beta_i-1).
Its only solutions are the fixed tangent. Hence the observation rank is7.
This establishes the raw certificate throughout the stated structured locus,
not only at the rational example.

The complete embedded SymPy program ran successfully for all four pivots.
I additionally reconstructed the first-jet matrices directly from the
formulas above, without using the root-polynomial program. This independently
reproduced every control determinant, characteristic polynomial, unit kernel
dimension3, and observation rank7 at the rational example.

## Nonlinear dynamical conclusion

The earlier standalone review was rechecked against the version included in
this packet. Finite observation rank controls the normal distance by a finite
sum of observation magnitudes. Nonnegativity and summability therefore imply
l1 normal distance and l1 tangent increments. The smooth moving eigenbasis
then gives a diagonal recurrence with an l1 perturbation.

The forward stable, backward unstable and backward unit-tail solution
operators map l1 forcing to c0 with uniform sup bounds. Their contraction
construction gives a full asymptotic solution basis. A nonzero solution
tending to zero must have a dominant stable negative mode; its nontrivial
observation alternates sign, contradicting nonnegativity. This excludes
the actual eventual-full-support orbit. No normal center-manifold theorem,
unproved infinite-dimensional multiplier, or exchanged infinite derivative
is used.

The included polynomial counterexample when the unit normal eigenvalue is
not persistent verifies a genuine boundary of the argument. Earlier cap
contacts, saturation equality, and empty dates were also explicitly tested
by the preceding exact adapter rather than discarded by genericity.

## Source audit and export-gate assessment

The named stopping-law payoff/cap identities, literal prefix identity and
full max-cap recursion were checked in their tracked Lean sources. Their
scope matches the unrestricted behavioral semantics used here. The cited
positive-minimum declaration concerns compact TOTAL debt; the packet correctly
does not use it to manufacture actual observer-constrained attainment.
The actual source, its pivot and its global minimality remain explicit inputs.

I affirm the conditional exception for the complete claimed reduction. On
the stated raw region, once the penalty is chosen below the positive source
threshold and epsilon(Z), and the source is selected afresh, the entire
eventual-full-support actual case is impossible. All charts, comparison
profiles, multipliers and orbit data are produced from that law. Neither a
successful controller nor an extra strategic certificate is assumed.

This strictly strengthens the prior mass-saturation alternative: the equality
case and arbitrary earlier finite contacts are now included in the exclusion.
The earlier positive quadratic-energy certificate fails for EVERY candidate
W throughout the structured locus because (D_pp-1/2)v_p<0; that failure
persists on a neighborhood. The argument is therefore not a renamed witness
for that sufficient test. This comparison does not assert that every raw
example is outside all existing UE existence theorems.

The result remains an actual-source mode exclusion, not a new UE reward-table
class, actual-attainment theorem, or Fin4 solution. Finite active laws,
infinitely many proper-support dates, and nonrealized endpoints remain open.
No claim that support labels must change infinitely often is made: the
precise conclusion is omission of some player at infinitely many nonempty
dates. These limitations and the table-dependent penalty threshold are
substantive parts of the approved statement.

## Final actual-law boundary addition

The final 28-line addition was independently checked and this review is
rebound to the complete hash above. For every stated structured pair and
0<rho<1, the diagonal inverse defining a is positive, and direct algebra
gives J a-E=-e_p/(1-rho). The geometric first-order hazards have exactly
the prescribed entrance and terminal offer derivatives. The already
invertible four-date map therefore supplies the stated exact analytic
blocks, with all hazards positive and pivot gaps strictly negative for
small positive amplitude. Constants are uniform as the geometric amplitudes
decrease within one fixed small interval.

Concatenating at amplitudes t_0 rho^(4n) matches the terminal and subsequent
entrance offers exactly. Summable positive hazards define genuine independent
complete laws with positive Never coordinates. Iterating the literal Never
recursion and letting the far boundary vanish proves equality of the assigned
and actual offers; no continuation beyond an infinite calendar is needed.
Each finite deadline is bounded by its corresponding entrance offer because
all pivot gaps are nonpositive, while every observer deadline is tied. Never
attains that offer. Hence the full unrestricted caps equal Never, and each
observer's actual mixture of deadlines and Never attains its cap. This is
an actual full-support ALL-END observer-optimal family on every structured
locus in the theorem, without asserting global minimality or a positive
absorbing gap. The addition is sound and makes the exclusion's boundary
more concrete; it does not enlarge or weaken the approved export scope.
