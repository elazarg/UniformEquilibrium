# Independent review of positive-Never off-minimum corner cap-face reduction

Reviewer: **CODEX_RAMSEY**  
Source: [`CODEX_EULER__POSITIVE_NEVER_OFF_MINIMUM_CORNER_CAP_FACE_REDUCTION.md`](../notes/CODEX_EULER__POSITIVE_NEVER_OFF_MINIMUM_CORNER_CAP_FACE_REDUCTION.md)  
Verdict: **PASS; no mathematical repair**  
Disposition: **internal only**.  The strict singleton-over-cap arm is genuinely
consumed, but the all-Continue cap face remains and the construction does not
regenerate the positive-Never rectangle.

## Claim checked

Let actual profiles `sigma_n` have terminal semantic pairs

```text
Sem(sigma_n)=(U_n,B_n) -> X=(U,B),
```

and let `m` be a global carrier minimizer with `D(m)=D_*>0`.  If a fixed
player `i` satisfies

```text
B_i <= r_i({i})-kappa,       kappa>0,
```

then every sufficiently late terminal-gap paid cap port extracted at the
literal source `sigma_n` has

```text
kappa/(kappa+4M) <= totalAbsorption
```

and hence

```text
D_* kappa/(kappa+4M)
  <= D(Sem(sigma_n))-D(port limit).
```

Under the positive terminal gap the port is in the checked quantitative-debt
descent arm.  Therefore the only unconsumed limiting scalar face is
`r_i({i})<=B_i` for every `i`, equivalently exactness of the all-Continue root
against `B`.

## Independent proof check

### 1. Limiting corner and source identity

Coordinate convergence gives, eventually,

```text
B_{n,i} <= r_i({i})-kappa/2.
```

For each supplied
`QuittingActualProfileTerminalGapPaidCapPort r m sigma_n gamma`, the fields
`source_profile` and `source_minimum` identify the paid-cap source profile
with exactly `sigma_n` and its minimum with exactly `m`.  Thus the time-zero
root in `source.totalAbsorption` is

```text
quittingCapLiftedPrefixRoot r sigma_n,
```

not a root selected at another rectangle corner.  Its exact Nash condition
against the unrestricted behavioral cap `B_n` is precisely
`quittingCapLiftedPrefixRoot_exactNash` in
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PaidCapLiftedSummablePort.lean`.
The endpoint-Nash conversion used in the note is the exact equivalence
`isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash`.

This verifies the same-source assertion for each fixed actual `Q`, `Y`, or
`Z` corner sequence produced upstream.  It does not identify the paid row or
cap-prefix chronology of one corner with those of another.

### 2. Absorption constant and boundary roots

Apply
`gap_div_le_quittingRootAbsorptionMass_of_isZeroEndpointNash` from
`UniformEquilibrium/Quitting/Boundary/Repair/FixedTailUniformAbsorption.lean`
with `eta=kappa/2`.  Its conclusion is joint root absorption, not merely
opponent absorption:

```text
(kappa/2)/(kappa/2+2M) <= quittingRootAbsorptionMass q_n.
```

The left side is exactly `kappa/(kappa+4M)`.  The declaration handles both
branches that matter at the boundary: if the selected player's Continue
probability is zero, joint absorption is one; otherwise endpoint optimality
and the outsider contribution bound give the displayed ratio.  No interior
root or stationary-support assumption is hidden.

The reward bound and `kappa>0` make the denominator positive.  If `M=0`, the
strict singleton-over-cap hypothesis is itself impossible for a reward table
bounded by zero, so there is no omitted zero-denominator case.

The complete charge is the `tsum` of nonnegative root absorption masses.  Its
time-zero term is therefore at most `source.totalAbsorption`; summability is
already supplied by the positive-minimum paid-cap source.  This establishes
the exact constant in (2.2), with no loss beyond replacing the limiting gap
by `kappa/2`.

### 3. Debt-drop orientation

`QuittingPaidCapLiftedSource.minimum_mul_totalAbsorption_le_debtDrop` in
`PaidCapPortExactTrichotomy.lean` states

```text
D(source.minimum) * source.totalAbsorption
  <= source.initialDebt-D(port.semanticPort.limit).
```

Using `source_minimum`, `source_profile`, and the definition of
`source.initialDebt` rewrites this literally as

```text
D_* * source.totalAbsorption
  <= D(Sem(sigma_n))-D(L_n).
```

Multiplication by the positive `D_*` preserves the absorption lower bound,
so the note's `D_* kappa/(kappa+4M)` constant and inequality orientation are
correct.  The port limit has the checked field `limit_mem`, hence it is a
carrier point; global minimality gives `D(L_n)>=D_*`.  Consequently

```text
D(Sem(sigma_n))-D_* >= D_* kappa/(kappa+4M),
```

and continuity of total debt under `Sem(sigma_n)->X` proves Corollary 3.1
without selecting a convergent subsequence of the varying port limits.

### 4. Exact trichotomy and terminal-gap use

Positive total absorption excludes `InertStall`, whose checked field is
`totalAbsorption_eq_zero`.  The theorem
`QuittingActualProfileTerminalGapPaidCapPort.quantitativeDebtDescent_or_inertStall`
uses the terminal exploitability gap to eliminate `ChargedNearReturn`, since
that branch carries an unrestricted uniform-equilibrium-payoff consumer.
Thus every sufficiently late port is indeed a
`QuantitativeDebtDescent`.  The proof does not confuse positive absorption
with positive cap displacement: the latter follows only after the terminal
gap has ruled out the zero-displacement charged-return branch.

For a finite player set, failure of all singleton inequalities gives an
attained positive maximum of
`(r_i({i})-B_i)_+`; conversely zero maximum is exactly the all-Continue cap
face by `isZeroQuittingRootNash_allContinue_iff_singleton_le`.  The stated
dichotomy is exhaustive.

## Provenance and exact surviving obstruction

The result is a real quantitative contraction of the off-minimum-corner
branch:

```text
strict singleton-over-cap at X
  => same-source positive cap charge
  => a carrier limit with a fixed total-debt drop.
```

It is not yet a regenerated descent.  The limiting carrier point `L_n` need
not be attained by a single behavioral profile, retain the source's
positive-Never law mass, retain the rectangle response square, preserve its
debt support, or come with a return edge to the original minimum source.  The
terminal-gap paid row used to construct the port is source-native at
`sigma_n`, but no paid-row identity across `n` or across rectangle corners is
proved.

Accordingly the exact residual is only the scalar all-Continue cap face at
the fixed actual off-minimum corner.  This note does not consume that face,
does not produce a finite-valued rank decrease, and does not by itself meet a
`FIN4_BT_QUESTION` output.  Its internal/no-export status is correct.

## Verdict

**PASS, no repair.**  The constant, source orientation, unrestricted-deviation
semantics, carrier debt inequality, and trichotomy composition all check.  A
formal wrapper would need only the elementary nonnegative time-zero-term
bound plus the displayed rewrites; there is no mathematical gap in the
ordinary argument.
