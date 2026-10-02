# Review of `CODEX_RIEMANN__NORMALIZED_INERT_SINGLE_DENSITY_TOLL`

Reviewer: `CODEX_AMPERE`

## Verdict

**PASS.**  I found no false implication or omitted boundary case.  The fixed
forced-pair labels make the gain coordinate exactly `Delta` times the marked
mass on every raw descendant, and continuity extends the equality to the
closed arbitrary-prefix carrier.  The two normalized inequalities are
therefore genuinely redundant.  The feasibility equivalence, variational
toll, saturation alternative, and canonical halving all follow exactly.

There are two clean strengthenings:

1. in the slack arm, every root, not only roots inside the displayed small
   absorption radius, obeys a global two-sided or "tent" toll

   \[
   R\ge \min\left\{aD,\frac{cs}{m}\right\};
   \]

2. in the canonical saturated arm the mass, gain, and debt ratios satisfy an
   exact proportionality, not only upper bounds by one half.

Neither strengthening supplies the missing chronological consumer.

## 1. Fixed-density identity on the raw orbit

Fix the singleton owner `j` and the forced outsider `o`, and put

\[
\Delta=r_o(\{j,o\})-r_o(\{j\})>0.
\]

At every base row, the source and target profiles agree before the marked
date.  At that date their pure roots are respectively `\{j\}` and
`\{j,o\}`.  Both roots absorb surely, so the common post-date tail is
unreachable in both profiles.  If `L_n` is the reached live mass, then

\[
M_n=L_n,
\qquad
G_n=L_n\Delta.
\tag{1}
\]

This is an exact behavioral-profile payoff calculation and is independent of
stationarity, cap attainment, and the choice of continuation.

The checked declarations

```text
pureSingleton_stageMass_eq_liveMass
forcedPair_stageMass_eq_liveMass
forcedAction_eq_true
sourceToTargetGain_eq_liveMass_mul_defect
```

give the same formal route.  At the pure singleton source row, the forced
owner's coordinate defect is the positive part of `Delta`; because
`Delta >= terminalGap > 0`, it is exactly `Delta`.

A common root word of survival `c` scales both coordinates by `c`, by

```text
rawDecoration_markedMass_eq_prefixSurvival_mul
rawDecoration_actualGain_eq_prefixSurvival_mul.
```

Thus every raw decoration has `G=Delta M`.  Since `G-Delta M` is continuous,
its zero set is closed and contains the raw prefix orbit.  It contains the
closure `prefixOrbitCarrier`.  Equation (6) in the note is correct.

The selected passport limit belongs to this same carrier.  Hence

\[
g=\frac{G_P}{2D_P}
 =\Delta\frac{M_P}{2D_P}=\Delta m.
\]

For every carrier point `X`, positivity of `Delta` gives

\[
gD(X)\le G(X)
\quad\Longleftrightarrow\quad
mD(X)\le M(X).
\]

Therefore the generic two-density normalized slice is literally equal to the
single mass-density slice in this Fin4 source specialization.  No division by
`M(X)` or `G(X)` is involved, so this remains true at zero-mass boundary
points.

## 2. Exact prefix feasibility

Let `Q` be the selected slice minimizer and write

\[
D=D(Q),\quad M=M(Q),\quad s=M-mD\ge0.
\]

The canonical densities give `m>0`; the strict inert arm gives
`D>D_*>0`; hence

\[
mD>0,\qquad M>0. \tag{2}
\]

For an arbitrary product root, let

\[
c=\operatorname{Cont}(q),\qquad a=1-c,
\qquad R=\operatorname{Defect}(q;B(Q)).
\]

The checked prefix map preserves the decorated tail and the closed carrier,
and its exact ledger is

\[
D'=cD+R,\qquad M'=cM,\qquad G'=cG.
\]

The tail-equality field of the slice is therefore automatic after prefixing.
The gain inequality is equivalent to the mass inequality by Section 1.  The
only remaining test is

\[
m(cD+R)\le cM.
\]

Using `M=mD+s`, this is exactly

\[
\boxed{mR\le cs}. \tag{3}
\]

Thus the "if and only if" is valid, including `c=0`, `s=0`, and `R=0`.

Whenever (3) holds, `q*Q` is a candidate in the same slice.  Minimality and
the ledger give

\[
D\le cD+R,
\qquad\text{hence}\qquad
\boxed{R\ge aD}. \tag{4}
\]

This argument does not require `q` to be cap--Nash.

## 3. Slack-radius toll and all edge cases

Assume `s>0` and `a<=s/M`.  If `R<aD`, positivity of `m` gives

\[
mR<maD.
\]

The absorption hypothesis is equivalent to

\[
a(mD+s)=aM\le s,
\]

and therefore

\[
maD\le(1-a)s=cs.
\]

Thus (3) holds, while the prefixed debt is strictly less than `D`, contrary
to minimality.  Equation (17) is correct.

The boundary cases in the note are also correct:

- `a=0`: the conclusion is only `R>=0`, true for total root Nash defect;
- `c=0`: then `a=1`, but `s/M<1` by (2), so the hypothesis
  `a<=s/M` is impossible;
- `s=0`: this is precisely the saturation arm, so no positive radius is
  claimed;
- `M=0` cannot occur by (2), so the displayed radius is defined;
- a sequence `q_n -> allContinue` has `a_n -> 0`; if `s>0`, positive
  absorptions eventually enter the fixed radius and satisfy
  `R_n/a_n >= D>0`, excluding a sublinear ratio.

## 4. Stronger global root toll

The exact feasibility criterion gives more than the small-radius statement.
For every root, either (3) holds or it fails.

- If it holds, (4) gives `R>=aD`.
- If it fails, `mR>cs`, hence `R>cs/m`.

Consequently every root in the slack arm satisfies

\[
\boxed{
R(q;B(Q))\ge
\min\left\{D(Q)\operatorname{Abs}(q),
\frac{\operatorname{Cont}(q)\,[M(Q)-mD(Q)]}{m}
\right\}.}
\tag{5}
\]

The two terms cross exactly at

\[
a=\frac{s}{M}.
\]

Thus (5) specializes to the note's linear toll for small absorption and adds
the complementary large-absorption feasibility toll.  At full absorption
`c=0`, the second term is zero, so the statement remains valid without a
spurious positive conclusion.

For Fin4, (17) also implies that every root inside the slack radius has some
coordinate Nash defect at least `aD/4`.  This is a quantitative
coordinate-level wall, though it is still not an executable chronology.

## 5. Canonical saturation

The passport limit `P` is in the normalized slice, so slice minimality gives

\[
D(Q)\le D_P.
\]

At saturation,

\[
M(Q)=mD(Q)=\frac{M_P}{2D_P}D(Q).
\]

Because all displayed denominators and numerators are positive, the sharper
identity is

\[
\boxed{
\frac{M(Q)}{M_P}
=\frac{G(Q)}{G_P}
=\frac{D(Q)}{2D_P}.}
\tag{6}
\]

The middle equality uses `G=Delta M` throughout the carrier.  Since
`D(Q)<=D_P`, equation (6) gives exactly the two half-loss inequalities in the
note.  It also records that neither marked mass nor actual gain vanishes at
the saturated strict-inert point.

## 6. Novelty against the checked modules

The named Lean modules contain all local identities needed for this proof but
not the combined result:

- `NormalizedPassportPrefixOrbit.lean` proves separate survival scaling of
  marked mass and actual gain.  It does not identify their ratio from the
  Fin4 forced-pair table gap or extend that identity to the carrier.
- `NormalizedPassportMinimizer.lean` proves the exact prefix debt ledger and
  unique all-Continue rigidity for exact cap--Nash roots.  It does not state
  the arbitrary-root feasibility equivalence (3), the linear toll (17), or
  the global toll (5).
- `FinFourProducerAtlas/NormalizedReturn.lean` defines two generic densities
  and uses both constraints.  It does not prove their redundancy for the
  actual forced singleton-to-pair family.
- `PaidNonexactCapStackAccount.lean` prices absorption using the global
  minimum and a historical semantic budget.  It does not give the local
  `D(Q)`-slope forced by normalized-slice slack at a fixed minimizer.

Thus equations (6), (18), and (23) of the note are mathematically new relative
to the named checked declarations, while remaining direct formalization
targets from those declarations.

## 7. Scope

The note correctly does not claim a terminal or renewable consumer.  The
root defect in (4)--(5) is an error paid at a proposed prefix, not prescribed
payoff charge on an admissible chronological edge.  Saturated mass can shrink
geometrically through repeated re-minimization, and the carrier minimizer need
not itself be an actual regenerated source.  The stronger formulas above do
not remove either obstruction.

## Addendum: audit of the density-to-zero trichotomy and barrier regression

The later Sections 5--6 of the author note also **PASS** adversarial audit.

Let `m_n=r_0/(n+2)` and

\[
u_n=\frac{m_nD_n}{M_n}\in(0,1].
\]

The positivity and upper bound are justified by `m_n>0`, `D_n>D_*>0`, and
slice feasibility `m_nD_n<=M_n`.  After compact subsequence selection there
are exhaustively two numerical cases:

- some subsequence has `u_n>=epsilon>0`; then
  `M_n=m_nD_n/u_n -> 0`, because `D_n` is bounded on the compact carrier;
- or a subsequence has `u_n->0`; then the slack radius is exactly
  `1-u_n->1`.

For each fixed root of absorption strictly below one, the latter radius
eventually contains the root, so the toll passes to the limit by continuity
of the cap coordinate, total root defect, and whole debt.  A root of
absorption one is correctly handled by independently mixing every marginal
with a positive Continue tremble: the perturbed roots have positive joint
Continue mass, converge to the original root, and a second continuity limit
gives the absorption-one case.  The quantifiers are in the valid order: the
subsequence and limit are fixed before choosing the arbitrary root.

If a limit has `D=D_*` and `M>0`, choosing

\[
m'=M/(2D_*),\qquad g'=\Delta m'
\]

makes that same point strictly feasible.  Global minimality makes it a
minimizer of the new positive-density slice, so the checked equality-arm
actualizer applies.  No attainment of the carrier point by one behavioral
profile is assumed in this step; the actualizer uses raw orbit convergence.

The exact regression

\[
r_i(S)=-\mathbf1_{i\in S}
\]

is also correct.  At the profile where only player `0` Quits immediately,
`U=(-1,0,0,0)`, `B=0`, and `D=1`.  Against cap zero, player `i`'s Quit
endpoint is `-1` and its Continue endpoint is zero, so its root defect is its
Quit probability `x_i`.  Therefore

\[
R=\sum_i x_i\ge1-\prod_i(1-x_i)=\operatorname{Abs}(q).
\]

All-Continue is the unique exact root, while all-Never is an exact terminal
Nash profile and the game's global minimum is zero.  This is a valid
regression for the barrier interface, with the limitation stated by the
author: it does not reproduce the positive-minimum forced-pair source.
