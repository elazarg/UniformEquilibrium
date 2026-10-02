# Hostile review of `EVENTUAL_CONSTANT_FORCED_PAIR_STALL`

Reviewer: `CODEX_RIEMANN`

## Claim reviewed

The note makes two separable claims:

1. if the autonomous maximum-absorption exact-cap prefix ray selects literal
   all-Continue once, it is thereafter a fixed, attained finite-clock point
   and all-Continue is the unique exact cap root there; and
2. the displayed rational Fin4 completion realizes the immediate forced-pair
   owner/payer pattern, unique all-Continue cap root, and every
   witness-independent structural field of the paired-singleton hard chamber,
   while all-Never gives debt zero.

I independently checked both arguments against the named source interfaces.

## Verdict

**PASS as a regression and formalization target, with one scope wording
qualification.**  It does not consume the strict ray and does not realize an
actual `FinFourQuantitativeFullSupportHardResidual`, because that structure's
`witness`, `massFloor_pos`, and `massFloor_le` fields are absent.  The note
already states this limitation near Proposition 4.4; it should remain explicit
in any exported/formalized version.

## 1. Autonomous fixation check

If the selected exact root is all-Continue, its absorption is zero.  Since the
selector maximizes absorption and absorption is nonnegative, every exact root
has absorption zero.  For a product root this forces every marginal Quit
probability to be zero, so the exact root is unique.

Literal all-Continue prefixing fixes the full terminal semantic pair, including
the unrestricted cap.  The autonomous selector therefore sees the same cap on
the next step and selects the same unique root.  The induction in Proposition
2.1 is valid.

The finite-attainment claim is also sound.  Before the displayed pure pair
there are only finitely many prefixed roots.  At the pair date, every
unilateral replacement leaves at least one sure quitter, so the tail is
unreachable even counterfactually.  An arbitrary behavioral deviation is a
distribution over finitely many effective stopping dates and its value is a
convex combination of the corresponding pure-time values.  Thus the cap is
attained by one of finitely many endpoints; no compactness or stationary-only
claim is used.

## 2. Reconstruction of the rational table

I reconstructed all fifteen reward rows from equations (11)--(15).  At
`C={0,1}` the result is exactly

\[
 U(C)=(1,4,1,2),\qquad B(C)=(3,4,2,2),
\]

and hence `d(C)=(2,0,1,0)`.  The owner comparison for player `1` is

\[
 r_1(\{0,1\})-r_1(\{0\})=4-3=1,
\]

with zero pair debt, and the payer comparison is

\[
 r_2(\{0,1,2\})-r_2(\{0,1\})=2-1=1.
\]

These labels and values are correct.

## 3. Unique-root proof

For cap `b=(3,4,2,2)`, direct expansion of Quit minus Continue gives exactly
the four polynomials in equation (20).  The proof uses only the valid Nash
implications

\[
 x_i>0\Rightarrow G_i\ge0,
 \qquad
 x_i=0\Rightarrow G_i\le0.
\]

The elimination is exhaustive:

* `x_0>0` forces `x_3>=2x_1`; the `x_3=0` subcase forces
  `x_1=0,x_2=1` and contradicts `G_1<=0`; the `x_3>0` subcase yields
  `x_3>=2x_1>=4x_0>=8x_3`;
* with `x_0=0`, positive `x_1` forces `x_3=0,x_2=1` and then contradicts
  `G_3<=0`;
* with `x_0=x_1=0`, positive `x_3` forces `x_2=1` and contradicts
  `G_0<=0`; and
* finally positive `x_2` gives `G_2=-2<0`.

Thus all four hazards vanish.  I found no missing boundary case.

## 4. Hard-field scope check

The singleton rows are exactly the checked `pairedSingletonMatrix`, so the
following claims really are inherited from the named paired-singleton
declarations:

* full normal core;
* `ResidualHardClass`;
* standard-Q/no-homogeneous/nonprojective-Q-bar singleton algebra.

Punishment normality is also valid: choosing all opponents Never makes the
player's best-reply value zero, equal to the diagonal singleton reward.

For uniform owner mass `1/4`, every row of the paired matrix has average
`1/4`; hence the mixture dominates the target zero.  Together with
punishment normality this constructs the claimed normalized singleton source
packet, with full support and mass `1/4`.

The precise limitation is structural, not a gap in these calculations:
`FinFourQuantitativeFullSupportHardResidual` includes a positive terminal-gap
witness, and its numerical mass-floor fields are defined using that witness.
The regression has all-Never as an exact terminal Nash profile, so those fields
cannot be supplied.  An integration theorem should therefore name the
witness-independent packet/matrix/normality conjunction rather than state that
the table inhabits the hard residual itself.

## 5. Conjecture-facing conclusion

The regression does what it claims: it refutes any attempt to eliminate an
eventual-constant forced-pair stall using only the local owner/payer data,
unique-root algebra, or singleton hard-class fields.  A successful consumer
must use positive global minimum provenance to control the horizontal
compensation `K_p`, or construct an executable return/descent.

