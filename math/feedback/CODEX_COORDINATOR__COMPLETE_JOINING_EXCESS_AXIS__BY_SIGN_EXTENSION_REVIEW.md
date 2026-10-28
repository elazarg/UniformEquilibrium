# Independent final review: signed reciprocal direct-return extension

Reviewer: GLOBAL_BLOCK_REVIEW. Date: 2026-10-28.
Artifact: `math/notes/CODEX_COORDINATOR__COMPLETE_JOINING_EXCESS_AXIS.md`.
SHA-256: `9a33917fe41b01bf7e593722ff4ede1d377c1fee58c831a9d65806505227d69b`.
Repository HEAD: `6b896ade6225e41d612de00d17c3dfb14fd81e30`.

**Verdict: PASS for internal retention; ordinary mathematics, not Lean-checked.**
I reread the complete retained note and its direct-return parent theorem.
Sections 1–3 retain their prior reviewed scope; this independent extension
review fully checks Section 4. No unresolved mathematical objection remains.

Replacing e>0,D>0 by e!=0,D!=0 and 0<x=e*b/D<1 is valid. The exact
row2 elimination identity was independently verified symbolically, with
its displayed minus sign and denominator. The retained C guard gives
k+s*b>0, and D*(D-e*b)=D^2*(1-x)>0. The row1 denominator stays positive
using only physical x and the retained guards. All remaining prefix,
wash, return and absorption arguments are independent of the signs of e,D.
The extension retains the nonzero-polynomial and all other raw hypotheses;
it introduces neither a simple-root condition nor an arbitrary-table claim.

For j<=0, arbitrary real h is valid with the revised prefix test. Its
piecewise endpoint u2 correctly encodes (1-a)X2>(h+c)a even when h+c<=0;
this replaces the original h-dependent interval endpoint. It ensures
Y2>c*a. The solo3 return interpolates between U and Y, so its quiet row2
values stay above min(T,Y2)>0 for either sign of h. Finite subdivision
therefore makes every c*q smaller than the current value. Quiet1's
nonnegative value beats its negative joining offer, quiet0 beats zeta0*q,
and owner3 is indifferent. The washed j>0 branch retains its original h>0.

For the H example, I independently verified the relabeling, the polynomial
-6*(7b-1)*(8b-1), and all displayed rational values. Exact symbolic coalition
enumeration checked the three Bellman transports, both joint-owner
indifferences, every solo-date margin, and both quiet joint comparisons.
The threshold (8) is exactly quiet1's nonnegative-margin condition;
equality is admissible. Quiet3's displayed nonpositive entries suffice.
The two entries Z1(01),Z1(012) are restricted through (8); the other
unspecified higher entries, including p, do not enter an executed comparison.
This example has an independently verified complete cap, not merely support
indifference or a stationary comparison.

Each deviator faces opponents-only absorption at least min(1/5,1/8)=1/8
per three-date period. Bounded Bellman unrolling therefore controls every
complete behavioral replacement, including Never, and identifies the actual
terminal values. Proper absorption under every deviation permits arbitrary
original own-level shifts kappa. The claimed 52R/T_horizon bound is the
terminal-versus-average payoff discrepancy, not the sum of both errors in
a direct regret comparison; its coefficient equals 2*(3/(1/8)+2)=52.
It yields the fixed original uniform-equilibrium payoff kappa+Y.

The result handles the specified higher-reward family on pointed witness3;
it does not cover arbitrary higher rewards on that singleton matrix or
separate this example from every earlier producer. Checks used exact SymPy
identities and rational coalition enumeration plus a full behavioral proof
audit. No Lean commands, tracked edits, or Git mutations were performed.
