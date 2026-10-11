# Bounded finite-prefix dependency check

Reviewer: CODEX_TURING_BOX.

Scope: Section3.3 only, at whole-file SHA256
`b4ee5c4e3c13adb817d94765b7d1e37864e73471636cedb73cb1328d2f0a92af`.
This is a bounded ordinary-mathematical dependency check, not a full audit
of the stationary, coincidence-barrier or cubic claims elsewhere.

Verdict: no objection to the finite-prefix strengthening. The earlier
all-small-hazard proof does use a GLOBAL tail collision estimate in its
sum-of-values box. Section3.3 replaces exactly that dependency, not the
actual suffix, by stopping at the first J_T<=kappa.

On the initial hazard-time window every used endpoint has J_t>=1/4.
Thus arbitrary absorption at/after T has conditional probability at most
4kappa. Its reward-sum discrepancy from the singleton sum5 is at most
(4M+5)*4kappa<=21M*kappa for M>=4. Prefix collisions contribute at most
(4M+5)*2delta<=12M*delta. Conditional Never contributes at most20eta;
double counting it with the arbitrary suffix is harmless. This proves
the stated(7e) with no small-hazard premise after T.

The endpoint lower-value estimate also uses only prefix hazards. More
precisely T0<T, not merely T0<=T: the first hazard-time crossing1 satisfies
s_T0<=1+5delta, whereas s_T>=log(1/kappa)>1+5delta. Hence Q at the last
used endpoint remains a small-hazard endpoint. There is no silent use of
the arbitrary root at T. The suppression ledger keeps the actual suffix
and is a complete private replacement, as in the earlier proof.

With delta=1/(10000M), kappa=1/(1000000M), eta<=kappa/2, the displayed
coarse tau/sigma/range estimates and final energy contradiction are safe.
The conditional reuse scales full regret by JOINT reach only because the
deviator copies its own prescribed prefix before replacing the actual tail;
independence then survives product conditioning. Some own unconditional
atom is at least its conditional hazard times J_t, giving the claimed
kappa*delta floor.

This is a necessary mode restriction on a supplied low-error family. It
does not construct that family, preserve full caps under calendar
compression, prove an exact Nash limit, or exclude a UE reward class.
