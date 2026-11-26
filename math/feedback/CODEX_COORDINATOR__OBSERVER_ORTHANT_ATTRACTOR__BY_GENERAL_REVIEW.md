# Independent whole review of the canonical observer attractor

Reviewer: RAW_ENTRY. I did not author the joining classification or the
canonical local-attractor proof. This review covers the entire canonical
`math/notes/CODEX_COORDINATOR__OBSERVER_ORTHANT_ATTRACTOR.md`, with its final
SHA256 recorded below.

Verdict: **PASS as ordinary mathematics: a local strategy-producing theorem,
sharp first-order joining classification, and fourth-player local corollary.**
There is no unresolved mathematical objection. This is not a UE theorem or
an export admission: entry and a recurrent absorbing construction remain open.

## Scope of the whole-proof check

I independently recomputed d=-1^T G^-1 and its sign equivalence with
hil-gjk>0. All explicit delta and epsilon bounds have positive right sides
under the five strict raw inequalities. The new mu lies strictly between
l/F and min(1,k/E), so both drift coefficients are positive without the
removed participant-pair sign restrictions.

The scalar root selector supplies the strategic roots from raw data. Its
signed denominators stay positive, z decreases, a increases, and f increases
strictly. The two endpoint signs follow exactly from failure of the explicit
face test. The odds bounds hold over the entire search interval. At an
interior seed every small proper root must have a,t>0, hence support01 or013;
the face equations or scalar equation then prove uniqueness. This argument
correctly excludes sure roots and does not claim uniqueness at boundary
seeds, where the displayed solo3 alternative is real.

I checked each exact sign identity in the assembled proof. The new N0
estimate follows from the full-root inequalities for a,z: subtracting
CF/(DE) from R_delta gives numerator
F*delta*(E|r1|+C|r3|) over D*E*(E-|r3|delta), yielding Q*delta. The K0
remainder is controlled by t<=delta and z/t<=R_delta. The face case gives
N0=-(A+g)t directly. For N1, the two exact coefficients are C-i and
jC-iD with the stated signed higher-order corrections. For N3,
w>=max(C3,0)>=mu*C3 is valid for both signs of C3; the a*t error is bounded
by delta(a+t)/2. Thus all signs used in the Lyapunov proof are justified.

The exact signed Lyapunov identity gives V'<=V-(a+t+z)/2. It both preserves
the smallness domain and proves summable odds. Active equalities imply S,u
converge to zero. The stated absolute-increment bound makes w convergent;
a positive limit would force the01 face forever and then
S'=(A+g)S/(A+S)>S near zero, a contradiction. The full finite-word
payoff/cap/survival tuple converges. Its fixed-seed closure interpretation
uses finite prefixes and does not execute a tail after infinitely many dates.
All marginal survivals remain positive, as explicitly stated.

The fourth-player argument is independent of its own Nash assertion:
passive updates first bound |beta| by B, summable odds bound total pivot
drift by bmin/4, and the additional delta bound makes every joining offer
at most bmin/4. Hence beta>=3bmin/4 strictly prices every pivot comparison.
This is not circular. The same finite-word closure then retains all four
full behavioral caps, and no actual continuation is assumed at the seed.

## Sharpness and attempted falsification

I recomputed the three generating rays of the first-order full-root cone.
Evaluation of its linear output numerators gives exactly the five weak
inequalities. On the01 face, minimizing
max(0,Ft-Ea)+ka-lt on either side of a/t=F/E gives F>=l and kF>=lE;
C>=i is the remaining face test, and N0 is already negative. Thus no
unexamined face enlarges the claimed closed region.

Every strict violated ray can be perturbed to positive a,t,z,u,w while
retaining the wrong output sign. Scaling gives interior seeds arbitrarily
near zero. For fixed arbitrary higher rewards, active0 forces t+z=O(tau),
active1 gives a=O(tau), and the normalized roots converge to the unique
linear root. Quadratic terms are O(tau^2), so the strict wrong sign persists.
The conclusion concerns every sufficiently small proper root, not only a
preferred selector; nonlocal and sure-root alternatives remain available.

I independently ran exact Fraction checks of all five rational examples:
only the named inequality fails; the listed active and quiet comparisons
hold; and the failed numerator is respectively -1/2,-1/2,-2/5,-3/20,7/4.
The enlarged-region example also passes all five strict inequalities while
J03,J13,J30 are simultaneously positive. This verifies an open enlargement
of the previous local theorem, including arbitrary finite higher rewards.

## Evidence and limits

I inspected the original canonical observer proof, the separate proposed
joining classification, and the diagonal prefix theorem in
UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean. The assembled
proof retains the original recursion, Lyapunov convergence, finite-word
semantics, and arbitrary-fourth-player argument; no lemma was lost in the
replacement of the joining inequalities. No new Lean build or formalized
claim is made.

The mathematical review does not depend on the availability of the linked
global-entry note. That separate obstruction is not a premise of the local
theorem. This packet supplies neither raw entry from positive pivot seeds
nor recurrence with survival tending to zero, and it closes no UE reward
class by itself.

Final canonical SHA256: 3993c8884e453d6749500ab04b9797852285cf95c451679fe63e6269a7d45da4.
