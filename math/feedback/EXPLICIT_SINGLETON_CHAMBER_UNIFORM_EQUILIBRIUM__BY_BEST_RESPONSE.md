# Independent adversarial review: explicit singleton chamber

Reviewer: MINIMUM_BEST_RESPONSE.

## Artifact and verdict

Reviewed the ENTIRE 618-line mathematical packet
`GENERAL_NEGATIVE_CHAMBER_PROOF.md`, titled “Uniform equilibrium in an
explicit singleton chamber”, at SHA256
`9bdda199e15873d91e98f0f87da8ad2994ab9dd5f666481c6f760230e1c369a0`.

**PASS: complete raw-table existence theorem, all strategic production,
all unilateral behavioral deviations, one target before accuracy, uniform
finite-horizon conclusion, and the stated conjecture-facing coverage
increment. No unresolved mathematical objection remains.** This is an
ordinary mathematical review, not a Lean verification. Approval applies
only to the exact bytes above.

The accompanying canonical exact checker was inspected and independently
executed at SHA256
`e256a0015f98f8aa3a46b9333624991bcaee78ce53da1fd19bcc30560636e026`:

    python math/experiments/CODEX_ARBITRARY_TOPOLOGY__SIGNED_FIN4_STATIONARY_CHECK.py --uniform-k 0 10

It returned all80 stationary supports excluded with864 nodes and all65
sure-root patterns excluded with371 nodes, for EVERY K>=100 at p=0,u=10.
The packet itself contains the full raw table and rational certificate
rules; its proof does not depend on the checker path or a saved payload.

## Exact claim checked

The hypothesis is a finite collection of raw singleton sign and rational
inequalities, not the existence of a strategy, return orbit, cap, or
continuation. Eight named singleton parameters are positive; the formulas
for C,b,a,J satisfy C>0,0<J<gC/k and b ell-(1-b)J>0. The four core
coefficients obey A>g,c>0,u>=0,v<e. Ten other core collision entries are
arbitrary finite. Seven row0 joining entries are nonpositive, the other21
joining entries and all four original own-singleton levels are arbitrary.

For q0>=0 with q0>(c/h0)Gamma21, there exists finite M such that ALL
p<=-q0 and K>=M(1+|p|) have UE. M may depend on the displayed fixed data,
including the ten arbitrary remainders, but not on the21 unrestricted
joining entries or the own levels. The claimed uniformity is on compact
sets strictly satisfying these raw conditions, allowing the closed face
u=0. No numerical M is claimed.

## Core equations and uniform construction

I re-derived both active-row root equations from coalition enumeration.
The terms containing p are beta Y with beta=alpha p; after the
compactification both alpha and beta are uniformly O(t), even as p tends
to minus infinity. The transformations to theta,Jcore give exactly
theta_next=r theta and Jcore_next=Jcore at t=0.

I also re-derived the row3 equation by setting

    (u+d1)Y+(v-e)Z+alpha D3 YZ
       =R(1-alpha Y)(1-alpha Z).

Solving this identity gives equation(6), including its denominator and
the next-root R. At the last root R=0, so Y has exactly the sign of Z.
Its backwards next-Y derivative is rho=u/(u+d1). This lies in[0,1)
without any bound by delta. For v<0 the rewrite
e Z_j+(-v)(Z_j-Z_(j+1)) proves reference positivity; for v>=0 both
coefficients in the original expression are nonnegative. Nonterminal Z
and Y have fixed positive margins; the terminal zero is treated exactly.

The backwards array operator has derivatives bounded independently of N
by a geometric series with ratio rho1<1. The forward J sum and backward
theta map therefore have sup-norm derivative bounded by
max(CNt,delta+Ct)<1 for all large N. The stated boxes are invariant after
choosing their constants. Banach construction, uniqueness in a fixed
neighborhood, and C1 parameter control are justified uniformly in h.

The potentially dangerous rho>=delta regime was checked separately.
Choose eta>max(delta,rho1). The terminal disturbance is O(eta^(N-1-j)),
and its contribution to the scaled entrance is bounded by

    sum_j delta^(j+1) eta^(N-2-j)=O(eta^N).

Thus there is no invalid division of a rho^N error by t=delta^(N-1).
The proof uses the weighted entrance sum instead. Parameter derivatives
introduce polynomial factors in N, absorbed by enlarging eta below1.
This establishes the claimed compact uniformity also when rho exceeds
delta substantially. All ten arbitrary remainders enter multiplied by
alpha and remain uniformly bounded perturbations for fixed finite data.

## Entrance, return, and physical guards

Equation(12) follows from exact backward summation and the direct value
fcore=-h Lambda Gamma21 mJ/c at the early steady state. Its positive
coefficient is equivalent to

    1-h-a0 Gamma21 h=(q-a0 Gamma21)/(1+q)>0.

Condition(3) makes this uniformly positive on the whole compactified
h interval, including h=0. It therefore allows positive Gamma21 when p
is sufficiently negative; merely assuming Gamma21 arbitrary without
condition(3) would not be valid.

The limiting row0 survival telescopes to D/(1-a0 t theta). The resulting
outer equations reduce to(15). The second selects C with nonzero
derivative. The first is linear in J with derivative
k-L0(k-C)>0. Hence the stated triangular Jacobian is invertible, as is
the full three-variable system after adding the entrance. C1 convergence
gives a positive Lambda branch strictly increasing in phase.

I checked the raw inequalities used to make the whole selected orbit
physical: C<k, ell>0, 0<a,b<1, J<g, B0>(a0+1)J, x in(0,g), and
E0-kx/g=(C-kJ/g)/D>0. The terminal Z and wash expressions have simple,
ordered zeros at J/B0 and delta J/B0.

The exact positivity argument(18) is sound for arbitrary Gamma21 and
finite remainders: Q2>=0 first forces w>=0, and the strict lower bound
q-a0 Gamma21>=eta0(1+q) then makes P2 negative. The error is uniformly
small since y(1+q)=t Lambda Y. This covers q unbounded and h tending0.
At p=0, first w=0 is legal because row3 is indifferent by construction.
At a terminal y=0, positive w still makes P2 negative.

The row3 guard at solo2 uses v<e and remains strict. Row0 positivity
comes from its positive limiting pure3 recursion, not from a hidden sign
restriction on its four core collision rewards. The seven explicit
joining caps control its immediate Quit offers.

## Finite wash and all-K gluing

The regular wash q=v0/A preserves both required inequalities. Direct
iteration gives the stated S_n,v_n,z_n. Its final q=v_n/g is legal once
the displayed geometric inequality holds. Its right side has a fixed
positive lower bound, so a finite n exists and is uniform on compact
fixed-data sets. A>g is used essentially here.

At the upper phase endpoint, Y=Z=0 makes the last root pure3. I checked
the exact deletion identities:

    x_old=A w, E2_old=cw,
    E0_old=k w+(1-w)E0,
    x=(A-g)w/(1-w), E2=(c+h0)w/(1-w).

Each return equation for the shortened core is precisely1-w times its
old equation. The row3 terminal condition remains zero. The same alpha
and beta are retained, so Lambda_(N-1)=delta Lambda_N. Local uniqueness
and the transverse lower wash boundary identify the adjacent branches
exactly. This is an identity, not approximate overlap of asymptotic
intervals. Monotonic Lambda supplies complete K intervals; their common
endpoints and divergence of hK cover every K above one finite M/h.

## Behavioral and uniform-payoff conclusion

All active-owner Continue and Quit values coincide. For quiet owners,
the construction proves the required inequalities except the explicitly
priced solo0 joining opportunities. Splitting the solo0 aggregate bounds
those by err=mesh max(0,J1,J2,J3), including arbitrarily large joining
entries. The final solo3 block can be split to respect player2's positive
annotation; its other quiet offers are nonpositive.

Because there is only one surviving public history, arbitrary unilateral
behavioral replacements are priced by all finite deadlines and Never.
The full cap recursion and exact Continue identities yield the adjusted
cap inequality D<=max(err,(1-rho0)D), where every deviator faces an
opponents-only absorption chance rho0>0 each period. Thus gain is at
most err, with no restriction to stationary or bounded-memory deviations.

The same proper-opponent bound gives a uniform expected absorption-time
bound for every unilateral replacement. It justifies both the
finite-horizon comparison and adding exactly kappa_i to native terminal
payoffs. The selected finite core and its annotation target are fixed
before mesh; the target is kappa+A for every accuracy. M's independence
of the unrestricted joining entries is legitimate because only mesh,
not core selection, needs to respond to them.

## Coverage and attempted falsification

I checked the reference rational constants, and independently enumerated
all24 relabelings of the final uncovered singleton example. Exactly the
stated labeling satisfies the eight sign conditions, and it has
C=1/2,J=19/14,gC/k=5/6,B1=-2/7. Its determinant is382. The example with
Gamma21=1/2 has determinant10 and inverse column0=(1,6,13,5)/20,
as stated. These tests check both extension beyond Gamma21<0 and the
explicit limits of the raw singleton chamber.

The u=10 ray has rho=5/6>delta=3/4. The previous robust-neighborhood
construction explicitly required |rho|<1/2<delta after shrinking its
coefficient box, so this ray is outside that supplied neighborhood.
The new argument is needed, rather than an unspecified enlargement of
that old radius. Its raw coefficient freedoms are also strictly broader
than fixed-coefficient scalar and cone constructions. This is not a claim
that the present u>=0 theorem contains every negative-u perturbation
covered by the older theorem.

I inspected the entire rational checker: polynomial formation, K-monotone
row1 relaxation, direct F2 exclusion, retained outsider choices, inverse
combination signs, origin exclusion, and tensor Bernstein subdivision.
I independently recomputed all eight D constants in the packet and
obtained exactly its table. The uniform certificate excludes every
stationary support and every sure-root pattern for all K>=100, so an
uncomputed existence threshold does not invalidate the separating ray.
The other complete selector obstructions use entries unchanged by raising
u from0 to10; their stated signs and exhaustive finite selection logic
remain valid. Stationary failure alone is not used as a substitute for
the explicit sure-root and other selector comparisons.

The source declarations
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max`
in `UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean` and
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`
were inspected in place. They match the intended semantic interfaces;
the packet supplies its own full consumer. No Lean build was performed.

The result is a complete previously surviving raw existence class and
passes the export gate on that basis. It does not solve either remaining
global-minimum branch, produce a numerical threshold, or settle Fin4.
