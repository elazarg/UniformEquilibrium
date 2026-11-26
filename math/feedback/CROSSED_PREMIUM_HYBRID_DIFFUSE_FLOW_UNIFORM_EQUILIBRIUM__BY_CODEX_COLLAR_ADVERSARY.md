# Adversarial review of the crossed-premium hybrid producers

Reviewer: CODEX_COLLAR_ADVERSARY.
**Mathematical verdict: PASS. Export-gate verdict: PASS.** No mathematical
objection remains in the full producer or behavioral consumer. No other review
was read. This is ordinary mathematical review, not Lean verification.

Reviewed artifact: `/tmp/FIN4_BOTH_CROSSED_DIFFUSE_FLOW_CANDIDATE.md`, for promotion as
`math/exports/CROSSED_PREMIUM_HYBRID_DIFFUSE_FLOW_UNIFORM_EQUILIBRIUM.md`.
Exact SHA256:

    cb596121a3c8518a9c54eaec99faf14bda066a7095df41c8ec12f971869a19b4

## Exact accepted scope

With the displayed singleton matrix, seven passive entries, nine core
participant entries and row0 upper bounds, UE exists for small positive beta on

    U: 0<a<3, c>1, 2a<3c;
    L: a>3, 0<c<1;
    B: a=3, 0<c<1.

One positive threshold works on compact subsets of each stratum separately.
No uniformity across strata or their boundaries is asserted. In particular,
the finite-prefix bound on L may diverge as a approaches 3. Own levels and
unlisted nonsingleton entries are arbitrary finite numbers; beta0 is
independent of them. Mesh and horizon choices may depend on their magnitudes.
The target precedes accuracy; deviations replace entire behavioral laws.

## The obstacle core on U

I reproduced the spectral conjugation and dissipation identity. The active
cone maps strictly into the positive quadrant. With b=xi*FW/3=k-a/3,

    1-A11/r-xi*Q0/3
      =[5(c-1)/8+a/3-b*delta/r]/r
      >[(c-1)/16+a/3]/r>0,
    k*(1+delta/r)<r.

These preserve the derivative cone and contract P0*|Y|+Q0*|W| under A/r,
producing the leading graph in a closed homogeneous Lipschitz class.
Its outer map covers the full quadrant: at fixed u>0, W(Y) decreases and
v increases from a negative value to infinity; u=0 is exactly W=G=0.
The determinant and inverse estimates hold as finite difference bounds.

The exact pair identity and quiet2 guard check; 2a<3c preserves legality.
The exact contact factor K_beta(s,0)=b_beta(s)*f_beta(s), b_beta>0, removes
additive boundary error. The negative Y dissipation and |s|<=C(f_beta+Y)
absorb Taylor errors uniformly on a compact.

The scalar implicit root is unique and preserves the enlarged derivative
cone. The a.e. chain rule is valid: its base map is a small Lipschitz
perturbation of beta*A, which is invertible for a>0, hence locally
bi-Lipschitz. Weighted contraction produces the exact Lipschitz graph.
Its scalar outer inverse has slope at least 1-xi*Q1/3-o(1)>0.
A legal pair output lies on the stopped graph: Psi>=tcrit gives nonnegative
virtual critical height, f_beta<=0 and G_beta=0; scalar uniqueness applies.
The pair and triple selections agree exactly at contact.

## The finite-sheet core on L

I independently derived the inverse recurrence. For its cone, the useful
exact slack is

    D0*v'/4-z'
      =A0*(3D0+4)u/8+D0^2*v/8+(D0/2+2/3)z>=0.

Together with D0*v>=2A0*u and z<=3D0*v/8, this gives z'>=0,
v'>=2v and u'<=(1-A0)u-D0*v. The initial ray has
D0*R0/(2A0)=a/(3c)>1. Consecutive outer slopes are strictly ordered until
u crosses zero in finitely many steps, uniformly on parameter compacts.
The first negative-u ray still has v,z>=0. Truncating its wedge at u=0
covers all remaining nonnegative outer ratios; w=(u+z)/3 stays nonnegative.

Consecutive seam rays span the needed pulled-back pair planes, with
nonsingular outer projection. Three consecutive rays are independent,
because e_(-1),e0 are distinct in z=0 and e1 has positive z. Thus every
required adjacent intersection is transverse. A seam landing exactly at
u=0 is handled by one further virtual sheet. The unused final E_(N+1)
need not be a nonvertical graph; only its transverse intersection is used.

Normalized forward iterates F_beta^n/beta^n extend analytically through beta=0,
producing exact sheets on a common domain without unbounded inverse iterates.
The exact contact tangent is (a-3)(2+c beta)/[3(1-c)(3+a beta)]. Ordered
seams persist, and the map sends each physical sector to the preceding one.
On the first triple sheet, exact factorization at contact preserves z>=0;
later sheets have strict positive hazard margins. The terminal pair sector
is invariant. This proves finite descent to actual legal pair roots.

Outside that sector the pair guard is negative, so tcrit>Psi. Monotonicity
of the virtual input t in z and physical z>=0 give T>=Psi exactly. Shared
seams select identical roots. Finite analytic sheets give the Lipschitz bound
and continuous parameter dependence within L; no limit as a tends to 3 is used.

## The analytic boundary core on B

I checked the left normal, solo axis, transverse margins and factorization

    (X-1)[8X^2+(5c+3)X-6c].

The normal is (-1/3,1,-B), with B=(1+2r)/(c+2r)>1. The holomorphic graph
transform contracts in the quadratic norm: its difference bounds are
O(radius), O(beta), and O(beta*radius^2). Division by beta is removable;
Cauchy estimates give common C2 and parameter bounds on each compact c-set.
No dominance over the positive eigenvalues is required.

The exact invariant solo3 axis is preserved by every graph-transform
iterate, hence T_beta(u,0)=u/3. Both T-tcrit and T-Psi vanish identically
there. Their transverse slopes are respectively

    (1-c)[1/(c+2r)-beta/(2+c beta)],
    (1-c)/(c+2r).

Uniform positivity on compact c-sets and C2 bounds give T-tcrit>=kappa*v
and T-Psi>=kappa*v up to the axis. Monotone inversion yields positive
triple hazards for v>0 and the exact solo3 root for v=0. The zero-hazard
owners satisfy indifference on that axis. Every output stays physical
and on the graph. All three cores have geometrically summable hazards,
legal passive0 guards and continuous positive axis limits p+O(u+v).

## Ribbon return and complete behavioral consumer

I reproduced both positive-beta complementarity factorizations, including
the pair-slack correction. Their maximum gives v>=0, alpha>=0, alpha*v=0.
The three-flow identities and segment nonnegativity check. Flow3 has owner
cap zero when present and is omitted when alpha=0.

Independent exact arithmetic reproduced every return factor, corner identity,
root-isolation sign, Bernstein bound and endpoint fraction. The blended
transverse return derivative is negative on the direct arc and on both
branches near its corner. Pair slack does not change the beta0 return.
Thus a fixed physical ribbon has opposite return signs on its transverse
faces; uniform C0 axis convergence preserves them without any axis derivative.

Choose the finite pair slack from the graph upper bound before shrinking
beta. It gives positive entry residual on the full pair endpoint face.
The other endpoint is strictly negative from T>=u/3+v: on U use D-V<0
and c>1; on L and B use D-U=-z_L*(1-w_L)/2<0 and a>=3.
Both signs persist on complete endpoint faces. The clipping/Brouwer argument
has the correct inward signs and produces a simultaneous zero without any
assumption that the return zero set is connected or admits a continuous
selection. The auxiliary axis projection equals actual output at that zero.

The macro0 guard retains 257/500<3/5; pair quiet2 slack is beta*sigma.
The complete query census puts free entries only in solo-flow unilateral pair
payoffs and mesh constants, so they do not affect beta0.

Finite meshes preserve all endpoints and Continue equations. Their Quit
error eta_n is charged once, since a deviator quits at most once while live.
The periodic word has one seam with defect E_N tending to zero. Every full
deviation faces opponent absorption at least x per word, so expected seam
visits are at most 1/x. Telescoping gives payoff error E_N/x and unrestricted
exploitability eta_n+2E_N/x. Surviving remainders vanish. The return and target
are fixed before N and the mesh. Expected absorption time at most word-length/x
gives the uniform finite-horizon estimate. Absorption is almost sure under
every replacement, justifying arbitrary own-level translation without shifting
literal Never or live rewards. No infinite chronological wash is executed.

## Nonredundancy and export gate

All three directions (1/10,2), (4,1/2), (3,1/2) are within the calibration
box at their printed beta bounds, further restricted by the existence
threshold. They fail the prior premium constructions as stated: in particular
L and B fail the lower diffuse a<3 condition, the pair test e<=h3, and the
cone inequality 8a<15(1-c). The role census leaves only the identity;
positive row rescaling does not rescue the relevant normalized criteria.

I checked every stationary and sure-owner support, including all feasible
punishment tails; every protected-set and nonnegative-weight selection;
and all fourteen proper children with full behavioral debts. Principal minors,
LCP support census, inverse-triple tests and all nondiscrete quotient tests
also check. The child comparison excludes the universal child-debt consumer,
not a method selecting a favorable child profile.

Nine cited Lean files are tracked; twelve declarations and their imports were
inspected statically and match their uses. No Lean command ran. The packet is
self-contained and produces every graph, root, continuation, return, flow and
profile from raw rewards. No strategic input remains assumed. It proves UE
on previously surviving classes and passes the export gate. The new producer
is ordinary mathematics; arbitrary Fin4 remains open.
