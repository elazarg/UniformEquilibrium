# Independent review of the cyclic joining-increment root region

PASS for [the cyclic joining-increment region](../notes/CODEX_COORDINATOR__CYCLIC_JOINING_CAP_REGION.md), SHA256
`04af8b1b81373718d2f9f029e7d77dfe346f8a58780d7f7893efacd6d75b0810`.

I independently reread and checked the whole final artifact, including its
general n>=3 hypotheses, its M14 specialization, and its source consumer.

- With own singleton zero, native root differences give exactly
  `C(x)=Lx-R(x)`, with L formed from the singleton joining increments and
  R from the negated higher joining increments. Arbitrary passive rewards
  introduce no extra sign requirement.
  Every proper positive support has an active owner with its premium
  predecessor missing, contradicting positive continuation. The sure-owner
  argument covers arbitrary other hazards and arbitrary continuation:
  nonsuccessors of a sure owner strictly Continue because every possible
  opponent coalition containing that sure owner has negative joining
  increment. Its successor surely Quits, and the first sure owner strictly
  improves by withdrawing. The last step uses n>=3; the argument correctly
  does not include reciprocal two-player cycles.
- Exact rational recomputation confirms the M14 L and positive inverse A,
  the determinant polynomial, both isolating endpoint values, row/column
  sums, the `539/32768` box, and all bounds used at the uniform fold.
- Supersolutions and least roots follow by bounded monotone iteration.
  The second existential supersolution test is equivalent as an existence
  statement, without requiring L to preserve coordinatewise inequalities.
  Holder applies to positive monomials of F_v(x)/x_i and proves log convexity.
  The general explicit box uses h=A1 and the valid inequality
  `R_i(s h)<=s^2 R_i(h)` for 0<s<=1. The general ratio bound
  `min x >= (min A/max A) max x` and all positive quadratic coefficients
  give precisely `X <= 1/[n*binom(n-1,2)*amin*c*kappa^2]`.
  This gives relative closedness and boundedness of D, including n=3.
- At a minimal root, Perron radius greater than one would produce a
  strictly smaller supersolution. Radius less than one gives a regular
  positive branch. Radius one excludes every strictly increased positive
  target by the left Perron vector and convexity along nonnegative
  directions. These arguments prove both directions of the boundary
  criterion and every claimed part of the radial partition. For two
  distinct ordered positive fixed points, the difference is strictly
  positive because A>0 and DR has positive off-diagonal entries. Strict
  Taylor expansion then proves uniqueness at every critical target,
  proves that every nonminimal root has Perron radius greater than one,
  and justifies the direct finite parametrization of the boundary.
- The critical Perron eigenvalue is simple; the Hessian pairing is strictly
  negative and positive target directions are transverse. Thus the asserted
  local fold is nondegenerate for all n>=3; a positive quadratic monomial
  in each R_i makes the Hessian pairing strict. The M14 uniform fold has
  Perron radius exactly one, and the general nonminimal-root and uniqueness
  criteria apply to it. The two A-transformed comparison cones follow
  exactly as stated, including nonzero forcing that has zero coordinates.
- The fold's positive current payoff is
  `(3s-15s^2-5s^3)/(1+s)^3`, correctly distinguished from continuation v*.
- The R=0 countercontrol is a consistent raw table: passive nonsingleton
  rewards and all larger participant rewards vanish, while participant
  pairs equal L. All higher increments are therefore zero, C=Lx, and
  x=Av is positive for every positive v. It correctly shows that allowing
  all higher increments to vanish destroys boundedness and the fold.
- For the source consumer, the nonzero root is fully mixed and is selected
  at full cap B. Its current full response cap is the root's indifference
  value T. The actual prescribed payoff loses exactly
  `c(B_i-U_i)`, where c is the joint Continue probability, so every full debt
  and the Never product scale by the same c in (0,1). This proves strict
  objective improvement for any selected pivot on the expressly assumed
  prefix-closed carrier. The general conclusion is B outside D; the v*,
  539/32768, and four transformed-coordinate restrictions are explicitly
  confined to the M14 specialization.
  The proof neither substitutes prescribed U for cap B in selecting the
  root nor claims admissibility inside an inherited fixed-cap fibre.

No unresolved mathematical objection. This is ordinary mathematics, not a
formal verification or a solution of the benchmark's UE problem. The scope
restrictions in the reviewed artifact are necessary and are stated clearly.
