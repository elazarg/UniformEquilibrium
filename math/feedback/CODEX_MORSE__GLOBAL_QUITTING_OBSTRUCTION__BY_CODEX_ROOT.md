# Scope check for the whole-payoff-set nonconvexity example

Reviewer: CODEX_ROOT. Preliminary scope check, not an independent export
review or a verification of the complete JF proof.

## Claim being checked

The jump–flow attempt claims a nonconvex full uniform-equilibrium payoff
set even for an all-own-zero Fin4 table whose singleton matrix is R₀,
Standard Q, has degree one and a strictly positive simplex image, and
has strict column preemptors. It distinguishes the grand-only model
in JF1–JF4 from the separate screened perturbation in JF5.

## Exact scope mismatch in the displayed fixture

Every singleton reward in every recipient row is zero. Consequently its
centered singleton matrix Γ is the zero matrix.

- Γλ=0 for every probability vector λ, so there is no strictly positive
  simplex image and no strict column preemptor.
- The homogeneous complementarity problem has every nonnegative vector
  as a solution, so Γ is not R₀.
- At offset −1 the residual is identically −1, so its complementarity
  problem has no solution and Γ is not Standard Q.

Thus the grand-only fixture alone cannot establish the stronger screened
headline. That limitation remains exact; it must not be hidden by
identifying the two tables.

The grand-only example is not a positive-gap game: it has explicit exact
equilibria. A barrier for a payoff window must remain distinct from a
positive exploitability floor over every profile.

## Review boundary

JF5 supplies a distinct complete table with singleton matrix
λ·circulant(0,99,99,−1), pair and triple rewards zero, and grand reward
one. It gives two literal equilibrium endpoints and transports the
grand-only target-window bound using a uniform whole-table perturbation
estimate. This supplies the missing scope argument; the objection that
the screened claim relies only on Γ=0 is resolved.

No objection here is asserted against the proposed grand-only payoff
classification itself. This check does not independently verify that
classification, the full complementarity census for the perturbation,
the quantitative midpoint bounds, or the jump–flow pruning. Those are
separate claims. No full-conjecture or export seal is given.
