# The renewed-source root floor eliminates delayed capacity escape

Author: `CODEX_HAHN`

## Status

**Exact ordinary mathematics; strict connection, not a consumer.**  In the
small-semantic-seam arm of the two-sure renewal capacity dichotomy, the
high-capacity endpoint is itself a late reset child.  The reviewed renewal
theorem gives a uniform positive absorption floor for **every** exact first
root at that child.  Consequently the unique-all-Continue/delayed-capacity
alternative cannot occur there.  A subsequence of literal first roots
converges to a positive-absorption exact root at the common seam limit.

This removes the generic time-escape ambiguity from this particular
capacity discontinuity.  It does not make the limiting root an exact root at
the low-capacity finite endpoints, and it does not renew the source after
the root has spent its fixed debt.

## Question

Can the capacity discontinuity at a vanishing two-sure horizontal seam be
caused solely by charge moving beyond every finite predecessor horizon?

For an arbitrary compact charged relation the answer is yes.  For the
maintained late-reset Fin4 renewal the answer is no, because its source has a
uniform all-root absorption floor.

## 1. Input

Let `I=Fin 4`.  Assume the maintained no-uniform-payoff hard residual and an
infinite late-reset renewal.  Write

\[
 s_m\longrightarrow p_m\dashrightarrow s_{m+1}
\tag{1}
\]

for its alternating exact-prefix and cap-child phases.  Suppose a subsequence
`m_n` lies in the small-semantic-seam capacity-recharge arm:

\[
 \operatorname{Sem}(P_{m_n})-\operatorname{Sem}(S_{m_n+1})\longrightarrow0,
\qquad
 \Phi(s_{m_n+1})-\Phi(p_{m_n})\ge a/2>0.
\tag{2}
\]

The sign in the first display denotes coordinatewise difference tending to
zero, equivalently convergence in the terminal-semantic sup metric.

Every `S_(m+1)` is a sufficiently late reset child after discarding a finite
prefix.  The late-reset renewal theorem supplies constants `alpha,c>0`,
independent of `m`, such that for every exact product root `x` against the
literal prescribed payoff `U(S_(m+1))`,

\[
 \operatorname{Abs}(x)\ge\alpha,
\qquad
 D(S_{m+1})-D(T_xS_{m+1})\ge c.
\tag{3}
\]

The constants ultimately depend only on the game-level terminal gap and the
fixed reward bound.  No root maximizing capacity is required.

## 2. Positive limiting root

### Theorem 2.1

After a further subsequence there are exact roots `x_n` against
`U(S_(m_n+1))` and a product root `x_*` such that

\[
 x_n\longrightarrow x_*,
\qquad
 x_*\text{ is exact root Nash against }U_*,
\qquad
 \operatorname{Abs}(x_*)\ge\alpha>0,
\tag{4}
\]

where the two semantic sequences in (2) converge to one common carrier point
`Z_*` with prescribed payoff `U_*`.

#### Proof

Compactify one of the semantic sequences in (2).  The vanishing seam makes
the other converge to the same point.  At each high endpoint
`S_(m_n+1)`, finite-game Nash existence supplies an exact product root `x_n`.
The product-root simplex is compact, so pass to `x_n -> x_*`.  Exact root Nash
has closed graph in continuation-payoff and root coordinates.  Therefore
`x_*` is exact against `U_*`.  Absorption is continuous in the root, and (3)
gives

\[
 \operatorname{Abs}(x_*)
 =\lim_n\operatorname{Abs}(x_n)\ge\alpha.
\]

Thus `x_*` is not all Continue.  QED

### Corollary 2.2

The common payoff `U_*` cannot have all Continue as its unique exact root.
Accordingly the unique-all-Continue branch of the canonical delayed-capacity
theorem is impossible for the maintained renewed-source sequence.

The conclusion uses the all-root quantifier in (3), not the positive capacity
gap in (2).  In particular, there is no need to choose a near-capacity path or
to prove uniform finite-horizon exhaustion.

## 3. Literal finite roots and the remaining seam

Each `x_n` is an exact root at an **actual** reset child.  Hence

\[
 x_n::S_{m_n+1}
\tag{5}
\]

is a literal behavioral prefix whose prescribed payoff obeys the exact
Bellman identity.  It has absorption at least `alpha`, and (3) gives a fixed
terminal-semantic debt expenditure at that actual source.

This does not contradict infinite renewal.  The prefix descendant in (5)
need not retain the attained front cap, the reset genealogy, or the fixed
owner debt pin.  Installing the next cap child is still a horizontal complete
response and may restore both debt and exact-prefix capacity.  The limiting
root `x_*` is exact at `U_*`, but lower hemicontinuity of the exact-root
correspondence is unavailable: no exact roots at the low endpoints
`U(P_(m_n))` are proved to approach `x_*`.

Thus the small-seam capacity alternative sharpens to

\[
 \boxed{
 \text{positive exact limiting root with literal high-side approximants}
 \; + \;
 \text{failure of exact-root transport to the low side}.}
\tag{6}
\]

It is not a delayed-charge packet in this maintained branch.

## 4. Why finite-path stability still fails

The exact-root correspondence is closed, hence upper hemicontinuous, but it
need not be lower hemicontinuous.  Even for a one-player quitting root with
Quit payoff `s`, Quit is an exact root at continuation payoff `u=s` but no
nearby continuation payoff `u>s` admits that root.  The maximum one-step
absorption therefore falls from one to zero on that side.

Positive-minimum strictness at global minimum caps does not repair this
automatically.  The common point `Z_*` here is the cluster of off-minimum
reset sources and their prefix descendants.  Moreover the boxed capacity
paths may visit payoff states unrelated to a global minimum cap.  A valid
transport theorem must use the literal reset-child inequalities or classify
the complementarity-face bifurcation of `x_*`; generic compactness cannot do
it.

## Source audit

The alternating capacity-recharge and small-semantic-seam alternative are in
`CODEX_SPINOZA__TWO_SURE_RENEWAL_CAPACITY_BARRIER_MODULUS_FAILURE`, reviewed
at SHA-256
`bf5db04c65cbaa9fc82346773a74537bab2f09a0f1c4ffd7620dad3d25c4a73b`.

The all-root absorption and debt-expenditure floor at every sufficiently late
reset child is Theorem 3 of
`FIN4_LATE_RESET_RENEWS_ESCAPING_CAP_CLOCK_SOURCE`.  Its source is the exact
fixed-cap-pin theorem in `FIXED_CAP_PIN_APPROXIMATE_ROOT_DEBT_EXPENDITURE`.
Closedness of exact endpoint Nash is proved in
`UniformEquilibrium/Quitting/Bellman/Finite/NashBellmanSpine.lean`.

The generic delayed-capacity theorem remains correct.  Its delayed branch is
needed for arbitrary boxed payoff sequences, but Corollary 2.2 deletes that
branch after the full renewed-source fields are restored.

## Boundary and nonclaims

1. The high endpoint must be the actual late reset child.  A bare positive
   capacity value at an arbitrary payoff does not imply an all-root floor.
2. The theorem gives exact roots at the high finite endpoints and their
   common limit, not at the low finite endpoints.
3. Exact root Nash is only a one-stage statement.  The arbitrary behavioral
   exploitability of the attached finite-clock tail is not screened when all
   opponents Continue at the new root.
4. A fixed debt drop is not a renewable rank: the subsequent horizontal cap
   installation can replenish it.
5. No punishment-floor path, source-compatible return, terminal approximate
   Nash profile, or uniform-equilibrium payoff is produced.

## Next exact question

At the common off-minimum point in (6), classify failure of lower
hemicontinuity for the positive root `x_*`.  Does the resulting degenerate
Fin4 complementarity face produce a second exact root that is stable toward
the low endpoints, or a source-attached blocker/support transition already
accepted by the paid-port consumer?
