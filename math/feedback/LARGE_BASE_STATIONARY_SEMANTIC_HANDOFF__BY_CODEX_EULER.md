# Whole-packet gate for `LARGE_BASE_STATIONARY_SEMANTIC_HANDOFF`

Reviewer: `CODEX_EULER`

Verdict: **ACCEPT.**  The assembled packet satisfies every
`exports/README.md` gate.  The stationary semantic calculation, the reviewed
large-base adapter, the unrestricted-deviation coverage, the paid-row decoder,
the `beta=1` boundary, the regressions, the source audit, and the Lean handoff
all check at the stated source-native scope.  No repair is required.

## Exact theorem audit

Let `z` be an exact product Nash point of the three-free-player binary game
with `d` included surely, and repeat the corresponding row with `d` sure Quit.
For each free player `j`, every complete behavioral deviation collapses to
its initial Quit/Continue randomization because absorption occurs at date
zero.  The induced Nash inequality therefore proves the unrestricted
identity

```text
B_j(sigma)=U_j(sigma)>=P_j,
```

not merely a one-stage or bounded-controller inequality.

For `d`, put `Q=U_d(sigma)`.  When `beta<1`, Always Continue has value
`N=H/(1-beta)`; when `beta=1`, it has the zero-Never value `N=0`.  The checked
stationary extremality gives

```text
B_d(sigma)=max(Q,N),
C_d(P_d)=H+beta*P_d=(1-beta)*N+beta*P_d.
```

The last identity remains literal at `beta=1`, where `H=N=0`.  If the maximum
were `Q`, both `N` and `P_d` would be at most `Q`, contradicting
`C_d(P_d)-Q>=delta>0`.  Hence `B_d=N>=P_d` and

```text
d_d(sigma)=N-Q>=K_d(z)>=delta.
```

Thus `d` is the unique debtor, and it is the only possible floor-violating
coordinate.

Always Continue attains the strict cap branch.  Replacing only `d` leaves its
opponents, hence its cap, unchanged; at the repaired stationary profile
`tau`, `U_d=B_d(sigma)` and `d_d=0`.  The global terminal gap therefore
selects a free debtor `j` with `d_j(tau)>=Gamma`.  Since the owner is now above
floor, the floor-safe/free-floor-damage split is exhaustive and disjoint.

Against the stationary opponents at `tau`, the free debtor's prescribed value
lies in the closed segment joining its immediate-Quit and Never values, while
its unrestricted stationary cap is their maximum.  This remains true when
opponent absorption is zero.  Therefore their difference has magnitude at
least `Gamma`.  Orienting `some 0` and `none` by payoff lets the checked
`exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub` decoder return
exactly

```text
Nonempty (QuittingPaidFirstDisagreementRow reward tau j Gamma),
j != d.
```

Ties, Never, and both payoff orientations are retained.  Nothing in this
argument identifies the strategy update with an exact Nash--Bellman edge.

## Actual-data adapter and conjecture-facing narrowing

Reviewed Proposition 29.2 supplies exactly the input claimed.  It moves the
paid base label `c` into the free set `F={c,x,y}`, retains singleton owner
`d`, and considers the full compact three-player induced Nash set.  If
`K_d<=0` at any Nash point, the checked singleton-base certificate and its
unrestricted consumer already yield a uniform-equilibrium payoff, contrary
to the terminal witness.  Continuity and compactness therefore give one
`delta>0` valid on the entire Nash carrier.

The packet consequently narrows the named large-base branch of
`PAID_ADMISSIBLE_PAYOFF_NEAR_RETURN`: it produces an actual stationary source
with debt concentrated in the owner, repairs that owner by an executable
stationary replacement, and leaves either a floor-safe outside debtor or an
explicit free-coordinate floor loss, while retaining a literal paid row in
both arms.  It does not claim that the reselected source is reached from the
old paid boundary face.

## Remaining export gates

- **Probability and agency:** all stationary mixing is independent private
  Bernoulli mixing; no correlation is introduced.  The free-player and owner
  cap arguments cover all behavioral deviations, finite times, Never, and
  ties.
- **Boundary tests:** the rational floor-damage regression checks the exact
  owner debt `2`, repair, free debt/floor damage, and paid gain `1`.  The
  separate all-free-Continue test checks `beta=1`, `N=0`, `K_d=1`, and the
  absence of illegal division.  The three necessity tests isolate the roles
  of positive excess, terminal gap, and sure date-zero ownership.
- **Source/novelty:** the named Lean declarations supply the stationary cap,
  minmax upper leg, singleton-base consumer, and paid decoder.  Neither those
  declarations nor the cited literature statement contains the assembled
  large-base re-selection plus unique-debtor/owner-repair handoff.  The two
  component results have independent reviews.
- **Lean handoff:** the proposed three declarations keep the semantic theorem,
  cap-attaining repair, and paid decoder separate from the ordinary compact-
  Nash adapter and do not encode the desired positive excess as a source
  field.
- **Nonclaims:** the packet explicitly excludes an exact root, Bellman edge,
  reached transition, tangent-frontier rank, charge, repayment, and payoff
  near-return.  It therefore cannot be misread as closing the maintained paid
  producer.

No unresolved mathematical, source, scope, or export-gate objection remains.
