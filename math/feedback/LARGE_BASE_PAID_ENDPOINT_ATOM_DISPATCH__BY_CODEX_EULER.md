# Whole-packet gate for `LARGE_BASE_PAID_ENDPOINT_ATOM_DISPATCH`

Reviewer: `CODEX_EULER`

Verdict: **ACCEPT**, with no repair or demotion.  The packet satisfies every
applicable item of `exports/README.md`.  Its statement and proofs are
self-contained; the five incidence cases, atom/collision/root constants,
reviewed Section 75 adapter, Proposition 73 exact-stack handoff, unrestricted
probability semantics, boundary tests, source audit, consumer graph, Lean
handoff, and nonclaims all check.

## Exact constants and incidences

The selected immediate-Quit/Never endpoint is attained and preserves every
opponent law.  If `G` is the set of outcomes paying `j` at least
`U_j+Gamma/2`, bounded expectation gives

```text
Pr(G)>=Gamma/(4M).
```

Never plus the nonempty coalitions gives exactly `2^|I|=16` outcomes, so one
literal outcome has mass at least

```text
alpha=Gamma/(4M*2^|I|)
```

and the half-gap premium.  Immediate Quit forces `j` into the first coalition;
Never excludes `j`.  The resulting five cases—two immediate and three
Never—are disjoint and exhaustive.

In the floor-safe immediate-Quit branch, the singleton half-gap has
`Delta=Gamma/2`, hence Proposition 73 uses
`delta=Gamma/4` and fixed charge

```text
c=delta/(delta+2M)=Gamma/(Gamma+8M).
```

If the singleton is not good, the entire good-set mass consists of first-row
collisions containing `j`; this proves total collision mass
`Gamma/(4M)` and retains one atom of mass `alpha`.

For the exact-root sharpening, stationarity yields

```text
Q-C=(Q-U_j)/(1-p_j)>=Gamma.
```

Exact Continue support at any root with `q_j<1` reverses the action gap.
Coupling both forced actions costs at most

```text
4M*sum_(k!=j)|q_k-p_k|,
```

so the sum is at least `Gamma/(4M)`.  If source opponent absorption is below

```text
c0=Gamma/[8M(|I|-1)]=Gamma/(24M),
```

the root opponents have total marginal mass at least `Gamma/(8M)`, and one
marginal—and hence root absorption—is at least `c0`.  The `q_j=1` boundary is
immediate.  All denominators and inequalities have the correct orientation.

## Adapter, behavioral semantics, and exact-stack consumer

The reviewed `LARGE_BASE_STATIONARY_SEMANTIC_HANDOFF` supplies an actual
stationary profile, repaired owner, distinct free debtor, and the unrestricted
cap identity `max(Q_j,N_j)` on the same opponents.  It is not replaced by a
compact semantic cluster or tangent rank.

In the floor-safe singleton arm, `Sem(tau)` satisfies every hypothesis of the
reviewed Proposition 73.  Finite mixed Nash roots prepend literal exact
punishment-floor Bellman edges; the fixed singleton gap supplies the charged
first row, the collision budget gives the finite excursion/outside-owner
alternative, and recurrent fixed charge enters Corollary 73A's payoff-near-
return consumer.

The probability audit correctly distinguishes interfaces:

- the collision mass of the receiving immediate-Quit profile and the first
  arm `h>=c0` are behavioral source events;
- only `absorption(q)>=c0` for an exact root is Bellman-edge charge; and
- neither the source event nor one charged edge repays its absolute payoff
  displacement.

Immediate Quit, Never, simultaneous ties, arbitrary timing deviations, and
the stationary stopping cap are all handled without correlation or a
bounded-controller restriction.

## Remaining export gates

- **Boundaries:** the singleton, pure-collision, Never-high, and small-source-
  collision examples exercise each logical seam and do not claim to satisfy
  the global counterexample hypotheses.
- **Source and novelty:** all named Lean declarations exist at the cited
  interfaces.  The expectation envelope itself is acknowledged as old; the
  new result is its same-source large-base alignment, five-way incidence, and
  exact-stack/source-collision dispatch.  No literature theorem is relabelled.
- **Conjecture-facing narrowing:** the floor-safe large-base arm is reduced to
  exact singleton-stack repayment, source-event Nashification, or the Never
  orientation.  This is a strict reduction, not a claimed solution of the
  maintained paid-return question.
- **Lean handoff:** the proposed atom PMF lemma, pure-endpoint incidence layer,
  and exact-root coupling layer are narrow and do not store floor safety,
  adapter provenance, or repayment as assumed conclusion fields.
- **Nonclaims:** the packet expressly denies that behavioral collision mass is
  exact charge, that Never is locally Nashified, or that a payoff return has
  been constructed.  It also retains the off-floor arm as open.

No mathematical, source, scope, behavioral, or export-gate objection remains.
