# Whole-packet gate: `FIN4_CHARGED_BLOCKER_COLLISION_OR_REPAYMENT_SPLIT`

Reviewer: `CODEX_EULER`

## Verdict

**ACCEPT.**  I checked the current packet against every item in
[`exports/README.md`](../exports/README.md).  The statement is self-contained
at literal `Fin 4`, the proof and constants are complete, the zero-drop source
adapter and exact-orbit consumer are identified accurately, and the packet
strictly narrows the named charged-blocker obligation without claiming a
collision root or a payoff near-return.  I found no mathematical or packet
repair.

## Exact statement and source adapter

The hypothesis supplied by the reviewed
[`FIN4_OFF_MINIMUM_CHARGED_BLOCKER_GATE`](../formalized/FIN4_OFF_MINIMUM_CHARGED_BLOCKER_GATE.md)
has all data actually used here: a fixed `a>0`, a nonempty rate interval via
the selected `p`, a boxed punishment-floor tail, and an exact positive solo
root with

```text
alpha=a/8 <= p <= 1-Gamma/(4M) < 1.
```

Although the upstream compactness proof initially names one blocker, the
present maximization may legitimately reselect it.  Exactness of the same
solo root at the actual limiting tail gives the endpoint upper inequality for
every inactive outsider.  If `i` maximizes `G_k(p)`, positivity gives
`R_i<Q_i`; consequently

```text
T_i=(Q_i-pR_i)/(1-p),
P_i <= Q_i < T_i <= X.1_i.
```

Replacing just coordinate `i` therefore preserves every other endpoint-Nash
condition and makes `i` indifferent.  This justifies the packet's reselected
tail `Y`; no unrecorded support or carrier assertion is used.  In particular,
the packet correctly says that `Y` is a boxed floor annotation, not a newly
constructed terminal-semantic carrier payoff.

## Compact gap and quantitative split

For a fixed owner and interior rate, `G_ell(x)<=0` says exactly that all three
outsiders weakly prefer Continue at the owner's full singleton payoff vector.
The owner is indifferent there.  Thus the positive solo row is exact endpoint
Nash, and punishment normality for the owner feeds the checked solo-cycle
completion, contradicting the maintained no-uniform branch.  Hence every
`G_ell(x)>0`.  The maximum of three affine functions is continuous, the owner
set is finite, and the supplied rate interval is compact and nonempty, so the
minimum `g_a` exists and is strictly positive.

The remaining identities and constants are exact:

```text
T-Q = p(Q-R)/(1-p) >= alpha*g_a,
g = (1-p)(s_i-R)+p(b-R),
s_i-Q = p(g-(b-R))/(1-p).
```

Thus either `b-R>=g/2>=g_a/2`, or the strict complement gives
`s_i-Q>alpha*g_a/2`.  No endpoint case at `p=1` is hidden because the checked
upper bound gives `p<1`.

## Orbit extension, orientation, and behavioral scope

The prescribed first root can be retained when extending the boxed floor
tail: exact floor propagation gives its first successor, and ordinary finite
mixed-Nash existence plus dependent choice selects every later row.  For the
resulting infinite punishment-floor orbit,

```text
V_(t+1)=Succ(V_t,q_t),   V_1(i)=Q_i.
```

The checked all-orbits theorem
`QuittingTerminalExploitabilityWitness.infiniteOrbit_exists_value_limit`
applies to every such extension, not merely to a canonical selection.  It
gives a coordinatewise annotation limit `L` with `L_i>=s_i`, so a finite
annotation repays at least `alpha*g_a/4` in coordinate `i`.  Executable
Bellman-relation orientation is the reverse annotation order
`V_t -> ... -> V_1 -> V_0`; its final edge is exactly the retained root and
has absorption `p>=alpha`.

The packet's probability audit is accurate.  Roots are independent product
laws, the positive pair premium is not pair-event mass, and the orbit is an
exact annotation path rather than a realized terminal behavioral profile.
Unrestricted behavioral power enters through the true punishment floor and
the checked terminal exploitability witness; it is not replaced by a
stationary-deviation argument.

## Boundary, novelty, and consumer audit

The algebraic premium example, repayment/orientation regression, and
zero-pair-mass example test the relevant sharp distinctions.  The empty-rate-
interval boundary is also stated explicitly and is excluded only by the
actual gate's supplied `p`.

This is not a duplicate of the upstream blocker gate.  Its new content is the
uniform compact gap and the exhaustive quantitative split into a fixed
same-pair reward premium or an anchored exact one-coordinate repayment.  That
strictly narrows the zero-drop arm of the maintained
`PAID_ADMISSIBLE_PAYOFF_NEAR_RETURN` obligation.  The downstream near-return
consumer is named correctly, and the packet equally clearly records why
neither current arm yet satisfies it: the premium lacks source-matched
collision mass, while repayment controls only one coordinate.

The Lean handoff isolates the new theorem from the reviewed blocker producer,
identifies the compact finite maximum, coordinate replacement, anchored orbit
extension, and checked value-limit theorem, and does not assume either output
as a structure field.  The final nonclaims correctly exclude positive pair
support, semantic debt spend, realized-limit provenance, full payoff return,
uniform payoff, and the full four-player conjecture.
