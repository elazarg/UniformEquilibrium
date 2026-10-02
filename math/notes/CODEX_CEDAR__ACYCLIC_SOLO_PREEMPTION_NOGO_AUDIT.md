# CODEX_CEDAR — independent audit of the acyclic solo-preemption no-go

## Status

**Complete independent proof from the supplied statement; awaiting Ramsey's
owned note for protocol feedback.**  The graph orientation, exact pure-time
formula, unrestricted behavioral reduction, boundary times, constants, and
empty/singleton cases all check.  This is ordinary mathematics, not Lean
checked.

## Statement audited

Let `I` be finite and let `r` be a finite quitting reward table.  Write

```text
s_i = r({i})_i.
```

Adjoin a vertex `bottom` and put directed edges on `I union {bottom}` by

```text
bottom -> i  iff s_i>0,
i -> bottom  iff s_i<0,
i -> j       iff r({j})_j>r({i})_j.
```

The last comparison is in the **target player's coordinate `j`**.  Assume
this graph is acyclic.

For `p in I`, define the maximal positive tie premium

```text
J_p=max(0, max_(j!=p) [r({p,j})_j-r({p})_j]).       (1)
```

The inner maximum is omitted when there is no outsider.  Thus `J_p=0` for a
singleton player set.

Then a sink gives one of the following profiles.

1. If `bottom` is a sink, all players Never is exact terminal Nash.
2. If `p in I` is a sink, let only `p` use a constant stationary Quit hazard
   `q in (0,1]` and let every outsider Never.  Its unrestricted terminal
   exploitability is at most `q J_p`.

For the strict form, define

```text
d_p=min({s_p} union
        {r({p})_j-r({j})_j : j!=p}).                 (2)
```

For a singleton set this is just `s_p`.  If `d_p>0`, then the closed-form
choice

```text
q=d_p/[2(d_p+J_p)]                                  (3)
```

lies in `(0,1/2]`, and the stationary-solo profile is an exact terminal Nash
profile against every behavioral deviation.  Formula (3) is an exact ratio;
it is literally rational-valued only when the input constants have the
corresponding arithmetic property.

Consequently acyclicity rules out a fixed terminal exploitability gap.  In
case 2, choose positive `q` with `qJ_p<=epsilon` for each error.  The checked
all-errors terminal consumer then gives a uniform-equilibrium payoff.

## Finite sink and graph orientation

Every finite acyclic directed graph has a sink.  If `bottom` is a sink, the
absence of `bottom -> i` says `s_i<=0` for every player.  Against all Never,
any finite Quit by `i` receives `s_i<=0` and Never receives zero.  An arbitrary
behavioral law is a mixture of its finite first-Quit times and Never, so no
one can gain.

Suppose instead that `p` is a sink.  The missing edge `p -> bottom` gives
`s_p>=0`.  For each `j!=p`, the missing edge `p -> j` gives

```text
r({j})_j<=r({p})_j.                                  (4)
```

This is the required no-preemption inequality for outsider `j`.  Reversing
the graph comparison would not prove (4), so the orientation in the supplied
statement is load-bearing and correct.

## Exact pure-time calculation

Let `T_p` be geometric on `{0,1,...}` with hazard `q`, so

```text
Pr(T_p=t)=q(1-q)^t,
Pr(T_p>t)=(1-q)^(t+1).
```

Since `q>0`, `p` Quits eventually almost surely and the prescribed profile
payoff is `r({p})`.

Fix `j!=p` and abbreviate

```text
b_j=r({p})_j,
s_j=r({j})_j,
c_j=r({p,j})_j.
```

If `j` Quits at finite time `t`, then `p` is strictly earlier, tied, or
strictly later with probabilities

```text
1-(1-q)^t,
q(1-q)^t,
(1-q)^(t+1),
```

respectively.  Hence the exact gain over prescribed Never is

```text
g_j(t)
 =(1-q)^t [q(c_j-b_j)+(1-q)(s_j-b_j)].              (5)
```

By (4), the second term in brackets is nonpositive, while
`c_j-b_j<=J_p`.  Therefore

```text
g_j(t)<=q(1-q)^t J_p<=qJ_p.                         (6)
```

This includes `t=0`: the singleton outcome has probability `1-q` and the tie
has probability `q`.  At `t=infinity`, `j` keeps Never and its gain is exactly
zero.

Player `p` faces only Never opponents.  Its payoff under any deviation law is
`s_p` times its probability of ever Quitting.  Since `s_p>=0` and the
prescribed geometric clock Quits almost surely, its deviation gain is at most
zero.

## Unrestricted behavioral deviations

Before absorption the only public history is a string of all-Continue rows.
Thus any complete unilateral behavioral strategy induces one first-Quit law
`mu` on `Nat union {infinity}`, independent of `p`'s private geometric clock.
Linearity of terminal expectation gives

```text
Gain_j(mu)=sum_(t finite) mu(t) g_j(t)+mu(infinity)*0.
```

Equation (6) bounds this by `qJ_p`.  No stationary, bounded-controller, or
finite-time restriction on the deviator is hidden.  Ties and Never are both
included literally.

## Strict sink constant

If `d_p>0`, then for every outsider

```text
b_j-s_j>=d_p,
c_j-b_j<=J_p.
```

For the choice (3),

```text
qJ_p-(1-q)d_p=-d_p/2.                                (7)
```

Substituting in (5) yields

```text
g_j(t)<=-(1-q)^t d_p/2<0
```

for every finite `t`, while Never has gain zero.  The owner has
`s_p>=d_p>0` and already Quits almost surely, so it also cannot gain.  The
profile is exact terminal Nash.  The denominator in (3) is positive and
`0<q<=1/2`; if `J_p=0`, then `q=1/2`.

## Empty and singleton player sets

- If `I` is empty, the graph consists only of `bottom`.  The empty all-Never
  profile is vacuously exact.  No `p`, `J_p`, or division is invoked.
- If `I={p}` and `s_p<=0`, `bottom` is a sink and all Never is exact.
- If `I={p}` and `s_p>0`, `p` is a sink.  There are no outsiders,
  `J_p=0`, and every `q>0` gives the exact payoff `s_p`; the strict formula
  gives `q=1/2`.
- If `I={p}` and `s_p=0`, both vertices are sinks.  All Never is exact, and
  the stationary-solo profile is exact as well.

## Terminal semantics, novelty, and scope

The argument is entirely terminal: a positive geometric clock terminates
almost surely, the payoff is the literal singleton vector `r({p})`, and the
only changed coalition under an outsider deviation is the tie `{p,j}`.  The
all-errors conclusion uses the checked declaration
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`;
the graph-to-profile producer and the exact formula (5) are the new ordinary
mathematics in the supplied claim.

A narrow conceptual comparison shows that this is not the general
signed-influence or odd-blocker theorem: it uses only singleton preemption and
one geometric owner, and it imposes no sign consistency on nonsingleton
coalitions beyond the bounded tie premium `J_p`.  It is a no-go for an
**acyclic solo-preemption architecture**, not a proof that every quitting
table has an acyclic graph.  Cyclic graphs remain outside the result.

