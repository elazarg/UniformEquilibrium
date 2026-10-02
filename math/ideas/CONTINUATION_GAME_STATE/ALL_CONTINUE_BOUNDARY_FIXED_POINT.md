# The All-Continue Trap in the Response-Graph State

The completed response graph distinguishes a finite all-Continue delay, unlike
the semantic pair and terminal law.  Nevertheless, infinitely many such
delays converge to a boundary fixed point.  The unique-all-Continue obstruction
therefore survives the state enlargement in a more explicit form.

## 1. One all-Continue prefix

For the all-Continue root, player `i` has

```text
Q_i = r_i({i}),   A_i = 0,   m_i = 1.
```

Writing `s_i = r_i({i})`, the graph transport formula becomes

```text
Gamma_i(C * sigma)
  = {(0,s_i)} union shift(Gamma_i(sigma)).                         (1.1)
```

The prescribed payoff and terminal law are unchanged.  The cap becomes

```text
B_i(C * sigma) = max(s_i,B_i(sigma)).                              (1.2)
```

Thus whenever all Continue is cap-Nash, `s_i <= B_i(sigma)`, the finite
semantic pair is fixed even though the response graph changes.

## 2. Repeated delay

After `N` all-Continue prefixes,

```text
Gamma_i(C^N * sigma)
 = { (d,s_i) : 0 <= d < N }
   union shift^N(Gamma_i(sigma)).                                  (2.1)
```

Let `H_i` be the compact set of all heights occurring in the original graph:

```text
H_i = { y : exists d, (d,y) in Gamma_i(sigma) }.
```

The graphs in (2.1) converge in the hyperspace to

```text
Gamma_i^inert
 = { (d,s_i) : d finite }
   union ({infinity} x (H_i union {s_i})).                         (2.2)
```

Proof sketch.  Every fixed finite date eventually lies in the inserted idle
prefix and has value `s_i`.  Every point of the shifted original graph has
date tending to infinity while retaining its height, so all of `H_i` appears
in the infinity fibre.  Conversely every graph point is of one of these two
forms, which gives the Hausdorff upper-limit inclusion.

The limit is fixed by another all-Continue prefix:

```text
{(0,s_i)} union shift(Gamma_i^inert) = Gamma_i^inert.              (2.3)
```

If `B_i(sigma) >= s_i`, its maximum height remains `B_i(sigma)`.

At the same time, every individual stopping law shifted by `N` dates converges
weakly to literal Never, although the ordinary terminal law of the jointly
shifted profile is unchanged.  The fixed state (2.2) is therefore the
response-graph refinement of the familiar pure-Never-marginals/positive-law-
bubble boundary normal form.

## 3. Interpretation

The semantic all-Continue trap is not caused merely by forgetting a finite
date.  Under graph completion, the old tail's complete response spectrum is
transported to a vertical boundary fibre at infinity.  The enlarged state
remembers the values but loses their finite chronological accessibility in
the limit.

This is a precise response-bubble normal form:

```text
finite dates:       constant solo value;
infinity fibre:     every inherited tail-response value;
terminal law:       unchanged;
prescribed payoff:  unchanged;
cap:                unchanged when all Continue is cap-Nash.
```

A positive paid row in the old suffix becomes a positive pair of heights in
the infinity fibre.  It does not force a non-all-Continue root, current
absorption, or an admissible return.  This matches the exact local regressions
for unique all-Continue caps.

## 4. Consequence for a possible consumer

Any theorem consuming the response-graph state must distinguish two kinds of
recurrence:

1. recurrence with charge or with a finite-date marked response, which may be
   executable; and
2. the fixed boundary state (2.2), where all nontrivial response geometry has
   escaped into the infinity fibre and every finite root remains inert.

The second case still needs an external source-provenance or punishment
argument.  Merely proving compact recurrence of the graph state will stop at
this fixed point.

This calculation is ordinary mathematics and has not been checked in Lean.
