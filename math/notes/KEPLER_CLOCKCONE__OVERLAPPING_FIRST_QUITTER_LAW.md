# KEPLER_CLOCKCONE — overlapping first-quitter law and `Fin 4` consumer

Author: `KEPLER_CLOCKCONE`

Status: **the overlapping square-root conjecture is proved as ordinary
mathematics, including arbitrary nonstationary hazards, atoms, and `Never`
mass.**  The constant is sharp and the equality laws are classified.  The new
law gives all adjacent-edge projections of the six-coordinate `K_4` pair-law
body and an exact conditional terminal-gap consumer.  It does not characterize
the full six-coordinate body and does not produce a reward table that activates
the consumer.  Nothing in this note is Lean-checked.

The main result is

```text
sqrt(P(T0=T1<T2, finite)) + sqrt(P(T0=T2<T1, finite)) <= 1
```

for three independent stopping times in `Nat union {Never}`.  The proof works
directly with the executed complete clocks.  Consequently, its negative-game
consumer bypasses backward-source/forward-chronology reconstruction, although
the strategic task of forcing forbidden pair masses remains open.

## 1. Self-contained question and source boundary

Let `T0,T1,T2` be independent random variables with values in
`Nat union {Never}`.  Put

```text
A = {T0=T1<T2 and T0 is finite},
B = {T0=T2<T1 and T0 is finite},
a = P(A),
b = P(B).
```

The finite clause excludes an all-`Never` equality.  A strict inequality such
as `T0<T2` still permits `T2=Never`.

I read `SOURCES.md`, `GOAL.md`, all current conference filenames, and
`notes/MERIDIAN_BLINDSPOTS.md` completely.  The narrow stopping-law sources
inspected afterward were:

- `quittingBehaviorStoppingLaw`,
  `quittingHazardStoppingLaw_none_toReal`,
  `quittingHazardStoppingLaw_some_toReal`, and
  `stoppingLawSurvival_quittingBehaviorStoppingLaw` in
  `UniformEquilibrium/Quitting/Paths/BehaviorStoppingLaw.lean`;
- `sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
  `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`;
- `quittingUniformEquilibriumPayoffConjecture` in
  `UniformEquilibrium/Quitting/Conjecture/Basic.lean`;
- `not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap`
  in `UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`;
- the stopping-law portions of
  `CODEX_CEDAR__STOPPING_TIME_COMPACT_GAME.md`,
  `CODEX_CEDAR__INDEPENDENT_CLOCK_TOGGLE_GADGET.md`, and
  `CODEX_CEDAR__TWO_PAIR_CLOCK_RIGIDITY_COMPILER.md`; and
- Propositions 17--19 in the disjoint-clock section of
  `CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL.md`.

The Lean declarations above establish the stopping-law semantics and the
unrestricted-deviation endpoint used in Section 8.  They do not state the
overlapping inequality proved here.  The disjoint-pair square-root law in the
conference notes is prior ordinary mathematics; it is used only for the
disjoint `K_4` projections in Section 7.

## 2. Exact finite-support falsification before the proof

For marginal atom vectors `p,q,r`, with the last coordinate denoting `Never`,
the exact formulas are

```text
a = sum_t p_t q_t (sum_(s>t) r_s),
b = sum_t p_t r_t (sum_(s>t) q_s),                 (2.1)
```

where the sum over `s>t` includes `Never`.

I exhaustively scanned two rational grids, using integer arithmetic rather
than floating comparison:

- all `455^3 = 94,196,375` triples of laws on
  `{0,1,2,Never}` whose masses are multiples of `1/12`; and
- all `495^3 = 121,287,375` triples of laws on
  `{0,1,2,3,Never}` whose masses are multiples of `1/8`.

If the common denominator is `D`, write `a=A/D^3`, `b=B/D^3`, and `M=D^3`.
The test first rejects `A+B>M`; otherwise it checks the exactly equivalent
integer inequality

```text
(M-A-B)^2 >= 4*A*B.                                (2.2)
```

There was no violation.  Both grids attained equality with `a,b>0`.  For
example, on `{0,1,2,Never}` the numerator vectors

```text
p=(0,0,12,0), q=(0,0,1,11), r=(0,0,11,1)
```

give `(a,b)=(1/144,121/144)`.

As a separate exact local screen, I checked every quadruple
`x,q,r,u` on the denominator-`40` grid, with future boundary point
`(a',b')=(u^2,(1-u)^2)`.  All `41^4=2,825,761` cases satisfied the propagated
inequality.  These finite scans are experiments, not the proof below.

There is also a finite-dimensional support reduction explaining why
two-point laws repeatedly appear.  With two marginals fixed, `(a,b)` depends
linearly on the third marginal.  On a finite date set its image is a polygon
in the `(a,b)` plane.  Since `(a,b) |-> sqrt(a)+sqrt(b)` is coordinatewise
increasing, a maximum lies on a Pareto-boundary vertex or edge.  The optimizing
marginal may therefore be supported on at most two dates.  Starting from a
global maximizer and replacing the three marginals in turn gives a global
maximizer with every marginal two-supported.  This is a useful finite-support
reduction, but the one-step proof makes order-type enumeration unnecessary.

## 3. The invariant one-step lemma

The failed local estimate recorded by `MERIDIAN` tries to add the square roots
of the two immediate event masses and joint continuation.  It is false at
three hazards `1/2`.  The correct invariant propagates the whole curved region.

### Lemma 3.1 (curved-region propagation)

Let `x,q,r` lie in `[0,1]`, and let `alpha,beta>=0` satisfy

```text
sqrt(alpha)+sqrt(beta)<=1.
```

Set

```text
c     = (1-x)(1-q)(1-r),
A     = x*q*(1-r) + c*alpha,
B     = x*r*(1-q) + c*beta.
```

Then `sqrt(A)+sqrt(B)<=1`.

### Proof

Put `u=sqrt(alpha)` and `v=sqrt(beta)`.  Because the displayed objective is
increasing in `v`, it is enough to replace `v` by `1-u`.  Define, for
`0<=u<=1`,

```text
F(u) = sqrt(x*q*(1-r) + c*u^2)
     + sqrt(x*r*(1-q) + c*(1-u)^2).               (3.1)
```

Each summand has the form `sqrt(d+c*u^2)` after an affine change of `u`; its
second derivative is nonnegative (and the zero-parameter cases follow by
continuity).  Thus `F` is convex and

```text
F(u) <= max(F(0),F(1)).                            (3.2)
```

Write `Q=1-q`, `R=1-r`.  At the right endpoint, put

```text
D = x*q+(1-x)*Q.
```

Two-coordinate Cauchy--Schwarz gives

```text
F(1) = sqrt(R*D)+sqrt(r*x*Q)
     <= sqrt((R+r)*(D+x*Q))
      = sqrt(q*x+Q)
      = sqrt(1-(1-x)*q)
     <= 1.                                         (3.3)
```

The symmetric calculation gives

```text
F(0) <= sqrt(1-(1-x)*r) <= 1.                      (3.4)
```

Equations (3.2)--(3.4) prove the lemma.  Notice that this retains exactly the
future split between the two boundary coordinates; subadditivity of square
root discards that split and is why the naive induction fails.  QED.

## 4. The arbitrary-clock theorem

### Theorem 4.1 (overlapping-pair square-root law)

For arbitrary independent `T0,T1,T2` in `Nat union {Never}`,

```text
sqrt(a)+sqrt(b)<=1.                                (OP)
```

Equivalently, with `ell=1-a-b`,

```text
ell >= 2*sqrt(a*b),
ell^2 >= 4*a*b.                                    (4.1)
```

### Proof

Represent each marginal by its conditional hazard at every finite date.  This
representation includes arbitrary atoms and an arbitrary limiting `Never`
mass.  At a live date let the three hazards be `x,q,r`, in the order
`T0,T1,T2`.  Conditional on all three clocks continuing, their tail laws are
again independent.

First truncate the two events to common times at most `N`.  Work backward
from future probabilities `(alpha,beta)=(0,0)` after date `N`.  At one step
the two conditional probabilities obey exactly

```text
A = x*q*(1-r) + (1-x)(1-q)(1-r)*alpha,
B = x*r*(1-q) + (1-x)(1-q)(1-r)*beta.
```

Lemma 3.1 propagates `sqrt(A)+sqrt(B)<=1` to date zero.  The truncated events
increase to `A` and `B` as `N` tends to infinity.  Continuity from below and
continuity of square root prove `(OP)`.  Finally, squaring `(OP)` gives
`a+b+2*sqrt(a*b)<=1`, which is (4.1).  QED.

This proof does not assume stationarity, finite support, eventual absorption,
or zero `Never` mass.

## 5. Sharpness and complete equality laws

The constant one is sharp.  There are two visibly different positive-mass
families.

### Same-date family

At a date `t`, let `T0=t` surely, let `P(T1=t)=p`, and let
`P(T2=t)=1-p`; on failure, `T1,T2` may have arbitrary later laws.  Then

```text
a=p^2, b=(1-p)^2.
```

### Staggered family

At a date `t`, let `T0` and `T1` independently stop with the same probability
`p`, while `T2` continues surely.  Conditional on continuation of both first
clocks, at a later date `s` let `T0=T2=s` surely and require `T1>s` surely.
Then

```text
a=p^2, b=(1-p)^2.
```

Exchanging players `1` and `2` gives the reverse orientation.  Taking the
later clock to be `Never` recovers `MERIDIAN`'s displayed example.

These exhaust equality, up to initial all-Continue dates and null tails.

### Theorem 5.1 (equality classification)

If `a,b>0`, equality in `(OP)` holds if and only if, after deleting an initial
string of dates at which all three hazards vanish, one of the following occurs.

1. `T0` stops surely at the current date, the hazards of `T1,T2` are
   `p,1-p` for some `0<p<1`, and later conditional laws are arbitrary.
2. The current hazards of `(T0,T1,T2)` are `(p,p,0)` for some `0<p<1`;
   conditional on joint continuation, `T0=T2=s<T1` almost surely for one
   later finite date `s`.
3. The current hazards are `(p,0,p)`; conditional on joint continuation,
   `T0=T1=s<T2` almost surely for one later finite date `s`.

In cases 2--3, the clock on the right of the final strict inequality can have
any law supported strictly after `s`, including `Never` mass.  If `b=0`,
equality means `a=1`, equivalently `T0=T1=s<T2` almost surely for one
deterministic finite `s`; the case `a=0` is symmetric.

### Proof

It remains only to justify necessity.  Apply Lemma 3.1 at the first date where
some hazard is nonzero.  Write `u=sqrt(alpha)`, `v=sqrt(beta)`.  If the joint
continuation coefficient `c` is positive, equality first forces `u+v=1`.

There is one degeneracy to separate before invoking strict convexity.  If both
immediate radicands in (3.1) vanish, then `F(u)=sqrt(c)` is constant on the
future boundary.  If `x=0` but `q` or `r` is nonzero, then
`c=(1-q)(1-r)<1`; if `x>0`, positivity of `c` and vanishing of both immediate
terms force `q=r=0`, so `c=1-x<1`.  Either way the current non-all-Continue
row gives strict loss.  The only equality degeneracy is therefore
`x=q=r=0`, an all-Continue row which can be deleted.  In every remaining case
at least one immediate radicand is positive, so the corresponding summand has
strictly positive second derivative on `(0,1)` and `F` is strictly convex.
Equality in (3.2) then forces `u=0` or `u=1`.

If `u=1`, equality in (3.3) forces `(1-x)q=0`.  Since `c>0` gives `x<1`, this
means `q=0`; equality in Cauchy--Schwarz then gives `r=x`.  The future law has
`(alpha,beta)=(1,0)`, producing case 3.  The endpoint `u=0` symmetrically gives
`r=0`, `q=x`, and case 2.

If `c=0` and both event probabilities are positive, the only possibility is
`x=1`.  The one-date Cauchy--Schwarz equality condition is `q+r=1`, giving
case 1.  A date before these patterns with any nonzero hazard would lose a
strict factor and cannot preserve equality.

Finally, independent countable random variables that are equal almost surely
must share one deterministic atom: if their common mass vector is `(m_s)`,
independence gives `sum_s m_s^2=1`, forcing one `m_s=1`.  Thus a conditional
future event of probability one has exactly the deterministic form stated in
cases 2--3.  The zero-coordinate boundary cases follow by the same argument.
QED.

## 6. Overlapping incomparable coalitions

The three-clock theorem is not restricted to pair coalitions.

### Corollary 6.1

Let independent clocks be indexed by any finite player set.  Let `C,D` be
two incomparable coalitions with `C intersect D` nonempty.  If `p_C,p_D` are
the probabilities that `C,D` are respectively the exact finite first-quitter
coalition, then

```text
sqrt(p_C)+sqrt(p_D)<=1.                            (6.1)
```

Choose `i` in `C intersect D`, `j` in `C\D`, and `k` in `D\C`.  The exact
`C` event is contained in `{Ti=Tj<Tk, finite}`; the exact `D` event is
contained in `{Ti=Tk<Tj, finite}`.  Apply Theorem 4.1 and monotonicity of
square root.

Incomparability is essential.  For nested coalitions `{i}` and `{i,j}`, a
single date with `Ti` sure and `Tj` Bernoulli can assign masses `1-p,p`; the
sum of their square roots exceeds one for `0<p<1`.

## 7. What this gives, and does not give, for the six `K_4` pair masses

For four clocks let

```text
q_ij = P({i,j} is exactly the finite first-quitter coalition).
```

Every two distinct edges of `K_4` are either adjacent or disjoint.  Corollary
6.1 handles adjacent edges; the prior disjoint-pair clock theorem handles
disjoint edges.  Hence the actual six-coordinate law body is contained in the
explicit semialgebraic outer body

```text
q_e >= 0,
sum_e q_e <= 1,
sqrt(q_e)+sqrt(q_f) <= 1          for every e != f,             (7.1)
```

or equivalently

```text
(1-q_e-q_f)^2 >= 4*q_e*q_f       for every e != f.              (7.2)
```

Thus the new theorem fills the twelve adjacent-edge projections, while the
three complementary matchings were already covered.  Every one of the fifteen
two-edge projections is sharp: use the equality laws above for adjacent edges
and the known two-gate equality law for disjoint edges, setting unused clocks
to `Never`.

This is not a characterization of the full six-coordinate body.  For example,
`q_e=1/6` for all six edges satisfies (7.1), but is not realizable.  Indeed, if
the finite first coalition has size exactly two almost surely, consider its
earliest date having positive absorption probability.  A product Bernoulli
row supported, apart from all-Continue, only on two-element nonempty sets must
have exactly two hazards equal to one and all others zero.  Absorption is then
sure at that row by one deterministic pair.  Therefore

```text
sum_e q_e=1  implies  q_e=1 for one edge and all other q_f=0.    (7.3)
```

Equation (7.3) is only an exact boundary rigidity statement, not the missing
quantitative global inequality.  A true description of the whole `K_4` body,
especially its star and cycle projections, remains open.

## 8. Precise `Fin 4` terminal-gap consumer

Here is the exact way the law can constrain a counterexample attempt.  Fix a
four-player reward table.  For a behavioral profile `sigma`, let `U_i(sigma)`
be prescribed terminal payoff, `B_i(sigma)` the supremum over all unilateral
behavioral replacements, and

```text
E(sigma)=max_i (B_i(sigma)-U_i(sigma)).
```

The checked pure-time extremality theorem cited in Section 1 says that each
`B_i` can equivalently be computed from deterministic finite quit times and
`Never`.

Suppose a strategic argument for two distinct edges `e,f` proves, for every
behavioral profile,

```text
q_e(sigma) >= alpha_e-L_e*E(sigma),
q_f(sigma) >= alpha_f-L_f*E(sigma),                (8.1)
```

where `L_e,L_f>=0`.  Define `[z]_+=max(z,0)` and

```text
Phi(delta)
 = sqrt([alpha_e-L_e*delta]_+)
 + sqrt([alpha_f-L_f*delta]_+),

Gamma
 = min {delta>=0 : Phi(delta)<=1}.                 (8.2)
```

If `sqrt(alpha_e)+sqrt(alpha_f)>1`, continuity gives `Gamma>0` (and the set in
(8.2) is nonempty whenever at least one slope is positive, as it must be for
consistent hypotheses).  Equations (7.1) and (8.1) imply

```text
Phi(E(sigma)) <= sqrt(q_e(sigma))+sqrt(q_f(sigma)) <= 1,
```

so every profile satisfies `E(sigma)>=Gamma`.  Approximation of the relevant
supremum then supplies, for every profile, one pure-time deviation gaining at
least `Gamma/2`.  Consequently
`not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap`
would refute a uniform-equilibrium payoff for that table.

More generally, if (8.1) is available for all six edges, take the maximum of
the fifteen numbers `Gamma_(e,f)`.  The twelve adjacent pairs are the genuinely
new consumers.  This formula is sharp given only the two affine forcing
inequalities and their pair-law projection: `Gamma` is exactly the first error
level at which the forced lower rectangle meets the square-root body.

This isolates the remaining hard residual without changing its quantifiers:

> Produce one finite reward table and two pair labels for which deterministic
> pure-time deviation inequalities imply (8.1), with
> `sqrt(alpha_e)+sqrt(alpha_f)>1`.

The law itself is reward-independent and applies after an arbitrary
nonstationary behavioral chronology has already been executed.  It therefore
bypasses source ancestry, suffix-fibre choices, and backward-to-forward
chronology on the negative side.  It does **not** produce (8.1).  In particular,
a pure sure-exit equilibrium or another low-exploitability escape can prevent
the required pair-mass floors.  The clock theorem is a complete consumer for
such floors, not a producer from arbitrary game data.

## 9. Dead ends retained and next question

- The local inequality
  `sqrt(immediate A)+sqrt(immediate B)+sqrt(continuation)<=1` is false at
  hazards `(1/2,1/2,1/2)`.  The curved-region propagation lemma is the repair.
- Coordinatewise two-point reduction is valid at a finite global maximizer,
  but classifying all weak order types would obscure the one-step invariant.
- The fifteen sharp pairwise projections do not characterize the six-edge
  law body; the uniform `1/6` vector and boundary rigidity (7.3) witness the
  gap.
- The new law does not by itself yield a four-player counterexample.  The next
  concrete mathematical question is whether a finite reward table can force
  the two affine mass bounds (8.1) for an adjacent edge pair, or whether every
  such attempt admits an explicit low-exploitability escape.
