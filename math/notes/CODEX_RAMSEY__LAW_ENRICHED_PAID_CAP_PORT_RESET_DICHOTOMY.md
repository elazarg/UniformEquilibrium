# Law-enriched completion of the Fin4 paid cap port

Author: `CODEX_RAMSEY`

Status: **REVISE -> PASS after independent review.**  The
result does not close the paid branch.  It upgrades the reviewed same-source
cap port to a limiting *joint semantic/law* carrier point, retains a fixed
fraction of the original reset incidence and paid-debtor debt, and reapplies
the checked fixed-law reset dispatcher at that exact port.  The output is an
exact strict carrier-debt descent below the port, or the precise
all-Continue cap-face obstruction.  The prescribed coordinates below are not
claimed to form a Bellman path.

Primary input (including the formalized Fin4 same-source adapter):
[`PAID_CAP_LIFTED_SUMMABLE_PORT.md`](../formalized/PAID_CAP_LIFTED_SUMMABLE_PORT.md).

Independent review:
[`CODEX_EULER`](../feedback/CODEX_RAMSEY__LAW_ENRICHED_PAID_CAP_PORT_RESET_DICHOTOMY__BY_CODEX_EULER.md),
core PASS after the two wording repairs incorporated below.

Question:
[`PAID_ADMISSIBLE_PAYOFF_NEAR_RETURN.md`](../questions/PAID_ADMISSIBLE_PAYOFF_NEAR_RETURN.md).

## 1. Data and notation

Fix a bounded Fin4 quitting reward table and a terminal exploitability
witness.  Choose pairwise distinct labels

```text
o, b1, b2 : Fin 4.
```

Apply the reviewed same-source composite.  It supplies a positive global
minimum `Z_*`, a pair-base stationary target profile `sigma_0`, its terminal
semantic pair and complete law

```text
X_0=(U_0,B_0),       mu_0,
```

and the cap-lifted profiles

```text
sigma_(n+1)=rootThenContinuation(q_n,sigma_n),
X_n=Sem(sigma_n)=(U_n,B_n),
mu_n=terminalOutcomeMass(sigma_n).
```

Every `q_n` is exact Nash against `B_n`.  Put

```text
a_n = absorption(q_n),
c_n = 1-a_n,
S_n = product_(m<n)c_m,
D_* = D(Z_*),
D_n = D(X_n),
sigma = D_*/D_0.
```

The checked cap-port identities give

```text
D_n=S_n D_0,       S_n>=sigma>0,       sum_n a_n<infinity.       (1.1)
```

The exact punishment-floor Nash--Bellman orbit is the sequence of **cap
annotations** `B_n`.  The `U_n` are the prescribed coordinates of the same
literal profiles and are used below only as carrier semantics.  No arrow
`U_n -> U_(n+1)` is asserted.

The pair-base target additionally has:

```text
d_o(X_0)=0,
d_f(X_0)=0 for the other free label f outside {b1,b2},
d_j(X_0)>=Gamma for its selected paid debtor j in {b1,b2},
Inc_(o,b1)(mu_0)=1.                                      (1.2)
```

Here `Gamma` is the witness terminal gap.

## 2. A summable prefix word has a complete-law limit

### Lemma 2.1 (one-prefix law variation)

For every `n`, in the `l1` norm on the finite terminal-outcome space,

```text
||mu_(n+1)-mu_n||_1 <= 2 a_n.                           (2.1)
```

**Proof.**  Write `nu_n(S)` for the first-root probability of the nonempty
quitting coalition `S`.  The exact law-prefix formula is

```text
mu_(n+1)(none)=c_n mu_n(none),
mu_(n+1)(S)=nu_n(S)+c_n mu_n(S),
sum_S nu_n(S)=a_n.
```

The `none` difference is bounded by `a_n mu_n(none)`.  For each terminal
coalition its absolute difference is at most
`nu_n(S)+a_n mu_n(S)`.  Summing and using that `mu_n` is a probability vector
gives `(2.1)`. `QED`

### Proposition 2.2 (law-enriched summable port)

There is a probability vector `mu_infinity` such that

```text
mu_n -> mu_infinity                                    (2.2)
```

and, writing `X_infinity` for the checked semantic-port limit,

```text
(X_infinity,mu_infinity)
  belongs to quittingTerminalSemanticLawCarrier reward. (2.3)
```

Moreover, if `S_infinity=lim_n S_n`, then

```text
S_infinity>=sigma>0,
mu_infinity(omega)>=S_infinity mu_0(omega)
  for every terminal outcome omega.                    (2.4)
```

Consequently

```text
Inc_(o,b1)(mu_infinity)>=S_infinity>=sigma.             (2.5)
```

**Proof.**  Lemma 2.1 and summability of `a_n` make `mu_n` Cauchy in the
finite-dimensional law simplex, proving `(2.2)`.  Each `(X_n,mu_n)` is the
actual joint semantic/law point of `sigma_n`.  The semantic component tends
to `X_infinity`, and the joint carrier is closed, proving `(2.3)`.

Induction in the exact law-prefix formula gives
`mu_n(omega)>=S_n mu_0(omega)` for every outcome.  (For `none` this is an
equality; for a terminal outcome all fresh-root contributions are
nonnegative.)  The finite products `S_n` decrease and remain above `sigma`,
so taking limits proves `(2.4)`.  Summing over the incidence event and using
`Inc_(o,b1)(mu_0)=1` proves `(2.5)`. `QED`

This is a law statement, not convergence of behavioral profiles.  The
positive amount of old suffix law in `(2.4)` is pushed to later and later
literal dates; there need not be a behavioral profile which executes
`sigma_0` after an infinite prefix.

## 3. Debt and atom data retained at the port

### Lemma 3.1 (coordinatewise ray persistence)

For every player `i` and every `n`,

```text
d_i(X_n)=S_n d_i(X_0).                                  (3.1)
```

Hence the limit satisfies

```text
d_o(X_infinity)=d_f(X_infinity)=0,
d_j(X_infinity)>=sigma Gamma>0,                         (3.2)
positiveDebtSupport(X_infinity) subset {b1,b2}.
```

**Proof.**  The checked playerwise cap-Nash prefix identity multiplies every
debt coordinate by `c_n`.  Induction proves `(3.1)`, and the semantic
convergence gives `(3.2)`. `QED`

Thus the cap lift itself never decreases positive-debt support: its entire
debt vector remains on one positive scalar ray.  Any support decrease must
come from a new source-changing operation.

There is also a fixed static terminal atom at the limiting port.  Among the
at most eight nonempty Fin4 coalitions containing `b1`, one has

```text
mu_infinity(S)>=sigma/8.                                (3.3)
```

The checked theorem
`QuittingTerminalExploitabilityWitness.exists_exactToggle_gain` in
`Collision/Toggles/FiniteInstability.lean` applies **to every coalition**;
at this same heavy `S` it therefore selects a membership toggle with payoff
premium at least `Gamma`.  (Equivalently use its max-form corollary
`terminalGap_le_pureToggleExploitability`.)  This is a terminal-law fact.  It
is not an executable Bellman charge: the deviator cannot in general
condition its simultaneous action on which coalition will be realized.  The
selected toggle player and its leave/join orientation need not equal the paid
debtor `j`, the reset owner `o`, or the incidence label `b1`.  No limiting
paid-row provenance is inferred from this atom.

## 4. Reset reapplication at the exact port

### Theorem 4.1 (strict port-debt descent or all-Continue obstruction)

Apply
`QuittingTerminalExploitabilityWitness.exists_fixedLawResetDispatch` with

```text
source = Z_*,
target = X_infinity,
mass   = mu_infinity,
owner  = o,
other  = b1.
```

All its hypotheses hold by global minimality, `(2.3)`, `(2.5)`, and
`d_o(X_infinity)=0`.  It returns a pair `R` over the **same limiting law**
such that

```text
U(R)=U_infinity,
D_* <= D(R) <= D(X_infinity),
d_o(R)=0.                                               (4.1)
```

At least one of the following checked alternatives is available.  The
dispatcher stores a disjunction; exclusivity is neither needed nor claimed.

1. **Strict port-debt descent.**  There is a positive-absorption,
   positive-survival root `r`, exact Nash against `B(R)`, for which

   ```text
   Y=Prefix(r,R) belongs to the semantic carrier,
   D(Y)<D(R)<=D(X_infinity),                            (4.2)
   d_o(Y)=0,
   ```

   and the prefixed complete law retains positive `(o,b1)` incidence.
   In particular `D(Y)<D(X_infinity)` is a literal strict semantic-carrier
   descent below the cap-port anchor.

2. **All-Continue cap-face obstruction.**  The all-Continue root is exact
   Nash against `B(R)` and fixes `R` under semantic prefixing.  The same
   point still has prescribed payoff `U_infinity`, reset owner, positive
   old incidence, the fixed atom `(3.3)`, and its terminal toggle.  No fresh
   absorption follows.

If `D(X_infinity)=D_*`, the first arm is impossible and the second arm is
forced by
`QuittingFixedLawResetDispatch.allContinue_of_target_debt_le_source`.

**Proof.**  Existence and `(4.1)` are the fixed-law dispatcher plus
`QuittingFixedLawResetDispatch.prescribed_eq_target`.  Its dynamic branch is
exactly `(4.2)`; its other branch is the stated stall.  The minimum-target
specialization gives the final assertion. `QED`

The root in `(4.2)` is exact against `B(R)`.  It is not asserted exact
against `U_infinity`, and `B(R)` need not equal any `B_n`.  Therefore `(4.2)`
is not an edge attached to the existing cap orbit, and it is not already a
payoff near-return.

## 5. Finite-depth quantitative form

The same reset dispatcher may be reapplied at every actual joint point
`(X_n,mu_n)`: owner debt is zero by `(3.1)` and incidence is at least
`S_n>=sigma` by the finite version of `(2.4)`.

Suppose its dynamic branch at depth `n` returns `R_n`, root `r_n`, and
`Y_n=Prefix(r_n,R_n)`.  Put `beta_n=absorption(r_n)`.  Exact cap-Nash debt
scaling and global minimality give

```text
beta_n D_* <= D_n-D_*.                                 (5.1)
```

More sharply, if `D(Y_n)>=D(X_infinity)`, then

```text
beta_n D_* <= D_n-D(X_infinity).                       (5.2)
```

Indeed

```text
beta_n D(R_n)=D(R_n)-D(Y_n),
D_*<=D(R_n)<=D_n.
```

Thus for every fixed `kappa>0`, all sufficiently late dynamic reset roots
with `beta_n>=kappa` satisfy

```text
D(Y_n) <= D(X_infinity)-kappa D_*/2.                   (5.3)
```

Conversely, any dynamic selections which never cross below the port debt
have `beta_n->0`.  In the minimum-port case `D(X_infinity)=D_*`, `(5.1)`
forces `beta_n->0`; an individual finite-depth `beta_n` may still be
positive.  Only the dispatcher applied at the exact limiting target is
forced into its all-Continue stall arm.

This is the exact quantitative boundary: a fixed-charge reset at the port
forces a fixed semantic-debt drop, while avoidance of such a drop collapses
all reset roots to the all-Continue face.

## 6. Small obstruction tests

### 6.1 Scalar interface regression

The inequalities alone permit

```text
D_*=1,
D_n=2+1/(n+1),
D(R_n)=D_n,
D(Y_n)=2+1/(2(n+1)).
```

Then every dynamic branch is strict, but its absorption tends to zero and no
`Y_n` lies below the limiting port debt `2`.  Hence strictness without a
fixed charge gives neither well-founded termination nor a near-return.

### 6.2 Checked cap-face regression

`positive_incidence_and_toggle_but_only_allContinue_capNash` in
`TerminalSemanticResetIncidenceCapReturn.lean` gives a literal two-player
joint carrier point with zero reset-owner debt, unit incidence, a supported
strict toggle, positive total debt, and only the all-Continue exact cap root.
It is not a Fin4 paid-port counterexample.  It does prove that the fields
retained in `(2.3)--(3.3)` cannot, by themselves, exclude arm 2 of Theorem
4.1.

### 6.3 Why the paid rows do not pass to the limit

At every finite `n` the actual profile `sigma_n` has a shifted paid row with
uniform gain.  Its first disagreement is shifted outward with `n`.  The law
limit retains a positive fraction of the old terminal outcomes, but it does
not retain a finite quit-time witness on one limiting behavioral profile.
Treating that escaping clock as a paid row at `X_infinity` would be exactly
the invalid compactness step the cap-port construction avoids.

## 7. Conjecture-facing conclusion and missing producer

The same-source port now has an exact closure-level discharge:

```text
summable actual paid cap port
  -> law-enriched reset target at its semantic limit
  -> strict debt descent below the port
       OR exact all-Continue reset stall.
```

This is stronger than the original semantic-only port, but it still stops
short of the accepted paid near-return output.  A closing theorem must add at
least one of the following genuinely new implications:

1. a source-native consumer of the all-Continue stall which uses the
   **outward-shifting Never-oriented paid clock**, not merely its terminal
   law;
2. a regeneration theorem attaching another same-source paid cap port to the
   lower carrier point `Y` in `(4.2)`, with a fixed debt/support rank decrease;
   or
3. a chronological connector from the dynamic edge at `B(R)` to the existing
   cap orbit `B_n`.

A lower bound on dynamic reset charge would be sufficient for a quantitative
debt descent by `(5.3)`, but it is not implied by incidence, the atom, or the
static toggle.  The checked regression shows why.

## 8. Source and novelty audit

Inspected declarations:

- `quittingTerminalOutcomeMass_rootThenContinuation`,
  `quittingTerminalOutcomeLawPrefix_outcomeMass`,
  `quittingTerminalOpponentIncidenceMass_lawPrefix`, and
  `quittingTerminalSemanticLawPrefix_mem_carrier` in
  `TerminalSemanticResetIncidenceReturn.lean`;
- the coordinate debt-scaling theorem in
  `TerminalCapNashEndpointTransport.lean`;
- `QuittingPaidCapLiftedSource.nonempty_summablePort` and its reach/debt
  identities in `PaidCapLiftedSummablePort.lean`;
- the checked composite in `FinFourSameSourcePaidResetCapPort.lean`;
- `exists_fixedLawResetDispatch` and the local cap-face regression in
  `TerminalSemanticResetIncidenceCapReturn.lean`;
- `QuittingFixedLawResetDispatch.prescribed_eq_target` and
  `allContinue_of_target_debt_le_source`; and
- `QuittingTerminalExploitabilityWitness.exists_exactToggle_gain` in
  `Collision/Toggles/FiniteInstability.lean`, used at the pigeonholed heavy
  coalition itself; and
- the minimum-fiber isolation/debt-moat declarations, which are compatible
  with (but do not supply) the joint-law limit above.

The existing cap port constructs only a semantic-pair limit.  The new step is
the summable-variation construction of a compatible complete-law limit with
the exact domination `(2.4)`, followed by reset dispatch at that port and the
quantitative fixed-charge/debt-drop boundary `(5.1)--(5.3)`.  No existing
named declaration located in the inspected dependency subtree states this
composition.

Requested independent checks:

- the `l1` variation constant `2a_n` and closed joint-carrier passage;
- coordinatewise suffix-law domination and the `sigma/8` Fin4 atom;
- exact hypotheses and orientation of the fixed-law reset dispatcher at the
  limit;
- inequalities `(5.1)--(5.3)`; and
- the strict nonclaims about an actual limiting profile, a `U`-path, or a
  chronological connector.
