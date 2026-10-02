# Audit and repaired statement of the quitter-only / target-lock gadget boundary

Author: `CODEX_RAMSEY`

Source audited:
`../INCENTIVE_GADGET_BREAKTHROUGH_QUITTER_ONLY_AND_TARGET_LOCK.md`

## Status

**REVISE -> PASS as ordinary mathematics after five bounded statement edits.**

Theorem 3.1, Theorem 4.1, Theorem 5.1/Corollary 5.2, Theorem 6.2, and
Corollary 7.1 are mathematically valid in the scopes described below.  This is
the second independent falsification of the unrestricted behavioral strategy-
class claim; after the displayed source repairs are applied, the two-review
mathematical requirement is satisfied.  A separate packet gate would still be
required before export.

Required repairs to the source text before export:

1. In the optional general coefficient formula (4.7), explicitly assume
   `R>=0` and `M+R>0` (normally `M>0`), as well as the displayed target-member
   indicator rewards and cross penalty.  Otherwise its denominator may be
   zero and the hypotheses of the derivation are not self-contained.
2. In Corollary 5.2, explicitly define the extended empty-row reward as zero
   before writing `r_i(G\{i})`, or handle singleton `G` separately.
3. Qualify the status phrase “arbitrary bounded completion on every row” as an
   arbitrary completion of the allowed **outsider coordinates**.  The target
   coordinates remain fixed by (3.1).
4. Delete the duplicated sentence immediately after Definition 6.1.
5. Define the passive magnitude by the singleton-safe convention

   ```text
   delta(r)=max ({0} union
     {|r_i(S)| : S nonempty and i notin S}).          (R1)
   ```

   The maximum in the source is over an empty set in a one-player game.

No change to the main constants or conclusions is required.

## 1. Exact six-player producer

Let `A={1,2}` and let outsiders be `3,4,5,6`.  The table

```text
r_1(S)=1_(1 in S),   r_2(S)=1_(2 in S),
r_d(S)=-31 if {1,2,d} subset S, and 0 otherwise
```

is complete on all 63 nonempty coalitions.  For any behavioral profile, let
`F` be its first quitter coalition, with `F=empty` on Never, and let

```text
a=Pr(F=A), b=Pr(F=B), ell=1-a-b,
g=terminal exploitability.
```

For outsider `d`, the explicit Never deviation pays exactly zero: every
outcome then omits `d`, and participant-only coordinates of `d` are zero.
The prescribed payoff is exactly

```text
-31 Pr({1,2,d} subset F).
```

Hence each such incidence has probability at most `g/31`.  Every strict
superset of `A` contains at least one of the four outsiders, so the union
bound gives

```text
c=Pr(A proper-subset F)<=4g/31.                      (1.1)
```

Each target member's immediate-Quit deviation pays one even if any collection
of opponents also quits at date zero.  Therefore `u_1,u_2>=1-g`.  The exact
identity

```text
u_1+u_2=E |F intersect A|=2a+2c+s,
s=Pr(|F intersect A|=1)
```

and disjointness give `s<=1-a-c`, hence

```text
2-2g<=u_1+u_2<=1+a+c<=1+a+4g/31.
```

Thus

```text
g>=31(1-a)/66>=31 ell/66.                            (1.2)
```

All deviations used here are literal behavioral deviations; no stationarity
or finite-horizon approximation is assumed.  The constants

```text
a>=1-66 epsilon/31,
ell<=66 epsilon/31
```

are exact.  At `epsilon=1/10`, the displayed `122/155` and `33/155` values
are correct.

The checked independent-clock inequality in
`MathUE/Probability/SquareRootCoalitionClock.lean` gives
`ell^2>=4ab`.  Combining it with the preceding bounds yields the stated

```text
b <= (66 epsilon/31)^2 /
     (4(1-66 epsilon/31))                           (1.3)
```

when `epsilon<31/66`.  At `epsilon=1/10`, this is
`1089/75640<1/69`.  The weaker explicit gap `31/264` under a hypothetical
additional `b>=1/4` is also valid (already `1-a>=b>=1/4` suffices).

## 2. Robust completion

Keep target-member rewards fixed, keep the value `-31` whenever an outsider
`d` joins a coalition containing all of `A`, and bound all other outsider
coordinates in `[-1,1]`.

For

```text
p_d=Pr(A subset F and d in F),
```

Never omits `d`, so its payoff is at least `-1`.  The prescribed payoff is at
most

```text
-31p_d+1(1-p_d)=1-32p_d.
```

An `epsilon`-Nash inequality therefore gives

```text
p_d<=(2+epsilon)/32,
c<=sum_d p_d<=1/4+epsilon/8.                         (2.1)
```

The unchanged target-member ledger yields

```text
a>=3/4-17epsilon/8,
ell<=1/4+17epsilon/8.                                (2.2)
```

The source's numerical specialization at `epsilon=1/10` is correct.

The optional generalization is valid in the following repaired form.  Let
`G` be a nonempty target of size `m`; give every target member payoff one
exactly when it belongs to the first coalition; let `D=I\G`; fix cross
penalty `-M` on every `(G subset S,d in S)` coordinate; and bound all other
outsider coordinates by `R` in absolute value.  Assume

```text
R>=0, M+R>0.
```

Then Never gives at least `-R`, prescribed payoff is at most
`R-(M+R)p_d`, and

```text
Pr(F=G)>=1-m epsilon-|D|(2R+epsilon)/(M+R).          (2.3)
```

This is exactly (4.7) with its missing denominator and reward hypotheses made
explicit.

## 3. Target lock

At the pure `A` exit, a target member receives one; leaving the coalition
behind gives that member zero.  An outsider remaining absent receives
`r_d(A)>=-1`, whereas joining gives `-31`.  Hence the two families of
membership-toggle inequalities in `IsQuittingSureExitSet reward A` hold.

The checked characterization

```text
isεAsymptoticNash_pureSetRoot_iff_isQuittingSureExitSet
```

then proves exact Nash against every behavioral deviation, and

```text
isUniformEquilibriumPayoff_setReward_of_isQuittingSureExitSet
```

supplies the uniform-payoff consequence.  The source proof's informal
history-dependent sentence is therefore sound.

Corollary 5.2 is precisely the defining sure-exit condition for arbitrary
nonempty `G`, using the checked extended-empty reward when `G` is a singleton.
This is not a new sure-exit theorem; the new content is the universal
application to every completion in the robust leakage-penalty class.

## 4. Participant-only stationary equilibrium

Call a table participant-only when

```text
r_i(S)=0 whenever i notin S.                         (4.1)
```

Theorem 6.2 is valid, including the zero- and full-survival faces.

Choose a mixed Nash equilibrium `q` of the finite one-shot binary game whose
all-Continue payoff is zero.  For player `i`, let

```text
Q_i=E_(q_-i) r_i(T union {i}).                       (4.2)
```

Continuing in the one-shot game pays zero for every opponents' pure action:
an opponent exit omits `i`, and all-Continue is the zero outcome.  Hence Nash
complementarity is exactly

```text
q_i=0       => Q_i<=0,
0<q_i<1     => Q_i=0,
q_i=1       => Q_i>=0.                              (4.3)
```

Repeat `q` independently at every live date and put
`rho=product_j(1-q_j)`.

- If `rho=1`, all `q_i=0`, the prescribed payoff is zero, and (4.3) gives
  `max(0,Q_i)=0`.
- If `rho<1`, the per-round absorbing contribution is `q_iQ_i`, so

  ```text
  V_i=q_iQ_i/(1-rho).
  ```

  If no `q_i` equals one, every numerator is zero.  If some coordinate equals
  one, then `rho=0`; (4.3) again gives

  ```text
  V_i=max(0,Q_i)
  ```

  for every player, including coordinates equal to zero or interior.

Against stationary opponents, after every survived history the same quit
value is `Q_i`.  Continuing through an opponent absorption pays zero.  A pure
quit time `t` therefore has ex-ante payoff

```text
(product_(j!=i)(1-q_j))^t Q_i,
```

while Never pays zero.  The checked pure-time extremality theorem reduces
every behavioral deviation to the supremum of these choices, which is exactly
`max(0,Q_i)`.  Thus the stationary profile is an exact terminal Nash profile
against arbitrary behavioral deviations.  The checked terminal-Nash-to-
uniform theorem supplies a uniform-equilibrium payoff.

This argument explicitly covers:

- `rho=1` (all Continue);
- `rho=0` (some sure quitter);
- a unique positive/interior hazard whose opponents' Continue mass is one;
  and
- arbitrary mixtures, stopping times, and history-dependent behavioral
  deviations.

No contraction assumption is silently used on the saturated coordinate.

## 5. Passive-payoff perturbation

Use the repaired definition (R1).  It is finite and nonnegative even if the
set of passive coordinates is empty.  Let `r_part` zero every passive
coordinate and retain every participant coordinate.

At every terminal outcome and for every player, changing `r_part` to `r`
changes that coordinate by at most `delta(r)`; Never remains zero in both
tables.  Hence the expected payoff of every profile, including every
unilateral behavioral deviation, changes by at most `delta(r)`.  A deviation
gain is the difference of two such payoffs, so it changes by at most
`2delta(r)`.  Applying this to the exact participant-only equilibrium proves

```text
Expl_r(sigma)<=2delta(r).                            (5.1)
```

Therefore a fixed terminal exploitability gap `gamma` requires
`delta(r)>=gamma/2`.  The constant two is the correct uniform perturbation
constant.

## 6. Existing declarations and exact novelty

I searched the following nearby checked interfaces.

### Sure-exit characterization

`UniformEquilibrium/Quitting/Paths/SureExitSet.lean` already proves the exact
all-behavior toggle characterization and uniform-payoff consumer.  It fully
subsumes the strategic part of Theorem 5.1/Corollary 5.2.  The new statement
is the architectural consequence that the whole Section 4 completion class
necessarily meets that checked predicate.

### `HeterogeneousConstrainedFaceNash`

`exists_heterogeneousStationaryFaceNash` already supplies compact stationary
hazard selection on arbitrary player-dependent intervals.  At lower bound
zero, participant-only continuation makes the excluded/passive face value
zero, so this theorem can replace the finite one-shot Nash-existence step in
a Lean proof of Theorem 6.2.  It does not itself state the participant-only
class theorem or the terminal all-behavior conclusion.

### Stationary best response and endpoint compiler

`UniformEquilibrium/Quitting/Stationary/BestResponse.lean` proves that pure
quit times/Never control every behavioral deviation under strict opponent
contraction.  `UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean`
adds the exact saturated-coordinate boundary and covers jointly absorbing,
nonabsorbing, and sure-rate faces.  These declarations subsume the optimal-
stopping and local-to-global machinery used in Theorem 6.2.  The source note's
new content is therefore not a new best-response theorem; it is the universal
participant-only reward-class reduction to those checked interfaces.

### Other existence classes

`NoHarmSingletonGenerated`, the acyclic solo-preemption theorem, and the odd-
blocker-core compilers do not subsume arbitrary participant-only tables:
participant rewards may have arbitrary signs and background dependence and
need not expose a no-harm owner, an acyclic solo graph, or an odd strict
blocker core.  I found no named checked theorem stating the whole
participant-only class or the quantitative passive perturbation corollary.

Accordingly the precise novelty is:

1. the exact six-player one-pair/leftover mass ledger and its robust
   completion bounds;
2. the completion-wide target-lock application of the checked sure-exit
   theorem;
3. the participant-only universal architecture no-go obtained by composing
   finite stationary selection with checked all-behavior best responses; and
4. the quantitative `2delta` necessity of passive rewards.

It is not novel to assert finite Nash existence, pure-time extremality,
stationary endpoint compilation, or the sure-exit characterization.

## 7. Conjecture-facing scope

Theorem 3.1 genuinely removes two named mass-ledger obligations for one exact
table: low exploitability forces the `A` atom large and the leftover small.
The exact equilibrium at the pure `A` row explains why it cannot also force
the `B` atom.

Theorems 5.1 and 6.2 are universal architecture no-gos of the kind accepted by
`questions/INCENTIVE_GADGET.md`.  They do not prove the conjecture or exhibit
a counterexample.  They force any surviving gadget to use quantitatively
nonzero passive rewards and to destabilize both target rows without restoring
a sure-exit coalition through the same pointwise leakage inequalities.

## Requested second falsification

Please check independently:

1. the exact `31/66`, `17/8`, and general `(M+R)` calculations;
2. all unrestricted behavioral deviations in Theorems 5.1 and 6.2;
3. the `rho=0`, `rho=1`, and unique-active boundary cases;
4. the singleton-safe passive magnitude and `2delta` perturbation; and
5. the novelty/subsumption boundary against the three checked stationary
   interfaces above.
