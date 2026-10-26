# A no-child benchmark with exact stationary and sure-root exclusions

This is a benchmark and a coverage audit, not a counterexample to UE.
The M=14 table below has an exact finite certificate excluding every
stationary terminal Nash profile and every sure-first terminal Nash profile
with arbitrary behavioral continuation. Several complete raw producer
families also fail. Arbitrary nonstationary strategies remain unresolved.

## Table

Original absorbing rewards are r_i(D)=4+Z_i(D), with live/Never zero.
Own native singleton rewards are zero, and the singleton matrix is

 Gamma=[0,-1,-1,2; -1,0,1,1; 1,2,0,-1; 1,-1,1,0].

For every nonsingleton D, put Z_i(D)=-5 when i belongs to D and Z_i(D)=0
otherwise. With successor cycle

                 0 -> 1 -> 3 -> 2 -> 0,

replace precisely four participant entries by

          Z_successor(j)({j,successor(j)})=M-1.

Take M=14, so those four entries are13. Every remaining native participant
nonsingleton is-5, and every passive nonsingleton is0. These rules specify
all60 original absorbing reward coordinates.

The matrix has determinant11 and

 Gamma^-1=(1/11)[3,-2,4,5; 1,3,5,-2; -2,5,1,4; 5,4,3,1].

Its unique positive inverse column is2. All other columns are mixed. The
principal triple determinants are1,1,3,3. The reciprocal opposition graph
is the path0--2--3--1, hence there is no positive-inverse triple. All columns
have a negative entry. Principal nonsingularity gives R0, and the unique
full root at offset-e2 gives degree+1, as proved in the
[residual partition](CODEX_COORDINATOR__FIN4_RESIDUAL_PARTITION.md).

## Exact stationary certificate

For q in[0,1]^4, let H_i be opponent survival, P_i the expected native
reward from their nonempty quitter coalition, and Q_i the native reward
from quitting against that coalition. Put

                  F_i=(1-H_i)Q_i-P_i.

Every stationary terminal Nash profile has F_i<=0 at q_i=0, F_i>=0 at
q_i=1, and F_i=0 at0<q_i<1. All Continue is not Nash because a solo quit
pays4 instead of0. Enumerate the other80 patterns in{quiet,sure,mixed}^4.
For a pattern, set quiet coordinates0, sure coordinates1, and bound the
mixed coordinates on their closed unit cube.

The checker uses these sound rules:

1. A pure pattern is rejected by an exact violated scalar sign.
2. For one mixed player and no sure player, an actual quiet-row restricted
   polynomial has nonnegative coefficients and is not zero. It is strictly
   positive at every positive free coordinate. The checker verifies this
   property from the new table. In fact the designated successor's field is
   q+(M-1)q^2, but no inherited family shortcut is assumed.
3. For at least two mixed players S and no sure player, write the active
   field as -Aq+R(q), where A=Gamma_SS and every monomial in R has degree
   at least2. The checker verifies all constant and linear coefficients.
   If V=A^-1 and C_j is the coefficient absolute sum of R_j, then an
   active zero satisfies ||q||infty<=K||q||infty^2, where
   K=max_i sum_j|V_ij|C_j. Thus a nonzero zero is outside the dyadic origin
   cube of side2^-E<1/K. If K=0, no nonzero zero exists. This is the only
   analytic removal of a box that has no strict polynomial contradiction.
4. Add the exact active equations V F_S=0. Convert all restricted
   polynomials to tensor Bernstein coefficients at their maximum occurring
   coordinate degree, with minimum degree1. Strict one-sided coefficients
   contradict an opposing weak sign or equality. Clear the common positive
   denominator and bisect using exact integer de Casteljau formulas.

For degree d on a fiber, the coefficients on the left and right halves,
multiplied by2^d, are

 left_r=2^(d-r) sum_(j=0)^r binom(r,j)b_j,
 right_r=2^r sum_(j=0)^(d-r) binom(d-r,j)b_(r+j).

These are exact restrictions, and the two child boxes cover their parent.
Patterns, free axes and coefficient indices are lexicographic; split the
free axis with least subdivision depth, break ties in player order, and
visit the left child first. Choose the first positive E with2^-E<1/K.
Abort before subdividing if node count exceeds100000 or coordinate depth
exceeds35. A failure makes no exclusion claim. For M=14 every box is
removed, totaling560 nodes including analytic shortcuts.

The standard-library checker is
[CODEX_NO_CHILD__BENCHMARK_EXACT_CHECK.py](../experiments/CODEX_NO_CHILD__BENCHMARK_EXACT_CHECK.py).
Its default command reports exactly:

```
EXACT RATIONAL PASS: M=14; all80 nonzero stationary patterns excluded; 560 nodes
EXACT RATIONAL PASS: M=14; all65 sure-root patterns excluded; 65 nodes
```

## Sure-first exclusion with unrestricted continuations

The same checker forms G_i=Q_i-P_i+4H_i. The value-4 is a valid native
lower bound for a player's full response in any continuation: never quit
gives only passive absorbing original rewards at least3, or Never0.
On a root containing a sure quitter, every other player has H_i=0. If
there is just one sure quitter, replacing its continuation response by
this lower bound increases its quitting advantage, preserving its necessary
nonnegative sign. Thus the usual quiet/sure/mixed signs for G are necessary.
All65 sure-root patterns fail immediately by exact Bernstein signs, without
subdivision. This prices arbitrary continuation laws rather than only
stationary continuations.

There is also a direct proof for every M>0. If j surely quits, every player
other than j and successor(j) strictly Continues: joining gives original-1,
whereas remaining outside any nonempty opponent coalition gives at least3.
The successor must then surely join, gaining M against j. Player j can
withdraw from the pair payoff-1 to a passive singleton payoff at least3.
This contradicts root Nash and exhausts every possible sure owner.

## Complete raw criteria and a solved boundary control

The same construction at M=10 is already solved. Its only premium trap is the full
player set, since every positive participant pair follows the single4cycle.
At uniform weights, its support-local forced-Quit upper averages are0 on
empty, -1 on singletons, -6 on cycle pairs, and-20 otherwise. Therefore
[the mixed-support upper-average theorem](../exports/MIXED_SUPPORT_UPPER_OR_CHARGE_UNIFORM_EQUILIBRIUM.md) proves UE there.
The exact stationary/sure-root exclusions at M10 remain valid, but they
do not separate that older nonstationary producer.

For M14 the following complete premise failures hold:

* **Upper averages and boxed charges.** The full set is still the only
  premium trap. Summing its four singleton upper-average tests gives
  (M-11)sum_i w_i=3sum_i w_i>0 for every nonzero nonnegative w.
  No such upper certificate exists. Its singleton boxed-charge quantity
  P_I({j})=M-11=3 is positive, so the required strictly negative range
  fails. This rejects the full-trap alternatives in the mixed-support and
  mixed-premium-trap theorems.
* **Every nonnegative joining ledger.** Summing the four singleton joining
  charges gives3w0+2w1+w2+2w3>0 for any nonzero nonnegative weight vector.
  Thus J({j})<=0 cannot hold for all four j. This rejects every weight
  support in the scalar and support-filtered ledger criteria. The stronger
  unfiltered H>=0 condition also fails independently: each passive triple
  has native reward0 outside and-5 inside, so nonzero weights make some
  proper-triple H strictly negative. Hence no finite family of such H
  ledgers can evade that obstruction.
* **All ordered anchor blocks.** If a marked player i lacks its predecessor
  in the marked set, their pair has only the positive marked premium13,
  violating its first-block cap. Marked sets must therefore be closed
  under the4cycle and equal I. For blocks, a predecessor cannot occur in
  a later block than its successor, so all players must share one block.
  The four pair caps then require13 lambda_successor<=5 lambda_owner;
  multiplication contradicts13^4>5^4. This also rejects calendar-polytope
  criteria requiring a proper marked subset and the same first-block caps.
* **General finite-invariant-cone alternating pairs.** Every pair has at
  least one participant premium-5, so that endpoint has
  c_i=Z_i(pair)-Gamma_i,mate<=-4<0. No pair partition satisfies the
  criterion c_i>0 for every player, irrespective of its proof-weight V.
* **Stationary producers.** Any claimed application of an exact stationary
  producer contradicts the complete stationary certificate. This covers
  the weighted dominance, strict/boundary inverse-column jackpot and
  contact-preserving bonus criteria when their full hypotheses hold.
* **Cyclic-child and full-positive-inverse hypotheses.** The matrix has no
  inverse-positive triple and has three mixed full inverse columns. These
  exact failures are invariant under all player relabelings and positive
  recipient scalings. Families requiring four opposite-sign cycle edges
  also fail because the opposition graph is only a three-edge path.
* **A protected participant row.** Every recipient has a positive native
  participant pair13. Thus no relabeling meets any theorem requiring one
  recipient's seven nonsingleton participant coordinates all nonpositive.
* **Scalar singular circuit.** Its four positive participant entries force
  roles along the displayed4cycle. Its negative singleton C3 and positive
  join at13 pin the unique mutually negative pair, leaving only role order
  (0,1,2,3)=(2,1,3,0). In that order its required denominator is
  D_X=M-5Z+(M-1)(-4-5Y)=4-3M-5Z-5(M-1)Y<0 for positive Y,Z,
  contrary to the criterion D_X>0. This rejects all relabelings of that
  finite scalar criterion, not just one natural role assignment.

These are exact premise failures, not claims that the corresponding broader
strategy architectures cannot solve the table. Unspecified qualitative
neighborhoods and arbitrary supplied-controller certificates have not been
classified. Proper-child singleton equilibria have an outside successor who
profits by joining; this rejects raw universal safety bounds, but by itself
does NOT rule out every possible nonstationary child equilibrium selection.
The table is therefore a useful no-child research target, not a proved
unrestricted counterexample and not a claim of universal producer coverage.

## Actual-source reduction for this family

The following uses the I2/I3/F/I4 notation and source definitions in
[the residual partition](CODEX_COORDINATOR__FIN4_RESIDUAL_PARTITION.md). It is
conditional on a positive absorbing gap, which has not been proved here.
The I2 and first two I3p exclusions hold for every M>0; all remaining
three-owner exclusions hold for M>11.

### Dispersion needs only the three displayed pair guards

The universal dispersion inequality
`D+beta epsilon>=c beta^2` from
[uniform three-owner dispersion](../exports/UNIFORM_THREE_OWNER_TAIL_DISPERSION.md) remains valid if full row
distinctness is replaced by `Gamma_ij!=0` and `J_ij!=Gamma_ij`, retaining
its pair guard `Gamma_ij J_ji-Gamma_ji J_ij!=0` and positive absorbing gap.
In that proof, Section5.3 uses nonzero Gamma to force positive tie mass,
uses `J!=Gamma` to exclude geometric contact ratio one, and uses the pair
guard to separate the two geometric rates. The coupling, normalized
response estimates, compactification and absorbing solo contradiction in
Sections2--6 use no other entry-distinctness assumption. The consumers in
Sections7--9 use only the proved inequality. Section10's generic
perturbation is source-access exposition, not a further step in the
universal dispersion proof. Thus the proof itself proves this weaker
version at the same table; no payoff perturbation or selected-minimum
transfer is used.

The benchmark satisfies all these weaker guards. In pair order
01,02,03,12,13,23, its determinants are

    (-M-4, 6-M, -5, 5, M-6, 6-M),

nonzero throughout M>11. At M14 these are (-18,-8,-5,5,8,-8).
Its four principal triple joining determinants `det(J-Gamma)`, in order
012,013,023,123, are `(-7M^2-144,-7M^2-144,-6M^2-252,-6M^2-252)`.
At M14 these are (-1516,-1516,-1428,-1428); thus the separate joining
nonsingularity guard of the actual-source construction also passes.
The deductions below require only the source-supplied ALL-END property,
zero observer debts, positive marginal Never masses, and positive absorbing
gap. They apply at M14 despite its repeated higher-coalition entries.

### Every actual I2 pair fails

For eleven of the twelve ordered pivot/observer pairs, the necessary contact
ratio `0<Gamma_ip/Z_i(ip)<1` fails. A positive singleton faces joining reward
-5. Each cycle successor has singleton -1 and joining reward M-1: the ratio
is negative for M>1, undefined at M=1, and greater than one for 0<M<1.

The only remaining ordered pair is `(p,i)=(1,0)`. Here rho=1/5,
`A=Gamma_10=-1`, and `C=Z_1(01)=M-1`, so the second necessary inequality is
violated strictly:

    A-rho C=-(M+4)/5<0.

This pair can also be rejected directly without any dispersion guard:
pivot ALL-END requires `(M-1)a0<=-f0` at every late date. Since
`0<=a0<=f0` and `f0>0`, the inequality is impossible when M>=1; when
0<M<1, its left side is at least `(M-1)f0>-f0`. Thus the all-M>0 I2
claim does not rely on guards for unrelated pairs at exceptional M values.

Thus no ordered I2 case survives. In particular all three cases at the
unique strict inverse-column pivot p=2 fail the first contact test.

### Two of the three I3p cases fail

With selected pivot2, the eventual owner set023 is impossible. Observer3's
premium predecessor1 is absent; every nonsolo joining reward available to
3 is -5. Its Quit payoff at every date is therefore nonpositive. Its Never
payoff is strictly positive, since both passive singleton rewards against0
and2 are +1, passive joint reward is zero, and both active opponents have
positive finite and Never masses. A zero-debt observer cannot quit at any
finite date under this strict comparison.

The same argument excludes owner set123 using observer1: its premium
predecessor0 is absent, and its two passive singleton rewards are +1.
Consequently only owner set012 survives these first two I3p exclusions.

### The remaining three-owner cases fail when M>11

Write `t=M-1>10`. Condition at each late date after all other owners' last
finite atoms. Let f_j be player j's remaining finite mass and a_j its current
atom, all in that mass-one conditional tail; set `beta=sum f_j`. For every
player i define E_i as its Never payoff minus its immediate-Quit payoff.
ALL-END gives `E_i>=0`; a zero-debt observer with a positive current atom
has `E_i=0`. Uniformly over the date,

    E_i=sum_(j!=i) Gamma_ij f_j
          -sum_(j!=i) Z_i(ij) a_j+O(beta^2).           (1)

Indeed passive singleton probabilities differ from f_j only when at least
two opponents have finite dates, an event of probability O(beta^2).
The immediate-Quit expectation differs from its singleton-atom expression
only when at least two opponents atomize now. All coefficients are fixed
and finite. Positive marginal Never masses give beta tending to zero.

In I3p with owner set012, dispersion and the direct ALL-END coupling bound
`d2<=2B f2(f0+f1)`, where B bounds absolute rewards, give `f2>=c beta`
for one fixed c>0: the two smallest finite masses sum to at most f2, so
`c0 beta^2<=d2+beta epsilon<=(2B+1)f2 beta`.
The three relevant leading gaps from(1) are

    E0=-f1-f2+5a1-t a2+O(beta^2),
    E1=-f0+f2-t a0+5a2+O(beta^2),
    E3=f0-f1+f2+5a0-t a1+5a2+O(beta^2).

There are arbitrarily late observer0 atoms. At one, E0=0 forces a1>0:
otherwise E0<=-f2+O(beta^2)<0. Thus observer1 is also active and E1=0.
The exact linear combination of the leading terms gives

    E3+E1+(t/5)E0
      =-(1+t/5)f1+(2-t/5)f2+(5-t)a0
          +(10-t^2/5)a2+O(beta^2).

Every displayed coefficient is negative for t>10. In particular the f2
term makes the right side strictly negative at sufficiently late dates.
The left side equals E3>=0, a contradiction. This excludes the last I3p
choice.

In I3o the owners are013. The quiet pivot's prescribed Never is optimal
by ALL-END, so total debt is zero. Three-owner dispersion gives
`min(f0,f1,f3)>=c beta`, in particular `f3>=c beta`.
Now

    E0=-f1+2f3+5a1+5a3+O(beta^2),
    E1=-f0+f3-t a0+5a3+O(beta^2),
    E3=f0-f1+5a0-t a1+O(beta^2).

At any sufficiently late observer0 atom, E0=0 and E1,E3>=0. But

    E1+E3-E0=-f3+(5-t)a0-(t+5)a1+O(beta^2)<0,

again a contradiction. This argument itself needs only t>=5.

Therefore for the benchmark at M=14, and throughout its parameter ray
M>11, all actual I2, I3p and I3o cases fail under the stated source
assumptions. An actual minimizing source must have finite owner support F
or all four infinite owners I4. Inherited endpoint cases remain separate;
no existence, global minimum, or UE conclusion is inferred from this
actual-source restriction.

### Exact finite last-root control at M=14

The local last-root necessary conditions do not eliminate F. Take independent
root hazards `q=(2/5,14/23,1/2,0)`, followed by the native Never value zero.
Writing P for each player's Continue offer and Q for its Quit offer gives

    P=(-1/2, 1/10, 102/115, 3/230),
    Q=(-1/2, 1/10, -88/23, -259/230),
    Q-P=(0,0,-542/115,-131/115).

Both active observers0,1 are indifferent, while the active pivot2 and quiet
observer3 satisfy the ALL-END comparison strictly. All hazards are below
one and the support has three owners. These fractions follow directly from
`H_i=prod_(j!=i)(1-q_j)`,
`P_i=H_i sum_(j!=i) Gamma_ij q_j/(1-q_j)`, and
`Q_i=-5(1-H_i)+18 H_i q_pred(i)/(1-q_pred(i))`.
This is an admissible local root only, not a minimizing source tuple or a
behavioral equilibrium profile. Its negative observer0 cap is permissible
at a descendant and prevents treating it as a positive-cap global minimum.
