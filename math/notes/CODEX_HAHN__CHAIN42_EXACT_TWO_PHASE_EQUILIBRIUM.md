# Exact two-phase equilibrium for the asymmetric chain-42 table

Author: `CODEX_HAHN`

## Status

**Exact ordinary-mathematics exclusion of one tracked rational negative
candidate; not Lean-checked.**  The normalized table called `chain-42-best`
by the exact-search campaign has an absorbing period-two terminal Nash profile
against unrestricted behavioral deviations.  Existence of the four interior
hazards is certified by an exact rational Poincare--Miranda box; the four
inactive inequalities hold there with a fixed strict margin.

Consequently this table has a uniform-equilibrium payoff and admits no
positive semantic barrier, including no moment-tight contact-cone barrier.
The result eliminates one highly asymmetric tracked table.  It is not a
theorem about the whole contact-cone grammar or about all screened-hard
tables.

## 1. The exact table

Players are `0,1,2,3`.  In coalition-mask order, the normalized rational
reward table is

| mask | coalition | player 0 | player 1 | player 2 | player 3 |
|---:|---|---:|---:|---:|---:|
| 1 | `{0}` | `1/4` | `1` | `0` | `0` |
| 2 | `{1}` | `1` | `1/4` | `-741/5878` | `-368/6713` |
| 3 | `{0,1}` | `2929/9134` | `1/4` | `373/1373` | `1/4` |
| 4 | `{2}` | `557/5348` | `-538/9753` | `836/2699` | `1` |
| 5 | `{0,2}` | `1/4` | `1049/3748` | `313/1811` | `229/5726` |
| 6 | `{1,2}` | `0` | `2131/7484` | `1/4` | `1254/4889` |
| 7 | `{0,1,2}` | `1144/6363` | `-145/8406` | `475/4969` | `-289/1839` |
| 8 | `{3}` | `0` | `-539/4968` | `1` | `45/188` |
| 9 | `{0,3}` | `1/4` | `0` | `1810/7151` | `1754/5213` |
| 10 | `{1,3}` | `776/2109` | `1/4` | `-165/5366` | `1790/6427` |
| 11 | `{0,1,3}` | `21/6086` | `2672/9075` | `252/3835` | `571/7198` |
| 12 | `{2,3}` | `1021/4024` | `626/3817` | `1/4` | `2227/3605` |
| 13 | `{0,2,3}` | `0` | `-1/4` | `-109/8161` | `1/4` |
| 14 | `{1,2,3}` | `0` | `0` | `1/4` | `575/9816` |
| 15 | `I` | `-404/2135` | `-1/4` | `-1871/8228` | `-1113/8915` |

Its canonical exact-search digest is

```text
5e9c89bf03444bd36d02b70332bae2dc848cc6b11146d7c0e9a47416fbdb346f
```

## 2. Period-two root pattern

At phase zero use

\[
 x^0=(a,0,0,d),
\]

and at phase one use

\[
 x^1=(0,b,c,0).
\tag{1}
\]

Thus players `0,3` mix only at phase zero and players `1,2` mix only at
phase one.  For a root `x`, let

\[
 \alpha(x)=\Pr_x(\hbox{all Continue}),
\]

let `G_i(x)` be the prescribed absorbing contribution, let `Q_i(x)` be
player `i`'s pure-Quit endpoint, let `A_i(x)` be the opponent-absorption
contribution after player `i` Continues, and let `chi_i(x)` be the probability
that all opponents of `i` Continue.

The unique bounded two-period prescribed values are

\[
 V_i^0={G_i(x^0)+\alpha(x^0)G_i(x^1)
          \over1-\alpha(x^0)\alpha(x^1)},
 \qquad
 V_i^1=G_i(x^1)+\alpha(x^1)V_i^0.
\tag{2}
\]

Define the four active Quit-minus-Continue differences

\[
 \begin{aligned}
 E_0&=Q_0(x^0)-A_0(x^0)-\chi_0(x^0)V_0^1,\\
 E_1&=Q_3(x^0)-A_3(x^0)-\chi_3(x^0)V_3^1,\\
 E_2&=Q_1(x^1)-A_1(x^1)-\chi_1(x^1)V_1^0,\\
 E_3&=Q_2(x^1)-A_2(x^1)-\chi_2(x^1)V_2^0.
 \end{aligned}
\tag{3}
\]

Clearing the nonzero rational constants and the common denominator in (2)
gives the following integer numerator polynomials, in variable order
`(a,d,b,c)`:

\[
\begin{aligned}
 f_0={}&4568bcd-4568bc-4011bd+4011b+780cd-780c-1337d,\\
 f_1={}&-3123367331119a^2bc+3123367331119a^2b
       +3123367331119a^2c-3123367331119a^2\\
 &+17575866631306abc+6338926945914ab
       -27589225110482ac-7699046154345a\\
 &-14452499300187bc-9462294277033b+24465857779363c,\\
 f_2={}&-1049812920ac^2d+1049812920ac^2
       +20435126047acd-23713658766ac\\
 &-19385313127ad+22663845846a+1049812920c^2d
       -1049812920c^2\\
 &+9783335081cd-9221541570c-10833148001d,\\
 f_3={}&13555828905ab^2d-13555828905ab^2
       +85630989083abd+83835971321ab\\
 &-99186817988ad-70280142416a-13555828905b^2d
       +13555828905b^2\\
 &-143061282723bd-98883556034b+156617111628d.
\end{aligned}
\tag{4}
\]

Zeros of `(f_0,f_1,f_2,f_3)` in the box below are exactly zeros of the four
active endpoint differences (3).

## 3. Exact Poincare--Miranda certificate

Let the rational center be

\[
 z_0=left(
 {71799\over400000},
 {225037\over1250000},
 {1170183\over10000000},
 {267491\over2000000}
 \right)
\tag{5}
\]

and let `B` be the closed coordinate box of radius `1/100000` around `z_0`.
In particular `B` is strictly inside `(0,1)^4`.

Use the rational preconditioner

\[
 A=\begin{pmatrix}
-633172/10^9&-57/10^{15}&-31841/10^{15}&-11561/10^{15}\\
-452407/10^9&-72/10^{15}&-73810/10^{15}&-5336/10^{15}\\
-70906/10^9&-43/10^{15}&-63906/10^{15}&-7390/10^{15}\\
-426772/10^9&-3/10^{15}&-53639/10^{15}&-11043/10^{15}
\end{pmatrix}.
\tag{6}
\]

It is invertible, with

\[
 \det A=
 {-4241658441945089\over
  250000000000000000000000000000000000000000000000000000}<0.
\tag{7}
\]

Put `g=A f`.  Expand every `g_i(z_0+y)` exactly as a polynomial in `y` and
evaluate it by rational natural interval arithmetic on
`[-1/100000,1/100000]^4`.  On the two faces perpendicular to coordinate `i`,
the exact enclosures satisfy, simultaneously for all four `i`,

\[
 \begin{aligned}
 y_i=-1/100000&\quad\Longrightarrow\quad
 g_i\in[-103/10^7,-97/10^7],\\
 y_i=+1/100000&\quad\Longrightarrow\quad
 g_i\in[97/10^7,103/10^7].
 \end{aligned}
\tag{8}
\]

These are rational inclusions, not floating-point evaluations.  The
Poincare--Miranda theorem therefore gives a point

\[
 (a,d,b,c)\in B
\]

with `g=0`.  Since `A` is invertible, `f=0`, hence every active endpoint
difference in (3) is zero.

For orientation only, the certified root is near

```text
a = 0.1794974934424661266...
d = 0.1800295953294771630...
b = 0.1170182963398209544...
c = 0.1337454841649917958...
```

## 4. Strict inactive inequalities

Evaluate the other two players' endpoint differences at each phase on the
same exact rational box.  Natural interval evaluation of their rational
functions gives

\[
 \begin{array}{c|c|c}
 \text{phase}&\text{inactive player}&Q-C\\ \hline
 0&1&[-0.051074,-0.051013]\\
 0&2&[-0.089286,-0.089225]\\
 1&0&[-0.048849,-0.048800]\\
 1&3&[-0.027806,-0.027758].
 \end{array}
\tag{9}
\]

The decimal endpoints in (9) are outward-rounded displays of exact rational
intervals.  In particular every interval is contained in

\[
 (-\infty,-1/50).
\tag{10}
\]

The common Bellman denominator is also uniformly positive on the box:

\[
 0.485369
 <1-\alpha(x^0)\alpha(x^1)
 <0.485418.
\tag{11}
\]

Thus all rational functions used above are well defined.  At the certified
point, every inactive player strictly prefers Continue and every active
player is indifferent between Quit and Continue.

## 5. Unrestricted behavioral equilibrium

Because each active hazard lies strictly between zero and one, the prescribed
mixture at its active phase has value equal to both pure endpoints.  At its
inactive phase the player chooses its strictly optimal Continue endpoint.
Therefore, for every player and both phases,

\[
 V_i^t=\max\{Q_i(x^t),
 A_i(x^t)+\chi_i(x^t)V_i^{t+1}\}.
\tag{12}
\]

Against any fixed player, at least one opponent has a positive hazard in
each complete two-phase cycle.  The player-deleted survival over a cycle is
therefore strictly below one.  The two-phase optimal-stopping Bellman operator
is a strict contraction over a complete cycle, so (12) is its unique bounded
fixed point.  It controls every deterministic stopping time, including Never
and arbitrarily late stops.  Randomized behavioral replacements are mixtures
of those stopping times and cannot do better.

Hence the period-two behavioral profile is an exact terminal Nash profile
against unrestricted unilateral deviations.  It absorbs almost surely and
its phase-zero payoff vector is a uniform-equilibrium payoff.

## 6. Consequence for negative certificates

The profile above is a literal infinite periodic root word, so its semantic
pair belongs to the closure of the finite-word orbit of all-Never.  Its debt
vector is zero.  Every closed set containing all-Never and invariant under all
product-root prefixes must contain this semantic point.  Therefore no such
set can have a positive debt floor.

In particular, for this table the exact moment-tight contact-cone invariance
sentence is infeasible for every positive `gamma` and all finite parameters
`L,C`.  This is an exact rejection of the tracked candidate, not evidence
that the grammar is infeasible for an unknown counterexample table.

## 7. Boundary and nonclaims

- The numerical optimizer's earlier residual near `4.7e-4` was not evidence
  of a positive gap; the exact algebraic root lies nearby.
- The proof uses a two-phase word and complete behavioral caps.  It is not a
  stationary-grid or finite-deviation-menu check.
- The rational box certifies existence, not uniqueness, of the active root.
- No claim is made that every tracked candidate has such a two-phase root.
- No positive barrier, counterexample, or proof of the Fin4 conjecture is
  obtained.

## 8. Sources inspected

- `Experiments/fin4_exact_search/fin4_exact_search/candidate_campaign.py`;
- `Experiments/singleton_collision_candidate_search/results.json`;
- `Experiments/singleton_collision_candidate_search/singleton_collision_candidate_search.py`;
- `notes/CODEX_HAHN__MOMENT_TIGHT_CONTACT_CONE_BARRIER_ANSATZ.md`; and
- `UniformEquilibrium/Diagnostics/Quitting/ExactRepairCertificate.lean` for
  the finite-cycle unrestricted-deviation semantics.

