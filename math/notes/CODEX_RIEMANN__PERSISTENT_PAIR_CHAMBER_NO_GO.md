# An open persistent-pair zero-debt chamber around the inert regression

Author: `CODEX_RIEMANN`

Linked note:
[`CODEX_RIEMANN__STRICT_INERT_RATIONAL_REALIZATION_AUDIT.md`](CODEX_RIEMANN__STRICT_INERT_RATIONAL_REALIZATION_AUDIT.md)

## Status

This note gives a rigorous nontrivial parameter chamber which cannot contain a
positive-gap table.  It arose by perturbing the checked rational cyclic
plateau while preserving its strict inert passport.

The chamber is larger than a small numerical neighborhood: all reward entries
outside the coalitions containing one fixed two-player base are arbitrary.  On
the relevant face, six explicit strict inequalities construct an exact
sure-exit mixed terminal Nash profile against every behavioral deviation.

An exact quarter-grid table in the chamber simultaneously has:

* the checked four-phase paid inert passport;
* pure-coalition exploitability at least `1/4` at every Boolean vertex; and
* an exact mixed terminal Nash profile.

Thus even the inert passport plus a uniform strict toggle at every pure
coalition is not evidence of a positive all-behavior gap.  A negative search
around this seed must cross one of the finite face walls below.

## 1. Persistent-pair chamber theorem

Let the four players be `f,s,h,o`, and put

\[
 B=\{f,s\}.
\]

The base players `f,s` will Quit surely.  The free players `h,o` use
independent Quit probabilities `y,z`, respectively.  Define the four free
membership gains

\[
\begin{aligned}
 a_0&=r_h(B\cup\{h\})-r_h(B),\\
 a_1&=r_h(B\cup\{h,o\})-r_h(B\cup\{o\}),\\
 b_0&=r_o(B\cup\{o\})-r_o(B),\\
 b_1&=r_o(B\cup\{h,o\})-r_o(B\cup\{h\}).
\end{aligned}
\tag{1}
\]

Assume the strict crossing signs

\[
 a_0<0<a_1,
 \qquad
 b_1<0<b_0.
\tag{2}
\]

Set

\[
 z={-a_0\over a_1-a_0},
 \qquad
 y={b_0\over b_0-b_1}.
\tag{3}
\]

Then `0<y,z<1`, and the two free players are exactly indifferent:

\[
 (1-z)a_0+za_1=0,
 \qquad
 (1-y)b_0+yb_1=0.
\tag{4}
\]

For `T subset {h,o}`, let

\[
 \pi_{y,z}(T)
 =y^{1_{h\in T}}(1-y)^{1_{h\notin T}}
  z^{1_{o\in T}}(1-z)^{1_{o\notin T}}.
\]

Define the base members' expected stay gains

\[
 G_f(y,z)
 =\sum_{T\subseteq\{h,o\}}\pi_{y,z}(T)
 \bigl[r_f(B\cup T)-r_f((B\setminus\{f\})\cup T)\bigr],
\tag{5}
\]

and analogously

\[
 G_s(y,z)
 =\sum_{T\subseteq\{h,o\}}\pi_{y,z}(T)
 \bigl[r_s(B\cup T)-r_s((B\setminus\{s\})\cup T)\bigr].
\tag{6}
\]

### Theorem

If (2) holds and

\[
 G_f(y,z)\ge0,
 \qquad
 G_s(y,z)\ge0,
\tag{7}
\]

then the root

\[
 x_f=x_s=1,
 \qquad x_h=y,
 \qquad x_o=z
\tag{8}
\]

defines a one-row repeated/stationary profile `sigma` which is an exact
terminal Nash profile against all behavioral deviations: for every player
`i` and every randomized history-dependent behavioral replacement `tau_i`,

\[
 U_i(\sigma[i\leftarrow\tau_i])\le U_i(\sigma).
\]

Consequently the global terminal debt minimum is zero and the table has a
uniform-equilibrium payoff.

### Proof

The base `B` contains two sure quitters, so absorption occurs at date zero
under (8) and after every unilateral behavioral deviation.  Each deviation
therefore reduces exactly to changing that player's date-zero Quit
probability.

For `h`, the Quit-minus-Continue payoff difference is

\[
 (1-z)a_0+za_1=0.
\]

For `o`, it is the second expression in (4).  Thus both free players are best
responding.  The corresponding differences for the two sure base players are
exactly (5) and (6), which are nonnegative by (7).  Hence both base players
are also best responding.  This proves exact Nash for the unrestricted
behavioral strategy class.  ∎

The strict version `G_f>0`, `G_s>0`, together with (2), defines an open
semialgebraic chamber: the probabilities in (3) and the gains in (5)--(6) are
continuous wherever the denominators in (3) are positive.

This is the explicit two-free-player specialization of the checked
persistent-base interfaces

```text
quittingPersistentBaseNashSet
nonempty_quittingPersistentBaseCertificate_of_inducedNash
exists_uniformPayoff_of_persistentBase_inducedNash_signs
```

in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/`.

## 2. Exact rational table surviving all pure screens

The targeted search used the script
[`codex_riemann_inert_perturbation_search.py`](../experiments/codex_riemann_inert_perturbation_search.py).
The search is only a producer of upper witnesses; its finite-clock values are
not lower certificates.  The following table, however, is now checked by an
ordinary exact calculation.  Coordinates are ordered `(f,s,h,o)`.

\[
\begin{array}{c|rrrr}
S&r_f&r_s&r_h&r_o\\ \hline
0001&0&0&0&0\\
0010&0&-3/4&0&-1/2\\
0011&1&1&0&-1\\
0100&0&1&-1&0\\
0101&1&0&-1&0\\
0110&1&0&-1&0\\
0111&0&1&-1&0\\
1000&-1/2&1/2&3/4&1\\
1001&3/4&1/4&1/4&1/2\\
1010&-1&3/4&-1/4&1/4\\
1011&3/4&1&1/4&0\\
1100&-1/2&3/4&1/2&-1\\
1101&1&0&1&-1\\
1110&1/2&-1&1/2&-1\\
1111&1/2&1&1/2&-1
\end{array}
\tag{9}
\]

Here the binary mask uses the player order `(f,s,h,o)`.  The four plateau
rows `0100,0101,0111,0110` are unchanged from
`FourPlayerCyclicPlateauCandidate.reward`, as are exactly the neighboring
coordinates needed for its cap passport.  Hence its four paid phase edges,
debt vectors, common cap `(1,1,0,0)`, and unique all-Continue cap--Nash root
remain intact.

Direct enumeration of all sixteen pure coalitions gives

\[
 \min_{C\subseteq I}\max_i
 [r_i(C\triangle\{i\})-r_i(C)]_+={1\over4}.
\tag{10}
\]

The minimum is attained at `C=1011`; every other Boolean vertex has a strict
toggle of at least `3/4`.  In particular, all-Never has exploitability one,
so this table passes the necessary positive-solo and pure-toggle screens very
strongly.

Nevertheless take `B={f,s}`.  For (9),

\[
 a_0=-1,
 \quad a_1={1\over4},
 \quad b_0=1,
 \quad b_1=-1.
\tag{11}
\]

Thus

\[
 y={1\over2},
 \qquad z={4\over5}.
\tag{12}
\]

The two base stay gains are

\[
 G_f={7\over10},
 \qquad G_s={9\over10}.
\tag{13}
\]

So the chamber theorem applies strictly.  The exact terminal semantic pair of
the root `(1,1,1/2,4/5)` is

\[
 U=B=\left({3\over5},1,{1\over5},-{1\over2}\right).
\tag{14}
\]

The finite-clock evaluator independently returns the pure-time value rows

\[
\begin{array}{c|ccc}
 &\text{Quit at 0}&\text{after support}&\text{Never}\\ \hline
f&3/5&-1/10&-1/10\\
s&1&1/10&1/10\\
h&1/5&1/5&1/5\\
o&-1/2&-1/2&-1/2.
\end{array}
\tag{15}
\]

This is an exact all-behavior zero, not a stationary-only numerical fit.

## 3. Consequence for the strict inert negative search

Any perturbation remaining in the strict chamber (2), (7) has `D_*=0`, even
if it:

* preserves the entire local inert passport;
* makes all-Never strongly exploitable;
* leaves no pure coalition even approximately stable; and
* changes singleton, collision, and preemption rewards in a coordinated way.

The entries outside coalitions containing `B` do not occur in (1), (5), or
(6), and may be changed arbitrarily without affecting the exact equilibrium.
Thus the chamber is not a singleton-only fence.

A positive-gap realization based on this seed must cross at least one of the
finite algebraic walls

\[
 a_0=0, a_1=0, b_0=0, b_1=0, G_f=0, G_s=0,
\tag{16}
\]

or change the selected persistent base.  In the strict-ray language, no
eventually constant or genuinely infinite inert ray can rescue a table while
it remains in this chamber: the exact sure-exit Nash profile kills the global
positive-minimum premise before a ray is selected.

## 4. A second exact chamber outside every detected persistent pair

Rejecting the chamber above does not yet make the negative search difficult.
The next quarter-grid survivor had no nondegenerate accepted two-player
persistent-base Nash point, but its apparent four-date small-debt profile
collapsed to an exact two-date threat.

This gives another general open chamber.  Fix distinct players `j,k` and
prescribe:

* `j` Quits surely at date zero;
* `k` Quits surely at date one; and
* every other player plays Never.

Assume

\[
 r_j(\{j\})\ge
 \max\{r_j(\{j,k\}),r_j(\{k\})\},
\tag{17}
\]

and for every `i != j`,

\[
 r_i(\{i,j\})\le r_i(\{j\}).
\tag{18}
\]

Then, for every player `i` and every randomized history-dependent behavioral
replacement `tau_i`, the two-date profile `sigma` satisfies

\[
 U_i(\sigma[i\leftarrow\tau_i])\le U_i(\sigma).
\]

In particular it is an exact terminal Nash profile for the unrestricted
behavioral strategy class, its semantic debt vector is zero, and it supplies
a uniform-equilibrium payoff.

Indeed, a deviation by `i != j` can only join `j` at date zero or receive the
prescribed payoff from `{j}`.  A deviation by `j` has only three effective
outcomes: quit at zero and receive `r_j({j})`, quit together with `k` at date
one and receive `r_j({j,k})`, or let `k` preempt and receive `r_j({k})`.
Equations (17)--(18) compare all three.  Arbitrarily late quitting and Never
are therefore included.

The complete second search table is below. Coordinates are again ordered
`(f,s,h,o)`.

\[
\begin{array}{c|rrrr}
S&r_f&r_s&r_h&r_o\\ \hline
0001&-1/4&1/2&0&1\\
0010&-3/4&3/4&0&1/2\\
0011&-1/2&-1/2&0&3/4\\
0100&0&1&-1&0\\
0101&1&0&-1&0\\
0110&1&0&-1&0\\
0111&0&1&-1&0\\
1000&-1/4&-1/2&0&1/2\\
1001&1&1/4&0&-3/4\\
1010&-1&1/2&-1/2&1/4\\
1011&1/4&3/4&-3/4&1/2\\
1100&1/4&-1/4&-1/4&-1\\
1101&1&1&1&-1\\
1110&1/2&1/4&0&-1\\
1111&-3/4&-3/4&1&-1
\end{array}
\tag{19}
\]

The inequalities are strict for this table with `j=f,k=s`:

\[
 r_f(\{f\})=-{1\over4},
 \quad r_f(\{f,s\})=-{1\over2},
 \quad r_f(\{s\})=-{3\over4},
\tag{20}
\]

while the three outsider join comparisons are

\[
 -{1\over2}<{1\over2},
 \qquad -1<0,
 \qquad -{3\over4}<1.
\tag{21}
\]

That table also preserved the cyclic inert passport, had pure-toggle floor
`1/4`, and lay outside the nondegenerate persistent-pair chamber screen.  Its
exact equilibrium payoff is simply

\[
 r(\{f\})=(-1/4,1/2,0,1).
\tag{22}
\]

Thus the negative search must exclude not only sure-exit stationary faces but
also off-path finite-clock punishment chambers.  This is precisely why a
positive pure-toggle floor does not lower-bound behavioral exploitability:
the tail attached to a date-zero singleton can reverse the singleton owner's
leave incentive without changing any outsider's prescribed-path comparison.

Both exact chambers are implemented only as exploratory rejection screens in
the script.  Their mathematical proofs above do not depend on the floating
search.

## 5. Current finite covering question

This does not prove that every perturbation preserving the cyclic passport
lies in either a persistent-base or a deadline-threat chamber.  The next
targeted search excludes both.  A finite covering theorem by these and a
small number of further exact chronology chambers would be a genuine local
elimination of the rational inert seed.

## 6. First survivor after both exact chamber screens

For completeness, the search produced one further exact quarter-grid table
after rejecting the persistent-pair chamber and every ordered two-date threat
of Section 4. It is stored as `CANDIDATE_C_ROWS` in the experiment script. It
has

\[
 \text{passport error}=0,
 \qquad
 \min_C\max_i[r_i(C\triangle\{i\})-r_i(C)]_+={1\over4}.
\tag{23}
\]

An exact case enumeration of the six prescribed two-player bases finds no
accepted induced Nash point: in every induced Nash component at least one
base player's expected stay gain is negative. A separate exact check of the
four three-player bases gives the same conclusion, including the two
degenerate cases in which the free player is indifferent. The four-player
base is excluded directly by its strict pure-toggle defect.

This survivor is **not** a positive-gap certificate. Actual finite-clock
search lowers its exact unrestricted exploitability as the support grows. A
denominator-`100000` eight-date profile gives the exact upper witness

\[
 \operatorname{Expl}
 = {3069083213250743827\over100000000000000000000}
 \approx0.03069083214.
\tag{24}
\]

The four stopping-law rows, with the last coordinate Never, are

\[
\begin{aligned}
&(12729/10^5,2811/20000,15873/10^5,4669/25000,
 5041/10^5,8187/10^5,7391/50000,5481/10^5,647/12500),\\
&(14701/10^5,7559/50000,981/5000,3677/20000,
 12127/10^5,2151/50000,559/10000,651/12500,4949/10^5),\\
&(17/10000,11/12500,187/20000,69/25000,331/10^5,
 1847/2000,2589/50000,12/3125,9/3125),\\
&(483/10^5,401/10^5,59/10000,383/10000,3697/4000,
 657/10^5,151/25000,119/25000,267/50000).
\end{aligned}
\tag{25}
\]

The evaluator's cap includes every supported pure date, the first date after
support, and Never; by pure-time extremality this is the full behavioral cap
for this actual finite-clock profile. Thus (23) is not a bounded-deviation
calculation. It remains only an upper bound over profiles.

The outer-hierarchy midpoint theorem then gives an exact zero lower-query
witness through level

\[
 M\le\left\lfloor{24\over\operatorname{Expl}}\right\rfloor=781.
\tag{26}
\]

So this table is a legitimate next falsification candidate, but no finite
lower certificate can begin at the early hierarchy levels. No claim of
positive gap is made.

## Source audit

The bounded sources inspected were:

* `questions/ESCAPE_AWARE_FIN4_CERTIFICATE_SEARCH.md`;
* `exports/STRICT_RAY_TAIL_NORMALIZED_CAP_FLOW.md`;
* `Research/Quitting/EscapeAwareQuantileClockHierarchy.lean` through its
  declarations recorded in `docs/TOOLKIT.md`;
* `Research/Quitting/FourPlayerCyclicPlateauCandidate.lean`;
* `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseInducedGame.lean`;
* `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseNashSemanticAdapter.lean`; and
* `notes/CODEX_EULER__FIN4_QUANTILE_CENTER_OUTER_PROTOTYPE.md`.

## Exact next question

Within the affine face preserving the four-phase cyclic passport, do the
persistent-base and finite-deadline threat chambers cover every table
satisfying a fixed positive pure-toggle floor?  If not, exhibit an exact
rational table outside their union and test it at increasing actual
finite-clock levels.
