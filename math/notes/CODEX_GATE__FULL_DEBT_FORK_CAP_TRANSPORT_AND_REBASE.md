# Full-debt fork cap transport and the exact-prefix rebase boundary

Identity: `CODEX_GATE`  
Date: 2026-08-31  
Status: **ordinary mathematics composed with named scratch Lean declarations;
positive local reduction plus an exact local no-go; no full-debt chamber
consumer.**  The main positive statement below turns the newly available
common-prefix complete stopping-law fork into a
source-attached, extension-compatible terminal-atom alternative after every
uniformly entered exact prefix.  Global minimality forces the required
other-player debt rise.  The output is not an exact Nash--Bellman return: an
explicit Fin4 table shows that the fork can invalidate every retained prefix
root even when the source is full debt, the fork is reached with probability
one, and all finite source prefixes have a common positive entrance floor.

## 1. Exact question

Let `I = Fin 4`, let rewards be bounded in absolute value by `M > 0`, and let

\[
 D(\sigma)=\sum_{i\in I}
   \bigl(B_i(\sigma)-U_i(\sigma)\bigr),\qquad
 D_*=\min_{x\in\mathcal C_{\rm sem}}D(x).
\]

Here every `B_i` is the supremum over all behavioral unilateral strategies.
Suppose an actual source profile is close to a full-debt global minimum and
is placed behind a finite exact punishment-floor prefix.  The recent scratch
results supply both:

1. a complete stopping-law replacement of one player with a fixed payoff
   gain; and
2. a first-disagreement date for that replacement with a fixed lower bound on
   the actual joint source reach.

The prefix theorem independently gives a horizon-free lower bound on the
joint entrance probability to the source suffix.  The question is whether
these data survive the other three players' unrestricted caps strongly enough
to give an exact charged return.

The answer obtained here is:

```text
uniform exact-prefix entrance + actually reached complete fork
  + global near-minimality
    -> fixed other-player debt rise
    -> one source-attached post-cut terminal atom,
       or one post-cut pure-time response rectangle
       whose observer debt is arbitrarily small;

but not -> retention of the old exact prefix roots.
```

Thus there is a genuine extension-compatible rebase of the **atom**, but not
yet an extension-compatible rebase of the exact Nash--Bellman prefix.

## 2. One simultaneous fork and reached cut

Fix an actual terminal source `sigma`, a mover `i`, and a number `Delta > 0`
such that

\[
 d_i(\sigma)=B_i(\sigma)-U_i(\sigma)\geq\Delta.
 \tag{2.1}
\]

Against the fixed opponents, let

\[
 f(q)=U_i(\sigma[i\leftarrow q]),\qquad
 C=\sup_{q\in\mathbb N\cup\{\infty\}}f(q)=B_i(\sigma),
\]

and let `nu` be the stopping-time law of the prescribed strategy of `i`.
Put

\[
 A=\{q:C-f(q)\geq\Delta/2\},\qquad a=\nu(A).
\]

The bounded-gap estimate gives

\[
 a\geq\frac{\Delta}{4M}.                              \tag{2.2}
\]

Choose one receiver `r` with `f(r)>C-Delta/4`, and redirect all mass of `A`
to `r`:

\[
 \nu^\dagger=\nu-\nu|_A+a\delta_r.                   \tag{2.3}
\]

Since `r` is not in `A`, this is a probability law and

\[
 \operatorname{TV}(\nu,\nu^\dagger)=a.              \tag{2.4}
\]

Let `tau` be the actual profile obtained by reconstructing
`nu^dagger` as `i`'s behavioral strategy.  Then

\[
 g:=U_i(\tau)-U_i(\sigma)
   =\int_A\bigl(f(r)-f(q)\bigr)\,d\nu(q)
   >a\Delta/4
   \geq\frac{\Delta^2}{16M}.                         \tag{2.5}
\]

Use the least finite bad source time when it exists, and use `Never` when all
finite bad times have zero mass.  Compare it with the same receiver `r` used
in (2.3).  Their first disagreement occurs at a finite date `t`: they cannot
both be `Never`, because their payoff difference is at least `Delta/4`.
The proof of
`positiveDebt_exists_actualJointReach_paidFirstDisagreementRow` then gives

\[
 \Pr_\sigma(\text{live at }t)
   \geq\frac{\Delta^2}{32M^2}.                       \tag{2.6}
\]

Moreover, the two complete mover strategies agree literally before `t`.

Equations (2.3)--(2.6) are a simultaneous choice, not merely an intersection
of two existential scratch declarations.  They are now packaged by the named
scratch theorem
`positiveDebt_exists_commonPrefix_profitableStoppingLawFork` in
`FableCommonPrefixFork.lean`.  Its output includes the paid row, transported
law, quadratic gain, both one-sided reach estimates, and literal equality of
the reconstructed mover behaviors at every date strictly before the row
start.  The bad-mass and total-variation identities above also follow by
inspection of its explicit `PMF.map` witness.  This is scratch Lean, not a
production or integrated declaration.

## 3. Transport through a finite exact prefix

Let `W` be a finite literal root word placed before the source suffix.  Write

\[
 P_W=\Pr(\text{all players Continue through }W),
\]

and suppose the exact-prefix construction gives the horizon-independent
bound

\[
 P_W\geq\rho_0>0.                                    \tag{3.1}
\]

For the prefixes in `FableUniformEntrance.lean`, one may take

\[
 \rho_0=
 \exp\!\left(-\frac{K}{(\gamma/(4M))^4}\right),      \tag{3.2}
\]

where `K` is the canonical prefix-charge bound and `gamma` is the terminal
exploitability gap.  Formula (3.2) is scratch-formalized, not yet a cited
production theorem.

Define the actual profiles

\[
 X=\operatorname{Stack}(W,\sigma),\qquad
 Y=\operatorname{Stack}(W,\tau).
\]

They differ in only the complete strategy of `i`, after the common prefix.
Fresh absorption in `W` cancels from their payoff difference, hence

\[
 G:=U_i(Y)-U_i(X)=P_Wg
   \geq\rho_0\frac{\Delta^2}{16M}.                   \tag{3.3}
\]

The scratch theorem gives literal root agreement before the cut

\[
 L=|W|+t,
\]

and locates its paid row at that cut.  The prescribed source reaches it with
probability at least

\[
 \Pr_X(\text{live at }L)
  =P_W\Pr_\sigma(\text{live at }t)
  \geq\rho_0\frac{\Delta^2}{32M^2}.                 \tag{3.4}
\]

Thus the complete payoff fork is not merely a horizontal semantic update:
it is a literal unilateral edge with a paid, uniformly reached cut behind one
common prefix.  The scratch theorem exposes equality before the cut; the
stronger claim that non-equality at the cut itself is a stored structure field
is not needed here.

## 4. Exact unrestricted-cap transport

The remaining issue is not the mover's cap.  It is the caps of the other
three players.

### Proposition 4.1 (total-variation cap transport)

Let two profiles `x,y` differ only in player `i`'s strategy, and let `eta` be
the total variation distance between the two complete stopping laws of `i`.
Then

\[
 |U_j(y)-U_j(x)|\leq 2M\eta\qquad(j\in I),            \tag{4.1}
\]

\[
 |B_j(y)-B_j(x)|\leq 2M\eta\qquad(j\ne i),           \tag{4.2}
\]

and

\[
 B_i(y)=B_i(x).                                       \tag{4.3}
\]

Consequently

\[
 |d_j(y)-d_j(x)|\leq4M\eta\quad(j\ne i),
 \qquad d_i(y)-d_i(x)=-(U_i(y)-U_i(x)).              \tag{4.4}
\]

#### Proof

For (4.1), hold every other strategy fixed and condition on `i`'s complete
stopping time.  The resulting payoff integrand is bounded by `M`; the usual
total-variation expectation estimate gives (4.1).

For (4.2), fix an arbitrary complete behavioral deviation of `j`.  Updates
of distinct players commute, and the same bounded-integrand estimate applies
uniformly to the payoff of that deviation.  Taking the supremum over all
behavioral deviations preserves the `2M eta` bound.  This is why (4.2) covers
unrestricted deviations rather than only pure times or stationary controls.
Finally, player `i`'s best-response cap depends only on the opponents, so it
is invariant under changing `i`'s prescribed strategy.  Subtracting payoff
from cap proves (4.4).  `QED`

For the prefixed fork, if `S_i(W)` is the mover's own survival through `W`,
the two global mover laws have

\[
 \eta=S_i(W)a\leq a.                                  \tag{4.5}
\]

Thus the complete fork has an honest all-behavior cap modulus, but it has no
favorable sign:

\[
 |B_j(Y)-B_j(X)|\leq2Ma,qquad
 |d_j(Y)-d_j(X)|\leq4Ma.                              \tag{4.6}
\]

Both the desired gain and the possible leakage are first order in the moved
mass `a`.  Making a radial fork smaller therefore does not remove the
cap-leakage ratio.

There is one narrow scratch-API distinction.  The proof of
`positiveDebt_exists_commonPrefix_profitableStoppingLawFork` constructs the
returned law by the explicit bad-set `PMF.map`, but its existential conclusion
does not retain a field identifying that map, the bad mass `a`, or the total
variation in (2.4).  A Lean consumer of the quantitative bounds (4.5)--(4.6)
would need a companion exposed-law/TV theorem or a slightly richer result
structure.  The minimum-debt transfer in Section 5 needs only the already
exposed payoff gain and therefore is not blocked by this API omission.

## 5. Global minimality forces a spectator debt rise

Assume now that the prefixed source is near the global minimum:

\[
 D(X)\leq D_*+\varepsilon.                            \tag{5.1}
\]

Own-cap invariance and (3.3) give

\[
 d_i(Y)-d_i(X)=-G.                                    \tag{5.2}
\]

Since `Y` is an actual profile, global minimality gives `D(Y)>=D_*`.
Therefore

\[
 \sum_{j\ne i}\bigl(d_j(Y)-d_j(X)\bigr)
   =D(Y)-D(X)+G
   \geq G-\varepsilon.                               \tag{5.3}
\]

If `epsilon <= G/4`, Fin4 pigeonhole supplies one fixed other player `j`
with

\[
 d_j(Y)-d_j(X)\geq G/4=:c>0.                         \tag{5.4}
\]

Combining (3.3) and (5.4),

\[
 c\geq\rho_0\frac{\Delta^2}{64M}.                   \tag{5.5}
\]

This is the exact answer to the first cap-transport question.  The other
caps need not be controlled from above with a favorable sign; instead,
near-minimality converts their aggregate leakage into a fixed positive debt
rise for one source-attached spectator.

For a sequence of near-minimum prefixed sources, `G` has the uniform lower
bound in (3.3), so `epsilon <= G/4` holds eventually.  The selected spectator
may initially depend on the rank; finiteness of the three outsider labels
gives one fixed `j` after passing to a subsequence of the same source family.

## 6. Extension-compatible atom rebase

Choose any `e` with

\[
 0<e\leq c/8.
\]

The checked declaration
`hasVanishingDebtAtomAlternative_of_endpointDebtRise` applies directly to
the literal edge `X -> Y`, mover `i`, observer `j`, rise `c`, and error `e`.
It returns

\[
 q=7c/8
 \geq \frac{7\rho_0\Delta^2}{512M}                 \tag{6.1}
\]

and one of the following.

1. **Prescribed-law atom.**  For some absorbing terminal outcome `S`,

   \[
   q/2\leq |\Omega|\,
     \operatorname{Atom}_j(X,Y;S).                   \tag{6.2}
   \]

2. **Common-response rectangle.**  For one pure stopping time `s` of `j`
   and some absorbing terminal outcome `S`,

   \[
   q/4\leq |\Omega|\,
     \operatorname{Atom}_j(Y[j\leftarrow s],
                           X[j\leftarrow s];S),       \tag{6.3}
   \]

   while

   \[
   d_j(Y[j\leftarrow s])\leq e.                      \tag{6.4}
   \]

Here `Atom` is exactly `quittingTerminalPayoffDifferenceAtom`, with the
orientation displayed in the Lean definition.  The symbol `|Omega|` is the
finite cardinality of `QuittingTerminalOutcome I`.

The new point is that both arms rebase through the same literal cut `L`.

### Proposition 6.1 (common-cut factorization)

In the prescribed arm, `X` and `Y` have the same root word before `L`.
The checked common-prefix identity
`quittingTerminalPayoffDifferenceAtom_literalRootStack` gives

\[
 \operatorname{Atom}_j(X,Y;S)
  =R_L\operatorname{Atom}_j(X^L,Y^L;S),              \tag{6.5}
\]

where `R_L` is their common joint reach and

\[
 R_L\geq\rho_0\frac{\Delta^2}{32M^2}>0              \tag{6.6}
\]

by (3.4).  Thus (6.2) is a genuine atom in the suffix at the reached cut,
not an unrelated realization of the same semantic point.

In the rectangle arm, a finite pure response time `s<L` would make the two
response profiles have exactly the same terminal law: before `L` their roots
are identical, and the observer surely terminates play at `s` if no earlier
absorption occurs.  This would make the atom in (6.3) zero, contradicting
`q>0`.  Hence

\[
 s\in\{L,L+1,\ldots\}\cup\{\mathrm{Never}\}.        \tag{6.7}
\]

The response therefore forces `j` to Continue through the common prefix.
Applying the same prefix identity to that force-Continue word gives

\[
 \operatorname{Atom}_j(Y[j\leftarrow s],X[j\leftarrow s];S)
  =R_L^{(-j)}\operatorname{Atom}_j(widehat Y^L,
                                    \widehat X^L;S),  \tag{6.8}
\]

where `R_L^(-j)` is the common prefix survival after forcing `j` to Continue.
It satisfies

\[
 R_L^{(-j)}\geq R_L>0.                               \tag{6.9}
\]

Thus the same source ancestry and the same reached cut survive the
unrestricted-cap decoder.  In the rectangle arm,
`exists_positive_causalStage_and_actualTerminalMass_of_rectangleCharge`
further supplies a positive causal stage and positive actual terminal mass
in one response endpoint.  Every positive such stage is at or after `L`,
because the mover laws coincide before `L`.  `QED`

This is stronger than a static debt-rise or time-forgetting atom: it is one
literal post-cut source/target packet with a fixed unconditional atom charge,
a positive entrance floor, and an arbitrarily small observer debt in the
response arm.

## 7. Why this is not yet a charged return

The preceding proposition rebases terminal-law evidence, not the exact root
certificate.  The roots in `W` were selected against the old continuation
caps.  After the complete fork, (4.2) permits another player's continuation
cap to move by a fixed amount.  A root which mixed that player at equality
can immediately cease to be Nash.  Neither the actual reach lower bound nor
the uniform entrance lower bound controls this equality.

The failure is visible already at the last retained root.  For a fixed
product root `p`, player `j`'s pure-Continue endpoint has the form

\[
 C_j(p,V)=A_j(p)+H_j(p)V_j,                           \tag{7.1}
\]

where `H_j(p)` is the probability that every opponent of `j` Continues at
that root; the pure-Quit endpoint is independent of `V`.  If the old root
puts positive mass on `j`'s Quit action at equality and the suffix fork raises
`V_j` by `delta>0`, then the Continue endpoint rises by
`H_j(p) delta`.  Whenever `H_j(p)>0`, the unchanged root violates the new
support-Nash inequality.  A positive entrance bound makes `H_j(p)` positive;
it does not create the strict slack needed to absorb `delta`.  Backward
Bellman recursion then cannot even start with the retained last root.

The two decoder arms leave distinct precise gaps.

- In the prescribed-law arm, the fork causes a fixed post-cut terminal-law
  difference, but no selected observer has small endpoint debt.
- In the rectangle arm, one response endpoint has arbitrarily small observer
  debt and a post-cut causal atom, but its total debt need not be close to
  `D_*`; changing the observer can raise the other two caps.

In both arms the old exact roots can fail after the suffix edit.  Therefore
the packet does not instantiate `QuittingPositiveAdmissibleReturn`, a
`QuittingChronologicalDebtShadowingCertificate`, or a finite-forward packet.
The all-frontier `VanishingDebtAtomChronologicalConsumer` cannot be cited as
a solution: `UniformExistenceBoundary.lean` proves it equivalent, reward
table by reward table, to the desired uniform-payoff existence statement.

## 8. Exact Fin4 regression: uniform entrance does not transport root Nash

This example stress-tests the missing implication without pretending to be a
counterexample to the conjecture.

Let the players be `i,j,k,l`.  For every nonempty coalition `S`, define

\[
 r_i(S)=1,
\]

\[
 r_j(S)=\mathbf 1_{j\in S}+\mathbf 1_{\{i,j\}\subseteq S},
\]

\[
 r_k(S)=\mathbf 1_{k\in S\ \mathrm{or}\ j\in S},
 \qquad
 r_l(S)=\mathbf 1_{l\in S\ \mathrm{or}\ j\in S}.   \tag{8.1}
\]

All rewards lie in `[0,2]`.

### 8.1 Full-debt source and exact debt transfer

At the all-`Never` source `sigma`,

\[
 U(\sigma)=(0,0,0,0),\qquad B(\sigma)=(1,1,1,1),
\]

so

\[
 d(\sigma)=(1,1,1,1).                                \tag{8.2}
\]

Replace `i` by immediate Quit and leave the other three at `Never`.  Call the
target `tau`.  Then

\[
 U(\tau)=(1,0,0,0),\qquad B(\tau)=(1,2,1,1),
\]

and hence

\[
 d(\tau)=(0,2,1,1).                                  \tag{8.3}
\]

The mover gains one, its debt falls by one, the unrestricted cap and debt of
`j` rise by one, and total debt remains four.  The fork's first difference is
date zero and its actual joint reach is one.

The cap computations are against unrestricted behavioral deviations.  At
`sigma`, each player can obtain its singleton reward one and no other player
ever quits.  At `tau`, player `j` obtains two exactly by quitting at date zero
with `i`; players `k,l` obtain one by doing the same, and no bounded or
unbounded stopping rule can exceed the displayed reward maxima.

### 8.2 An infinite exact source prefix with uniform entrance

Against the source cap

\[
 V=(1,1,1,1),
\]

let root `q_n` make only `j` Quit, with probability

\[
 p_n=2^{-(n+2)},                                      \tag{8.4}
\]

and make every other player Continue surely.  Every pure endpoint payoff at
this root equals one for every player:

- `i` receives one at every nonempty coalition;
- `j` receives one by quitting alone and one by continuing to `V`;
- `k,l` receive one whether they join, Continue while `j` quits, or Continue
  to `V`.

Thus every `q_n` is an exact product-root Nash equilibrium and its Bellman
successor is again `V`.  Every finite prefix `q_0,...,q_(H-1)` is therefore
an exact Nash--Bellman prefix.  Its joint entrance satisfies

\[
 \prod_{n<H}(1-p_n)
   \geq1-\sum_{n<H}p_n
   \geq\frac12.                                      \tag{8.5}
\]

This is a genuine horizon-independent entrance floor, with summable total
root absorption.

### 8.3 The fork destroys every retained root

After the suffix fork, the continuation cap is

\[
 V'=(1,2,1,1).
\]

At the unchanged root `q_n`, player `j` gets one from pure Quit and two from
pure Continue, because all other root players Continue and the successor
coordinate is `V'_j=2`.  Since `p_n>0`, `q_n` is not Nash against `V'`.
This holds at every prefix depth.

All Continue is an exact root against `V'`, so an exact rebase exists, but it
has zero absorption charge.  The local data do not force a charge-preserving
choice.

This regression has all of the following local fields:

```text
full debt at the displayed source;
complete unilateral fork gain one;
actual first-disagreement reach one;
exact cross-player unrestricted-cap rise one;
exact preservation of total debt;
arbitrarily long exact source prefixes;
one common entrance floor at least 1/2.
```

It nevertheless has no extension of the **same** exact prefix past the fork.
The example does not satisfy the maintained positive-global-minimum
hypothesis.  Indeed the profile in which `j` quits immediately and everybody
else plays `Never` pays `(1,1,1,1)` and has zero semantic debt, so `D_*=0`.
Accordingly it is a sharp local coherence no-go, not a negative answer to
`FIN4_FULL_DEBT_CHAMBER_CONSUMER.md`.

## 9. Source and declaration audit

Files and declarations inspected narrowly:

- `positiveDebt_exists_commonPrefix_profitableStoppingLawFork`, together with
  the finite-mass, survival, hazard, and behavior equality lemmas below a cut,
  in `fable/lean/FableCommonPrefixFork.lean` -- scratch formalization of the
  simultaneous profitable/reached/common-prefix fork used in Sections 2--3;
- `positiveDebt_exists_profitableStoppingLawFork` in
  `fable/lean/FableProfitableFork.lean` -- scratch formalization of the
  underlying complete fork;
- `positiveDebt_exists_actualJointReach_paidFirstDisagreementRow` in
  `fable/lean/FableDebtActualReach.lean` -- scratch formalization of the true
  joint-reach floor;
- `QuittingTerminalExploitabilityWitness.uniform_prefixSurvival_lowerBound`
  in `fable/lean/FableUniformEntrance.lean` -- scratch formalization of the
  uniform exact-prefix entrance;
- `quittingTerminalPayoff_update_stoppingLawBehaviorStrategy_eq_expect` in
  `Quitting/Paths/StoppingLawExposure.lean`;
- `quittingContinuationBestResponseValue_update_self` and the stopping-law
  debt convexity declarations in
  `Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawDebtConvexity.lean`;
- `exists_quittingStoppingLawCommonResponseWitness_of_endpointDebtRise` and
  `hasVanishingDebtAtomAlternative_of_endpointDebtRise` in
  `Diagnostics/Quitting/StoppingLaw/VanishingDebtAtomAlternative.lean`;
- `quittingTerminalPayoffDifferenceAtom_literalRootStack` and the
  force-Continue survival identities in
  `Diagnostics/Quitting/StoppingLaw/ContinuePrefixAtomAccess.lean`;
- `exists_positive_causalStage_and_actualTerminalMass_of_rectangleCharge` in
  `Diagnostics/Quitting/TerminalSemanticPureTimeRectangleDisintegration.lean`;
  and
- `VanishingDebtAtomChronologicalConsumer` together with its equivalence to
  uniform-payoff existence in
  `Diagnostics/Quitting/UniformExistenceBoundary.lean`.

No Lean file, fable file, or export was edited.  The cap-transport proposition,
the simultaneous packaging in Section 2, the common-cut synthesis in Section
6, and the regression are ordinary mathematics in this note.

## 10. Verdict and one next question

The actual-joint-reach result and uniform prefix entrance do solve one
important provenance problem: after the complete fork, global minimality and
the checked debt-rise decoder produce a quantitative terminal atom or response
rectangle behind the **same reached cut**.  Other-player unrestricted cap
leakage is therefore not invisible; it becomes a fixed spectator debt rise
and then a source-attached atom packet.

They do not solve exact reattachment.  The smallest remaining question is:

> In the positive-minimum full-debt chamber, does the maintained terminal gap,
> global singleton moat, and minimum-law atom force the rectangle endpoint
> `Y[j <- s]` of Section 6 either (a) to have total debt `D_*+o(1)` while
> `d_j=o(1)`, giving a genuine support-rank drop, or (b) to admit an exact
> punishment-floor prefix with positive charge that preserves the common cut
> and atom?

The regression proves that uniform entrance, full debt of the displayed
source, total-debt conservation across the fork, and actual reach alone cannot
prove either alternative.  A positive theorem must use the genuinely global
positive-minimum/hard-residual data to control the two remaining players'
unrestricted caps after the observer response.
