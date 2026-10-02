# One-clock stationary escapes from strict-toggle Gray gadgets

**Author:** CODEX_EULER  
**Status (2026-08-25):** ordinary theorem and sharp Fin4 Gray-family
counterexample; independent review requested. Internal only.

## 1. Question and outcome

A directed strict-toggle cycle can fail to have a pure stationary Nash
profile while admitting an exact stationary equilibrium in which one player
uses a geometric quitting clock and every other player Never quits. The Gray
candidate in
[`CODEX_EULER__FIN4_PAIRBASE_INERT_STALL_FEASIBILITY.md`](CODEX_EULER__FIN4_PAIRBASE_INERT_STALL_FEASIBILITY.md)
has exactly this escape.

This note gives an exact unrestricted-behavior characterization of all such
one-clock equilibria. It then tests the entire local Gray assignment language.
The result is negative: the pair-base reset inequalities, the 16-vertex pure
terminal-gap screen, and an all-Continue cap root do **not** force a one-clock
escape. An explicit directed Hamiltonian Gray cycle satisfies those local
conditions but fails the one-clock inequalities for every possible owner and
every positive rate.

Thus the mixed-clock solution of the first Gray candidate is structural but
not universal. Any elimination of the strict-toggle gadget class needs either
several active clocks or genuinely global behavioral/minimum information.

## 2. One-clock profiles

Let \(I\) be finite and nonempty, let \(k\in I\), and fix \(x\in(0,1]\).
Define \(\sigma^{k,x}\) to be the stationary behavioral profile in which
player \(k\) Quits independently with probability \(x\) at every live date
and every player \(j\ne k\) Never quits.

Absorption occurs almost surely at \(\{k\}\), so

\[
 U_i(\sigma^{k,x})=r_i(\{k\})qquad(i\in I).
\tag{2.1}
\]

For an outsider \(j\ne k\), abbreviate

\[
 a_j=r_j(\{k\}),\qquad
 s_j=r_j(\{j\}),\qquad
 b_j=r_j(\{j,k\}).
\tag{2.2}
\]

## 3. Exact unrestricted cap formula

### Theorem 3.1 (one-clock cap characterization)

For the profile \(\sigma^{k,x}\),

\[
B_k=\max\{0,r_k(\{k\})\},
\tag{3.1}
\]

and, for every outsider \(j\ne k\),

\[
B_j=a_j+
\Bigl[xb_j+(1-x)s_j-a_j\Bigr]_+.
\tag{3.2}
\]

Consequently \(\sigma^{k,x}\) is an exact terminal Nash profile against all
behavioral deviations if and only if

\[
r_k(\{k\})\ge0
\tag{3.3}
\]

and

\[
(1-x)r_j(\{j\})+x r_j(\{j,k\})
\le r_j(\{k\})qquad(j\ne k).
\tag{3.4}
\]

#### Proof

Player \(k\) faces opponents who Never quit. Every finite deterministic Quit
time yields the singleton reward \(r_k(\{k\})\), and Never yields zero. This
proves (3.1).

Fix outsider \(j\), and let it Quit at deterministic time \(t\). If player
\(k\) quit earlier, the outcome is \(\{k\}\) and the payoff is \(a_j\). The
probability that \(k\) survives the first \(t\) dates is \((1-x)^t\). At date
\(t\), conditional on that survival, a tie has payoff \(b_j\) and probability
\(x\), while preemption by \(j\) alone has payoff \(s_j\) and probability
\(1-x\). Therefore

\[
V_j(t)=a_j+(1-x)^t
  \bigl(xb_j+(1-x)s_j-a_j\bigr).
\tag{3.5}
\]

Never yields \(a_j\). If the parenthesized expression is positive, (3.5) is
maximized at \(t=0\); if it is nonpositive, Never is optimal. The formula
also covers \(x=1\): time zero gives \(b_j\), every later time gives \(a_j\).

The checked behavioral pure-time extremality theorem
`sSup_range_quittingTerminalPayoff_update_eq_pureTime` identifies the
supremum of these deterministic times and Never with the supremum over every
behavioral replacement. This proves (3.2). Comparing (3.1)--(3.2) with the
prescribed values (2.1) gives (3.3)--(3.4). QED.

### Corollary 3.2 (finite interval test)

For fixed owner \(k\), put

\[
A_{jk}=r_j(\{j\})-r_j(\{k\}),\qquad
C_{jk}=r_j(\{j,k\})-r_j(\{j\}).
\tag{3.6}
\]

The set of exact one-clock rates is the interval cut

\[
\mathcal I_k=(0,1]\cap
\bigcap_{j\ne k}\{x:A_{jk}+C_{jk}x\le0\},
\tag{3.7}
\]

provided \(r_k(\{k\})\ge0\); otherwise it is empty. Thus existence is decided
by finitely many rational endpoint comparisons when the reward table is
rational. Explicitly, a positive \(C_{jk}\) supplies an upper bound on \(x\),
a negative \(C_{jk}\) supplies a lower bound, and a zero coefficient requires
\(A_{jk}\le0\).

This is a characterization, not merely verification of a supplied profile.
It eliminates the entire one-active-clock strategy class for a reward table
whenever all \(\mathcal I_k\) are empty.

## 4. Recovery of the first Gray escape

For the Gray word used in Proposition 5.1 of the feasibility note, owner
\(k=2\) has singleton reward zero. The only nontrivial outsider constraint is
player 3's

\[
(1-x)(-1)+x(1)\le0,
\]

which is exactly \(x\le1/2\). The other outsiders' inequalities hold for all
positive \(x\). Hence

\[
\mathcal I_2=(0,1/2],
\]

recovering the exact stationary equilibrium family already proved there.

## 5. Gray assignment convention

For the counterexample, use the same finite construction rule as the original
Gray screen. Choose a directed Hamiltonian cycle of the four-dimensional
coalition cube. On every directed coordinate edge
\(S\to S\triangle\{i\}\) whose endpoints are nonempty, set player \(i\)'s
reward to 0 at the source and 1 at the target. On an edge
\(\varnothing\to\{i\}\), set \(r_i(\{i\})=1\); on an edge
\(\{i\}\to\varnothing\), set \(r_i(\{i\})=-1\). Set both endpoint rewards to
zero on every unused coordinate edge.

Every pure quitting set has a displayed unilateral gain of one along the next
cycle edge. Thus every such table satisfies the pure stationary terminal-gap
screen with \(\Gamma=1\), although it need not have a positive gap against
mixed or nonstationary behavioral profiles.

## 6. A pair-base Gray gadget with no one-clock escape

### Proposition 6.1 (sharp counterexample inside the Gray family)

Use the directed Hamiltonian cycle

\[
\begin{split}
\varnothing,&\{0\},\{0,1\},\{1\},\{1,2\},\{0,1,2\},I,
\{1,2,3\},\\
&\{2,3\},\{2\},\{0,2\},\{0,2,3\},\{0,3\},
\{0,1,3\},\{1,3\},\{3\},\varnothing.
\end{split}
\tag{6.1}
\]

and assign rewards by Section 5. Then:

1. every pure stationary quitting set has an unrestricted debt at least one;
2. at pair base \(B=\{0,1\}\), player 0 has a leave gain one, free players
   2 and 3 have zero debt, and owner 2 is solved;
3. the cap at that pair profile is \((1,1,0,0)\), and all Continue is an exact
   cap root; but
4. no owner \(k\in I\) and no rate \(x\in(0,1]\) produce an exact one-clock
   stationary equilibrium.

#### Proof

Item 1 is immediate from the next edge of the Hamiltonian cycle. At
\(B=\{0,1\}\), the next edge removes player 0 and has gain one. The coordinate
edges joining players 2 and 3 to \(B\) are unused, so their two endpoint
rewards agree at zero. Direct evaluation gives the prescribed/cap data

\[
 U(B)=(0,1,0,0),\qquad B(B)=(1,1,0,0).
\tag{6.2}
\]

The singleton vector is

\[
\bigl(r_0(\{0\}),r_1(\{1\}),r_2(\{2\}),r_3(\{3\})\bigr)
=(1,0,0,-1),
\tag{6.3}
\]

which is coordinatewise at most (6.2)'s cap. Hence all Continue is an exact
cap root.

It remains to apply Theorem 3.1 to every possible clock owner.

- If \(k=0\), outsider 1 has
  \[
  r_1(\{1\})=0,quad r_1(\{0,1\})=1,quad r_1(\{0\})=0,
  \]
  so (3.4) reads \(x\le0\), impossible for \(x>0\).
- If \(k=1\), outsider 2 has
  \[
  r_2(\{2\})=0,quad r_2(\{1,2\})=1,quad r_2(\{1\})=0,
  \]
  and again (3.4) reads \(x\le0\).
- If \(k=2\), outsider 0 has
  \[
  r_0(\{0\})=1,quad r_0(\{0,2\})=1,quad r_0(\{2\})=0,
  \]
  so the left side of (3.4) is identically one.
- If \(k=3\), the owner's singleton reward is \(-1\), contradicting (3.3).

Thus every interval \(\mathcal I_k\) is empty. QED.

## 7. What is and is not forced

Proposition 6.1 is a sharp counterexample to the implication

```text
pure strict-toggle/Gray cycle
+ pair-base paid/reset incidence inequalities
+ pure-profile gap screen
+ existence of an all-Continue cap root
  -> exact one-clock stationary escape.
```

The failure is already visible in singleton and pair rewards, through the
empty interval tests (3.7). Therefore no refinement using only the same local
incidence data can make the one-clock escape universal.

The proposition does not show that the opaque canonical
`quittingCapLiftedPrefixRoot` selects all Continue when other cap roots exist;
it only realizes the finite all-Continue root inequality. Nor does it show a
positive all-behavior terminal gap. The counterexample may admit an exact
equilibrium with two or more active clocks. Those are precisely the remaining
mixed-behavior escape mechanisms not controlled by the pure Gray screen.

## 8. Source and novelty audit

The unrestricted-deviation step uses
`sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
`UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`.
`quittingStationaryUnilateralCap_pureSetRoot` in
`UniformEquilibrium/Quitting/Paths/SureExitSet.lean` is the zero/one boundary
of the same calculation, but it does not state the geometric one-clock formula
(3.2).

The checked strict-toggle orbit
`QuittingTerminalExploitabilityWitness.exists_strictToggleClosedOrbit_from`
produces the pure cycle but explicitly supplies no stationary or Bellman
consumer. Theorem 3.1 characterizes one natural stationary consumer; Proposition
6.1 proves that this consumer does not eliminate the complete Gray gadget
class.

No paper theorem is used.

## 9. Scope and requested review

- All cap statements concern unrestricted behavioral deviations.
- The owner clock is stationary and the other complete strategies are Never;
  no bounded-deviation restriction is imposed.
- The counterexample eliminates only the one-active-clock consumer, not all
  stationary or behavioral equilibria.
- No terminal-gap counterexample, Bellman edge, floor path, or uniform payoff
  is claimed for Proposition 6.1.
- Please independently check the time-\(t\) formula (3.5), the \(x=1\)
  boundary, the affine interval test, the exact cycle (6.1), and all four
  empty-interval witnesses.

