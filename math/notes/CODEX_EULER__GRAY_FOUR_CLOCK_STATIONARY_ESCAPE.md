# Exact four-clock stationary escape in the no-one-clock Gray table

**Author:** CODEX_EULER  
**Status (2026-08-25):** exact ordinary-mathematics existence certificate;
independent review requested. Internal only.

## 1. Result

The sharp Fin4 Gray table from Proposition 6.1 of
[`CODEX_EULER__ONE_CLOCK_STATIONARY_ESCAPE_CHARACTERIZATION.md`](CODEX_EULER__ONE_CLOCK_STATIONARY_ESCAPE_CHARACTERIZATION.md)
has no exact stationary equilibrium with only one positive quitting clock.
It nevertheless has an exact **fully mixed stationary terminal Nash profile**.
All four quitting probabilities lie in explicit rational intervals of radius
\(10^{-6}\), and unrestricted behavioral pure-time extremality proves that
the stationary endpoint equalities control every behavioral deviation.

Thus this Gray gadget has a uniform-equilibrium payoff. Its escape mechanism
is genuinely multi-clock: all four immediate-Quit/Never endpoint differences
vanish simultaneously through collision and preemption mass. The example
cannot obstruct the updated checked paid-cap trichotomy, the prescribed
singleton double port, or the strict minimum-fiber tube; it lacks their global
terminal-gap/positive-minimum source.

## 2. Exact reward table

Use players \(I=\{0,1,2,3\}\) and the directed Hamiltonian cycle

\[
\begin{split}
\varnothing,&\{0\},\{0,1\},\{1\},\{1,2\},\{0,1,2\},I,
\{1,2,3\},\\
&\{2,3\},\{2\},\{0,2\},\{0,2,3\},\{0,3\},
\{0,1,3\},\{1,3\},\{3\},\varnothing.
\end{split}
\tag{2.1}
\]

On every directed coordinate edge
\(S\to S\triangle\{i\}\) with nonempty endpoints, give player \(i\)
payoff 0 at the source and 1 at the target. Give the first singleton payoff
\(r_0(\{0\})=1\), the last singleton payoff
\(r_3(\{3\})=-1\), and put zero on both endpoints of every unused coordinate
edge. This determines all 60 reward coordinates without conflict.

The table has pure stationary debt at least one at every quitting set, the
pair-base local fields recorded in the preceding note, and no one-clock
stationary equilibrium.

## 3. Stationary unrestricted endpoint equations

Let \(p_i\in(0,1)\) be player \(i\)'s stationary quitting probability and put

\[
y_i=\frac{p_i}{1-p_i}>0.
\]

For player \(i\), write

\[
P_i=\prod_{j\ne i}(1+y_j).
\]

The one-stage opponents' coalition weights are \(y_T/P_i\). Conditional on
some opponent eventually quitting, the first opponent coalition has weights
\(y_T/(P_i-1)\) for nonempty \(T\). Therefore the immediate-Quit value
\(Q_i\) and Never value \(N_i\) in this exact table are

\[
\begin{array}{c|c|c}
i&Q_i&N_i\\ \hline
0&\dfrac{1+y_2+y_1y_2}{P_0}
 &\dfrac{y_1(1+y_3+y_2y_3)}{P_0-1}\\[1.1em]
1&\dfrac{y_0(1+y_3)}{P_1}
 &\dfrac{y_3(1+y_2)}{P_1-1}\\[1.1em]
2&\dfrac{y_1}{P_2}
 &\dfrac{y_0y_3}{P_2-1}\\[1.1em]
3&\dfrac{-1+y_0y_2+y_0y_1y_2}{P_3}
 &\dfrac{y_2}{P_3-1}.
\end{array}
\tag{3.1}
\]

For completeness, if \(c_i=\prod_{j\ne i}(1-p_j)\), the payoff from player
\(i\) quitting at deterministic time \(t\) against these stationary
opponents is

\[
V_i(t)=N_i+c_i^t(Q_i-N_i).
\tag{3.2}
\]

Indeed, if the opponents quit earlier their stationary first-coalition law is
the law defining \(N_i\); conditional on their survival to time \(t\), the
time-\(t\) payoff is \(Q_i\). Never pays \(N_i\).

The checked declaration
`sSup_range_quittingTerminalPayoff_update_eq_pureTime` upgrades (3.2) from
deterministic times and Never to the full unrestricted behavioral cap. Hence
a fully mixed stationary profile is exact terminal Nash precisely when

\[
F_i(p):=Q_i(p_{-i})-N_i(p_{-i})=0
\qquad(i=0,1,2,3).
\tag{3.3}
\]

At such a point every pure time has the same value, and the prescribed
geometric clock, being a mixture of those stopping times, has
\(U_i=Q_i=N_i=B_i\).

## 4. Exact rational contraction certificate

The solution of (3.3) is not a simple rational vector. The following
certificate proves exact existence without assuming a numerical root.

Let

\[
c=10^{-6}(513125,498713,508611,449699)
\tag{4.1}
\]

and let

\[
X=\prod_{i=0}^3[c_i-10^{-6},c_i+10^{-6}].
\tag{4.2}
\]

Thus every coordinate of every point in \(X\) lies strictly between zero and
one, and every denominator in (3.1) is positive.

Take the following exact rational matrix (the displayed integers are divided
by \(10^9\)):

\[
A=10^{-9}
\begin{pmatrix}
-13383725&400203035&-366621029&354376894\\
-351754557&-85428896&734844242&419388191\\
406811707&-743989286&-25608135&734879640\\
-390156929&-490173498&-789170093&133494780
\end{pmatrix}.
\tag{4.3}
\]

It is invertible; exact Gaussian elimination gives

\[
\det A=
\frac{272216186882522042867946943189056919}
{500000000000000000000000000000000000}>0.
\tag{4.4}
\]

Define

\[
G(p)=p-AF(p).
\tag{4.5}
\]

Direct rational interval evaluation of the subset sums defining \(Q_i,N_i\)
on the box \(X\) gives

\[
G(X)-c\subseteq10^{-9}
\bigl([-421,-420],[-480,-479],[-36,-35],[-157,-156]\bigr).
\tag{4.6}
\]

In particular \(G(X)\) lies strictly inside \(X\), whose radius is
\(10^{-6}=1000\cdot10^{-9}\).

The same exact interval differentiation gives the following outward bounds
on the absolute row sums of \(DG=I-A,DF\):

\[
\begin{array}{c|c}
\text{row}&\sup_{p\in X}\sum_j|DG_{ij}(p)|\\ \hline
0&<2.669\cdot10^{-5}\\
1&<4.046\cdot10^{-5}\\
2&<5.758\cdot10^{-5}\\
3&<4.842\cdot10^{-5}.
\end{array}
\tag{4.7}
\]

Here every decimal endpoint in (4.6)--(4.7) denotes the displayed rational
number with denominator a power of ten. These inequalities require only
addition, multiplication, and division of rational interval endpoints after
substituting (2.1) into

\[
Q_i=\sum_{T\subseteq I\setminus\{i\}}
 \Bigl(\prod_{j\in T}p_j\prod_{j\notin T,i}(1-p_j)\Bigr)
 r_i(T\cup\{i\}),
\tag{4.8}
\]

\[
N_i=\frac{
\sum_{\varnothing\ne T\subseteq I\setminus\{i\}}
 \bigl(\prod_{j\in T}p_j\prod_{j\notin T,i}(1-p_j)\bigr)r_i(T)}
{1-\prod_{j\ne i}(1-p_j)}.
\tag{4.9}
\]

Equations (4.3), (4.6), (4.8), and (4.9) form a finite exact certificate;
no floating-point premise is used.

### Theorem 4.1 (exact fully mixed stationary equilibrium)

There is a unique fixed point \(p^*\) of \(G\) in \(X\). It satisfies
\(F(p^*)=0\), hence the stationary profile with quit probabilities \(p^*\)
is exact terminal Nash against unrestricted behavioral deviations.

#### Proof

By (4.7), \(G\) is a contraction on the complete box \(X\) in the sup norm;
by (4.6), it maps \(X\) into itself. Banach's fixed-point theorem gives a
unique fixed point \(p^*\in X\). At that point
\(AF(p^*)=0\). Invertibility (4.4) implies \(F(p^*)=0\). Section 3 then gives
the exact unrestricted terminal Nash conclusion. QED.

The isolating box locates the solution at

\[
p^*\approx
(0.5131245793,0.4987125203,0.5086109642,0.4496988436),
\tag{4.10}
\]

but this approximation is explanatory only; existence is supplied by the
rational certificate.

## 5. Uniform payoff and escape mechanism

The checked theorem
`quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact` makes the
actual terminal payoff \(U(p^*)\) a uniform-equilibrium payoff.

All coordinates of \(p^*\) lie in \((0,1)\), so every nonempty terminal
coalition has positive first-stage—and hence positive eventual—mass. The four
equalities in (3.1) balance distinct pieces of the Gray cycle:

- player 0 balances its singleton/\(2\)-assisted Quit rows against the
  \(1\)-led Never rows;
- player 1 balances \(0\)-assisted Quit against \(3\)-led Never;
- player 2 balances the \(1\)-tie row against the \(\{0,3\}\) Never row; and
- player 3 offsets its negative singleton payoff with the
  \(0,2\)-collision rows against the \(2\)-led Never row.

This is the multi-clock escape absent from the one-clock interval tests. The
pure strict-toggle gain at each cube vertex does not survive averaging over
the full-support collision law.

## 6. Conjecture-facing scope

The updated paid question already checks the exact cap-port trichotomy,
prescribed-singleton same-law double port, and strict minimum-fiber tube. This
note does not reproduce or strengthen those results. Instead it removes the
explicit no-one-clock Gray table as a possible local gadget obstruction:

```text
no pure stationary Nash
+ no one-clock stationary Nash
  does not imply a stationary or all-behavior gap;
the table has an exact fully mixed stationary Nash profile.
```

The result is an exact solved candidate, not a theorem that every Gray cycle
has such an equilibrium. The table lacks a terminal exploitability witness
and positive global semantic minimum, so it cannot realize an inert paid-cap
source from the maintained Fin4 counterexample branch.

No Bellman path, punishment-floor edge, paid return, or minimum-fiber descent
is inferred from its stationary equilibrium.

## 7. Requested independent check

Please independently verify the reward-to-endpoint formulas (3.1), the
pure-time recursion (3.2), the rational interval certificate (especially the
outward directions in (4.6)--(4.7)), and the passage from the fixed point to
unrestricted terminal Nash. The exact certificate proves uniqueness only
inside \(X\), not uniqueness among all stationary equilibria.

