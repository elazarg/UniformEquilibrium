# From absorbing row-perfect sequences to approximate equilibrium

## Quitting-game data

Let \(I\) be a finite player set. At every live stage, each player chooses
Continue or Quit. If the nonempty set \(S\subseteq I\) of players chooses Quit,
the game terminates and pays

\[
  r(S)=(r^i(S))_{i\in I}\in\mathbb R^I.
\]

If nobody ever quits, the payoff is the arbitrary vector
\[
  z=(z^i)_{i\in I}\in\mathbb R^I.
\]

Write \(r(\varnothing):=z\) when the empty coalition is included in the
reward notation.

A mixed row \(q=(q^i)_{i\in I}\in[0,1]^I\) assigns player \(i\) Quit
probability \(q^i\). Actions are independent within the row. Its probability
of exactly the quitting coalition \(S\subseteq I\), including \(S=\varnothing\),
is

\[
  p_q(S)
  :=\prod_{i\in S}q^i\prod_{j\in I\setminus S}(1-q^j).
\]

Write
\[
  c(q):=p_q(\varnothing)=\prod_{i\in I}(1-q^i)
\]
for its all-Continue probability.

## Root sequences, survival, and restarted tails

A root sequence is \(x=(q_n)_{n\ge0}\), where every \(q_n\in[0,1]^I\).
For \(m\ge0\), its restarted tail is
\[
  x_{\ge m}:=(q_{m+n})_{n\ge0}.
\]

Define survival through the first \(N\) rows by

\[
  a_{0,N}(x):=\prod_{t=0}^{N-1}c(q_t),
  \qquad a_{0,0}(x):=1.
\]

More generally, survival in the tail restarted at stage \(m\) is

\[
  a_{m,N}(x):=\prod_{t=m}^{N-1}c(q_t)
  \quad(N\ge m),
  \qquad
  a_{m,\infty}(x):=\lim_{N\to\infty}a_{m,N}(x).
\]

The limit exists because the finite products are decreasing and lie in
\([0,1]\).

The sequence is **initially absorbing** when

\[
  a_{0,\infty}(x)=0.
\]

It has **every-tail termination** when

\[
  a_{m,\infty}(x)=0
  \qquad\text{for every }m\ge0.
\]

These are different conditions. If \(c(q_0)=0\), then the sequence is
initially absorbing regardless of every later row. In particular, all later
rows may be all-Continue, so the tail restarted at stage \(1\) need not
terminate.

## Restarted-tail terminal payoff

The payoff of the tail started anew at stage \(m\) is

\[
\begin{split}
  \gamma_m^i(x)
  := {}&
  \sum_{n=m}^{\infty}
    a_{m,n}(x)
    \sum_{\varnothing\ne S\subseteq I}
      p_{q_n}(S)\,r^i(S)\\
  &\quad + a_{m,\infty}(x)z^i .
\end{split}
\tag{1}
\]

The series is absolutely convergent. Indeed,

\[
  \sum_{\varnothing\ne S\subseteq I}p_{q_n}(S)=1-c(q_n)
\]

and, for every \(N>m\),

\[
  \sum_{n=m}^{N-1}a_{m,n}(x)(1-c(q_n))
  =1-a_{m,N}(x).
\]

The terminal mass coefficients therefore sum to
\(1-a_{m,\infty}(x)\). Since \(I\) is finite, the reward table is bounded,
which proves absolute convergence and also shows that the terminal and Never
coefficients in (1) sum to one.

Formula (1) is used even when stage \(m\) has probability zero under the
original sequence: it is the payoff of the specified tail restarted as a
fresh game, not a conditional expectation on a null event.

## One-stage values and row perfection

Fix a row \(q_n\), a player \(i\), and continuation payoff
\(\gamma_{n+1}(x)\). For \(T\subseteq I\setminus\{i\}\), set

\[
  p_{q_n}^{-i}(T)
  :=\prod_{j\in T}q_n^j
    \prod_{k\in I\setminus(T\cup\{i\})}(1-q_n^k).
\]

If player \(i\) chooses Quit surely while the opponents retain their row, her
one-stage value is

\[
  Q_n^i(x)
  :=\sum_{T\subseteq I\setminus\{i\}}
       p_{q_n}^{-i}(T)\,r^i(T\cup\{i\}).
\tag{2}
\]

If she chooses Continue surely, her value is

\[
  C_n^i(x)
  :=\sum_{\varnothing\ne T\subseteq I\setminus\{i\}}
       p_{q_n}^{-i}(T)\,r^i(T)
    +p_{q_n}^{-i}(\varnothing)\gamma_{n+1}^i(x).
\tag{3}
\]

The successor value under the prescribed mixed action is

\[
  V_n^i(x):=q_n^iQ_n^i(x)+(1-q_n^i)C_n^i(x).
\tag{4}
\]

Decomposing (1) at its first row gives the indexing identity

\[
  \gamma_n^i(x)=V_n^i(x).
\]

The row \(q_n\) is **playerwise \(\varepsilon\)-perfect against its actual
restarted-tail value** when, for every player \(i\),

\[
\begin{array}{rcl}
  Q_n^i(x)&\le&V_n^i(x)+\varepsilon,\\
  C_n^i(x)&\le&V_n^i(x)+\varepsilon,\\
  q_n^i>0&\Longrightarrow&V_n^i(x)\le Q_n^i(x)+\varepsilon,\\
  1-q_n^i>0&\Longrightarrow&V_n^i(x)\le C_n^i(x)+\varepsilon.
\end{array}
\tag{5}
\]

The first two inequalities say that neither pure action gains more than
\(\varepsilon\). The last two say that every action used with positive
probability is within \(\varepsilon\) from below. These four inequalities,
not a claim that the entire strategy is a best response in every subgame, are
the meaning of rowwise sequential perfection here.

## Behavioral profiles and terminal Nash equilibrium

While the game is live, every earlier player must have chosen Continue at
every earlier date; any Quit would already have ended the game. Hence there is
exactly one live public history of each finite length. A behavioral strategy
for player \(i\), restricted to the histories at which an action is still
chosen, is therefore exactly a sequence
\(\sigma^i=(\sigma_n^i)_{n\ge0}\) of Quit probabilities in \([0,1]\), one for
each possible survival date. Conversely, every such sequence specifies a
behavioral strategy at every live history. Thus a behavioral profile
\(\sigma=(\sigma^i)_{i\in I}\) is a root sequence and has terminal payoff
\(U_i(\sigma):=\gamma_0^i(\sigma)\).

A profile is **stationary** when there is one row \(q\in[0,1]^I\) such that
\(q_n=q\) for every \(n\).

A unilateral behavioral deviation by player \(i\) is any other sequence
\(\tau^i=(\tau_n^i)_{n\ge0}\) of Quit probabilities. It replaces only player
\(i\)'s coordinates in every row; all opponents retain
\(\sigma^{-i}\).

The profile \(\sigma\) is a **terminal \(\eta\)-Nash equilibrium** when

\[
  U_i(\tau^i,\sigma^{-i})
  \le U_i(\sigma)+\eta
  \quad\text{for every }i\in I
  \text{ and every unilateral behavioral deviation }\tau^i.
\tag{6}
\]

Approximate-equilibrium existence means that for every \(\eta>0\), some
behavioral profile satisfies (6). The profile may depend on \(\eta\); no
common payoff target is required.

## Absorbing row-perfect sources

Assume

\[
\begin{split}
\exists\varepsilon_0>0\ \forall\varepsilon\,
  \bigl(0<\varepsilon<\varepsilon_0\bigr)\Longrightarrow
  \exists x^\varepsilon=(q_n^\varepsilon)_{n\ge0}\quad&
  a_{0,\infty}(x^\varepsilon)=0,\\
  &\text{every row }q_n^\varepsilon
    \text{ satisfies (5) for every }n.
\end{split}
\tag{A}
\]

The threshold \(\varepsilon_0\) is fixed, but the witnessing root sequence
may depend on \(\varepsilon\). Every continuation in (5) is the actual
restarted-tail payoff (1), including residual Never payoff.

## Question

For every finite player set and reward table, does (A) imply
approximate-equilibrium existence? Explicitly, prove

\[
  \text{(A)}
  \quad\Longrightarrow\quad
  \forall\eta>0\ \exists\sigma\
  \text{such that \(\sigma\) satisfies (6).}
\tag{R}
\]

The conclusion may use any behavioral profile \(\sigma\). It need not use the
particular root sequence \(x^\varepsilon\) supplied by (A), and profiles
chosen at different errors need not be related.

An equally complete resolution is a finite payoff table \(r,z\) which
satisfies (A) but has no terminal \(\eta\)-Nash equilibrium for some
\(\eta>0\).

## Reduction of nonterminating restarted tails

The row inequalities imply the following observation: if a sequence
satisfies (5) and \(a_{m,\infty}(x)>0\) for some restart \(m\), then

\[
  r^i(\{i\})\le z^i+\varepsilon\qquad(i\in I).
\]

Indeed positive restarted survival forces all hazards to tend to zero and
the later restarted payoffs to tend to \(z\); taking limits in the Quit
inequality gives the bound.

All Continue is an exact terminal equilibrium precisely when
\(r^i(\{i\})\le z^i\) for every player. Otherwise choose a player with
\(d=r^i(\{i\})-z^i>0\). Every row-perfect witness at error
\(0<\varepsilon<d\) must then terminate after every restart. Thus the
question reduces to every-tail witnesses unless all Continue already solves
the game; a nonterminating null tail is not a separate obstruction.

## Why the supplied-profile shortcut is false

Even every-tail termination and exact rowwise perfection do not imply that the
supplied root sequence itself is an approximate equilibrium.

For example, take \(I=\{1,2\}\), \(z=(0,0)\), let player 2's terminal payoff
always be zero, and let player 1 receive \(-1\) whenever player 1 belongs to
the quitting coalition and \(0\) otherwise. At every stage prescribe player 1
to Quit surely and player 2 to Continue surely. Every restarted tail
terminates at its first row. In (2)--(4), both available actions give player 1
value \(-1\), while both give player 2 value \(0\); hence every row is exactly
0-perfect.

Yet player 1 can deviate to Continue forever. Then nobody quits, so her payoff
changes from \(-1\) to \(z^1=0\), a gain of one. The supplied profile is not a
terminal \(\eta\)-Nash equilibrium for any \(\eta<1\). On the other hand, the
all-Continue profile is an exact stationary equilibrium of this game.
Therefore the example refutes only the supplied-profile shortcut, not
(R).

## Scope

Any counterexample to (R) must rule out every behavioral profile in (6), not
only the supplied row-perfect sequences. Conversely, a positive proof may
construct any actual approximate equilibria; it need not preserve the source
sequence, its chronology, or its payoffs.
