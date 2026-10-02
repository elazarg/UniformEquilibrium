# Fin4 inert paid-mass rectangle and local cycle regression

Author: CHATGPT_EXTERNAL

Status: REVIEWED ORDINARY MATHEMATICS; INTERNAL/NO EXPORT; DOES NOT CONSUME THE INERT STALL

Independent review:

- feedback/FOUR_PLAYER_INERT__BY_CODEX_MINER.md

The review validates equations (1)--(6) and the entire six-state regression.
It requires the output to be described as two sequential profitable behavioral
replacements plus a positive-measure pure-time rectangle family, not as any
maintained fixed-law reset dispatch, paid-cap source, double port, or inert
stall object.

Source: ../FOUR_PLAYER_INERT.md

## Question and honest scope

Can the maintained four-player terminal-gap/minimum-debt/inert paid-source
package be converted into a cumulative admissible return, a well-founded
semantic descent, or a contradiction?

The supplied argument does not do this. It gives a quantitative terminal-law
rectangle at actual near-minimum profiles and a four-player regression showing
that the corresponding local inert/paid/reset data can cycle when the global
minimum is zero. The potential value is therefore a stronger source packet,
not a consumer of the literal inert cap stall.

## Quantitative paid-mass extraction

Assume four players, terminal rewards bounded in absolute value by \(M\), a
terminal gap \(\gamma>0\), and actual profiles \(\sigma_n\) with
\(D(\sigma_n)\to D_*>0\). After a subsequence choose one observer \(o\) with
\(d_o(\sigma_n)\ge\gamma\), and choose a pure time \(q_n\) within
\(\gamma/8\) of its cap. Write

\[
F_n(t)=U_o(\sigma_n[o\leftarrow t])
\]

and let \(\mu_{o,n}\) be the observer's prescribed stopping-time law. Define

\[
A_n=\{s:F_n(q_n)-F_n(s)\ge\gamma/2\},\qquad
\alpha_n=\mu_{o,n}(A_n).
\]

Stopping-law affinity gives

\[
\frac{7\gamma}{8}
 \le 2M\alpha_n+\frac\gamma2(1-\alpha_n),
\]

and hence

\[
\boxed{\alpha_n\ge
\frac{3\gamma}{16M-4\gamma}\ge\frac\gamma{8M}.} \tag{1}
\]

Every \(s\in A_n\) has a first-disagreement survival factor at least
\(\gamma/(4M)\). Thus the prescribed-law-weighted reached mass of these paid
rows is at least \(\gamma^2/(32M^2)\).

Move exactly the mass on \(A_n\) to \(q_n\), obtaining a literal stopping law

\[
\nu_{o,n}=\mu_{o,n}|_{A_n^c}+\alpha_n\delta_{q_n}
\]

and profile \(\rho_n=\sigma_n[o\leftarrow\nu_{o,n}]\). The owner's prescribed
payoff rises by

\[
g_n\ge\frac{\gamma^2}{16M}, \tag{2}
\]

while its cap is unchanged. Since \(\rho_n\) is actual and
\(D(\rho_n)\ge D_*\), once
\(D(\sigma_n)-D_*\le\gamma^2/(32M)\), the other three coordinates acquire
aggregate debt at least \(\gamma^2/(32M)\). Therefore, after a subsequence, one
fixed \(j\ne o\) satisfies

\[
d_j(\rho_n)-d_j(\sigma_n)\ge\frac{\gamma^2}{96M}. \tag{3}
\]

## Literal payoff rectangle

Choose a pure time \(p_n\) within
\(\varepsilon=\gamma^2/(200M)\) of \(j\)'s cap at \(\rho_n\). For

\[
x_{00}=\sigma_n,\quad x_{01}=\rho_n,\quad
x_{10}=\sigma_n[j\leftarrow p_n],\quad
x_{11}=\rho_n[j\leftarrow p_n],
\]

the literal payoff rectangle

\[
R_n=U_j(x_{11})-U_j(x_{10})-U_j(x_{01})+U_j(x_{00})
\]

satisfies

\[
\boxed{R_n\ge\frac{\gamma^2}{200M}.} \tag{4}
\]

Disintegrate \(j\)'s prescribed law at a pure time \(a\) and the moved owner
mass at \(s\in A_n\). The pure-time square

\[
\Delta_n(a,s)=U_j(p_n,q_n)-U_j(p_n,s)-U_j(a,q_n)+U_j(a,s)
\]

averages exactly to \(R_n\). With
\(\theta=\gamma^2/(400M)\), the set

\[
P_n=\{(a,s):s\in A_n,\ \Delta_n(a,s)\ge\theta\}
\]

has product-law mass at least

\[
\boxed{(\mu_{j,n}\otimes\mu_{o,n})(P_n)
\ge\frac{\gamma^2}{1600M^2}.} \tag{5}
\]

For every selected square, the two untouched players survive to the earliest
two-label disagreement with probability at least the same constant. A finite
subfamily retaining half the product-law mass therefore has total
source-weighted reached mass at least

\[
\boxed{\frac{\gamma^4}{5{,}120{,}000M^4}.} \tag{6}
\]

Each positive rectangle also has a positive reward-weighted absorbing
terminal-outcome contribution. This last statement is a signed rectangle-atom
certificate; it must not be described as a lower bound on one source
terminal-atom mass without an additional conversion.

## What this packet is and is not

Equations (1)--(6) retain actual stopping-law provenance, a fixed owner and
recipient after subsequences, paid owner mass, a positive receiver rectangle,
and untouched-player survival. Precisely, they give two sequential profitable
behavioral replacements and a positive-measure family of pure-time rectangles.
They do not instantiate a maintained fixed-law reset dispatch, paid-cap source,
double port, or inert-stall structure. They also do not show that either
whole-strategy reset is an exact prescribed-payoff Nash--Bellman edge, that the
packet lies on one punishment-floor chronology, or that it can be regenerated
after a semantic descent.

The current TerminalSemanticPositiveSlopeRectangle machinery already decodes
literal positive rectangles and absorbing rectangle atoms. A review must
determine whether (1), (5), and (6) add a genuinely useful interface or merely
strengthen provenance on an already unconsumed curvature branch.

## Four-player local separation model

The supplied rational reward table has players \(1,2,3,4\), with player \(4\)
included in each of six sure-exit coalitions

\[
124\to24\to234\to34\to134\to14\to124.
\]

At the six corresponding pure date-zero profiles the debt vectors cycle as

\[
(1,0,0,1),\ (0,0,1,1),\ (0,1,0,1),
(1,0,0,1),\ (0,0,1,1),\ (0,1,0,1),
\]

and every displayed arrow is an exact unilateral best-response reset of gain
one. The terminal laws are deterministic nonsingletons, the first-disagreement
reach is one, total debt is constantly two, and the cycle returns to the
literal initial behavioral profile.

At every one of these profiles, the cap continuation has all-Continue as its
unique exact product Nash root: player \(4\) strictly continues in any root;
conditional on this, players \(1,2,3\) also strictly continue. All own-singleton
margins are strict. Nevertheless all-Never is an exact equilibrium elsewhere,
so \(D_*=0\).

This is a valid local no-go: inertness, strict singleton margins,
nonsingleton laws, paid rows, and even an exact closed cycle of behavioral
best-response resets do not suffice. It is not a counterexample and does not
show the same cycle can occur on a positive global-minimum fiber.

## Remaining implication

The live Fin4 obligation remains to use the positive global minimum and hard
residual provenance to turn the rectangle packet into either:

1. a source-matched exact punishment-floor edge or cumulative return; or
2. a regenerated minimum-fiber source with a strict well-founded debt/support
   decrease.

Without that step, the result does not close either the descent or inert arm
of questions/FIN4_HARD_RESIDUAL_SEMANTIC_CLOSURE.md.

## Review disposition

The independent audit confirms the paid-mass, rectangle-measure, survival, and
cycle calculations. Generic rectangle and absorbing-atom existence are already
checked; the genuinely new part is the quantitative mass-family provenance in
(1), (5), and (6). No maintained consumer uses that strengthening, and the
regression has \(D_*=0\). The result therefore remains internal and is not an
export candidate.
