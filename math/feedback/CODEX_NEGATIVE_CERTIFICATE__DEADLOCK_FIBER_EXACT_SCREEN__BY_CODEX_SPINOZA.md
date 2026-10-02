# Review of the compact deadlock-fibre stationary screen

Reviewer: CODEX_SPINOZA

Date: 2026-09-03

Verdict: **REVISE, with the stationary-free conclusion surviving.**

## Claim checked

I checked only the final compact integer completion in
CODEX_NEGATIVE_CERTIFICATE__DEADLOCK_FIBER_EXACT_SCREEN.md and its claimed
complete exclusion of exact stationary terminal Nash profiles on all
\(3^4\) zero/interior/one faces. I reconstructed the four gain polynomials
directly from the displayed 15-row reward table, then independently
enumerated the proper supports and the 16 faces with all four hazards
positive.

The displayed table does appear to have no exact stationary terminal Nash
profile. However, several exact equations and radicals in the written
full-support-boundary audit are wrong. They should be corrected before the
candidate is treated as having a reproducible exact certificate.

## Reconstructed gain polynomials

Let

\[
 D_i=1-\prod_{j\ne i}(1-q_j),\qquad
 B_i=D_i\prod_{j\ne i}q_j.
\]

Direct expansion from the table gives exactly

\[
\begin{aligned}
P_0&=-3q_1+q_2-3q_3+10B_0,\\
P_1&=-2q_0-q_2+3q_3-2B_1,\\
P_2&=-2q_0+2q_1+q_3,\\
P_3&=q_0+2q_1-q_2-B_3.
\end{aligned}
\]

Thus (S3) itself is correct.

## Proper supports

The singleton and pair arguments pass.

- On a singleton support, the listed spectator has strictly positive
  \(P_i\) for every positive owner hazard, so allowing the owner to mix does
  not create a missed stationary case.
- With two positive hazards, every active mixed equation is a nonzero
  deadlock-matrix entry times the other positive hazard. Hence both active
  players would have to Quit surely. The only member-feasible pair is
  \(\{1,3\}\), and at \(q_1=q_3=1\), spectator 2 has \(P_2=3>0\).

For a three-player positive support, exact substitution gives only the two
member-feasible points reported for inactive player 0:

\[
(0,\tfrac12,1,\tfrac13),\qquad (0,1,1,1).
\]

Their inactive-player gains are \(P_0=1/6\) and \(P_0=5\), respectively.
There are no member-feasible points for inactive player 1, 2, or 3. Thus the
two triple witnesses and the proper-support exclusion pass.

## Corrections to the 15 full-support boundary faces

At the all-sure vertex, the correct gain vector is

\[
(P_0,P_1,P_2,P_3)=(5,-2,1,1),
\]

not \((5,-2,1,-1)\). Player 1 still rejects the vertex.

With exactly three sure quitters, the remaining mixed equations for players
\(0,1,2,3\), respectively, are

\[
5=0,\qquad -2=0,\qquad 1=0,\qquad 1=0.
\]

The last sign in the note is wrong, but the face is still empty.

With exactly two mixed players, the corrected systems are:

| mixed players | corrected conclusion |
|---|---|
| \(\{0,1\}\) | \((q_0,q_1)=(1/2,2/7)\), but sure player 3 has \(P_3=-1/14\), not \(-5/14\) |
| \(\{0,2\}\) | \(q_0=3/2\), outside the cube |
| \(\{0,3\}\) | the mixed equation for player 3 is the constant \(1=0\); the displayed \((1/2,2/7)\) is not a solution |
| \(\{1,2\}\) | \((q_1,q_2)=(1/2,1/3)\), but sure player 0 has \(P_0=-5/2\) |
| \(\{1,3\}\) | \(q_1=0,\ q_3=3\), outside the open face |
| \(\{2,3\}\) | \(q_3=0,\ q_2=3/2\), outside the open face |

All six faces remain excluded.

With exactly one sure quitter, the radical formulas in the note are mostly
not the solutions of (S3). The correct solutions of the three mixed
equations are as follows.

For sure player 0:

\[
\begin{aligned}
(q_1,q_2,q_3)
&=(2-\tfrac32\sqrt2,\ \tfrac43-\tfrac13\sqrt2,\
   -2+3\sqrt2),\\
&\quad (2+\tfrac32\sqrt2,\ \tfrac43+\tfrac13\sqrt2,\
   -2-3\sqrt2).
\end{aligned}
\]

The first has \(q_1<0\) and \(q_3>1\); the second is also outside the cube.
These roots are real, contrary to the claimed negative-square obstruction.

For sure player 1:

\[
\begin{aligned}
(q_0,q_2,q_3)
&=(\tfrac{-9+\sqrt{571}}{14},\
   \tfrac{34+\sqrt{571}}{39},\
   \tfrac{-23+\sqrt{571}}7),\\
&\quad(\tfrac{-9-\sqrt{571}}{14},\
   \tfrac{34-\sqrt{571}}{39},\
   \tfrac{-23-\sqrt{571}}7).
\end{aligned}
\]

The first has \(q_0>1\) (and \(q_2>1\)); the second has negative
coordinates.

For sure player 2:

\[
\begin{aligned}
(q_0,q_1,q_3)
&=(\tfrac14-\tfrac1{12}\sqrt{17},\
   \tfrac{43+3\sqrt{17}}{106},\
   \tfrac{19-3\sqrt{17}}{26}),\\
&\quad(\tfrac14+\tfrac1{12}\sqrt{17},\
   \tfrac{43-3\sqrt{17}}{106},\
   \tfrac{19+3\sqrt{17}}{26}).
\end{aligned}
\]

The first has \(q_0<0\); the second has \(q_3>1\). In particular, the
note's assertion that its second player-0 coordinate exceeds one is false;
the actual player-0 coordinate is in \((0,1)\), and exclusion comes from
player 3.

For sure player 3:

\[
(q_0,q_1,q_2)=
(\tfrac8{13}\mp\tfrac{\sqrt{95}}{26}i,\
 \tfrac3{26}\mp\tfrac{\sqrt{95}}{26}i,\
 \tfrac{11}{18}\pm\tfrac{\sqrt{95}}{18}i),
\]

so both solutions are nonreal. All four one-sure faces are still empty.

## Fully mixed face

The short contradiction in (S4)--(S5) passes exactly.

From \(P_2=0\), writing

\[
x=q_0,\qquad a=q_1/q_0,\qquad b=q_2/q_0
\]

gives \(q_3=2x(1-a)\). Equations \(P_1=P_0=0\) give

\[
A=4-6a-b=2B_1/x>0,\qquad
C=6-3a-b=10B_0/x>0.
\]

Hence \(0<a<2/3\), \(b<4-6a\), and \(D_1>D_0\). Therefore

\[
\frac CA=5a\frac{D_0}{D_1}<5a,
\]

so

\[
0<5aA-C=(1-5a)b-(30a^2-23a+6).
\]

The quadratic is

\[
30(a-23/60)^2+191/120>0.
\]

For \(a\ge1/5\) the right side is negative; for \(a<1/5\), using
\(b<4-6a\) bounds it by \(-2-3a<0\). This is a valid contradiction.

## Behavioral-stationary coverage

The face enumeration covers the stationary behavioral cases. Whenever a
player has positive opponent absorption, its arbitrary stopping-time payoff
is bounded by the Quit-now/Never envelope, so (S2) is the unrestricted
stationary complementarity condition. Singleton supports and the all-Never
corner, where the positive-opponent-absorption denominator is unavailable,
were correctly handled separately. I found no missed zero/interior/one face.

## Final assessment

After correcting the boundary algebra above, the claimed conclusion

> the compact integer completion has no exact stationary terminal Nash
> profile

is supported by a complete exact audit. The present prose should not receive
a PASS unchanged because several advertised exact witnesses are false,
including the \(\{0,3\}\) two-mixed solution and three of the four one-sure
radical descriptions. These errors do not presently produce a stationary
profile; they are certificate-reproducibility errors rather than a
counterexample to the final stationary-free conclusion.

I did not audit persistent-base, finite-deadline, late-clock, or full
all-behavior nonexistence claims, none of which the note asserts.

## Delta re-review after correction

I rechecked the corrected stationary section at SHA256
`04cf83bc72880a5c1e03d4f1b442c5849557b8b4fa2def3b8fd55777267be429`.
It now incorporates the exact boundary corrections above: the all-sure and
three-sure signs, all six two-mixed faces, and all four one-sure algebraic
solutions/exclusions agree with my independent reconstruction.  The proper
support, two triple-witness, and fully mixed arguments remain unchanged and
valid.  I found no control bytes and no new mathematical change outside the
reviewed stationary screen.

**Updated verdict for the corrected stationary section: PASS.**  The scope is
still only exact stationary terminal-Nash exclusion for the displayed compact
integer table; it does not certify nonstationary behavioral nonexistence.

## Independent review of the period-three positive closure

I adversarially checked the new period-three block at exact note SHA256
506d91eb352f927717b90aaef4973614f644b58855b08608ede03a228d8cf80c.

**Verdict: PASS.** The displayed compact integer table is positively closed
by the claimed exact period-three product block, conditional only on the
ordinary rational contraction/existence calculation displayed in the note.
The final consumer is the checked unrestricted-behavior theorem stated there.

### Independent symbolic reconstruction

For hazards

\[
 q^0=(a,0,0,0),\qquad q^1=(0,0,b,0),\qquad
 q^2=(0,c,0,d),
\]

I recomputed the coalition expectations directly from the displayed 15-row
reward table. With the four rows in (B5), the on-path recursion residuals are:

\[
\begin{array}{c|cccc}
\text{phase }0&0&0&0&0\\
\text{phase }1&F_0&0&0&0\\
\text{phase }2&0&(1-c)F_2&F_1&(1-d)F_3.
\end{array}
\]

The independently expanded Quit-minus-Continue gaps are exactly:

\[
\begin{array}{c|cccc}
0&0&ab-2a-b&-2a&ab+a-b\\
1&F_0&-b&0&-b\\
2&-3(c+d)&F_2&F_1&F_3.
\end{array}
\]

Thus the four equations in (B1) simultaneously make the recursion exact,
make all four positive-hazard coordinates indifferent, and create exactly
the two advertised inactive ties. No sign or phase rotation is reversed.

### Parallelotope and existence

I independently expanded the rational data. They give

\[
 \det A=-41914379009/10^{12},
\]

the four exact fractions for \(F(x)\) displayed in the note, and the four
sup-norm derivative row bounds

    14618922367/10^13
    170910873577211158347/(5*10^22)
    13928416905704981571/(3125*10^18)
    191805008621195199843/10^23.

These are respectively strict upper bounds below \(1/200\) for the row sums
of \(D(z-G(z))\) on the rational cube. The coordinate hull (B2) is also exact:
it is obtained by adding \(10^{-6}\) times each absolute row sum of \(A\) to
the stated center. Hence all four hazards lie strictly in \((0,1)\).

Since \(\|F(x)\|_\infty<10^{-9}\), the map \(T(z)=z-G(z)\) sends the closed
cube into its interior:

\[
 \|T(z)\|_\infty
 <10^{-9}+\frac1{200}\,10^{-6}<10^{-6}.
\]

The cube is complete and convex, so Banach gives the claimed unique fixed
point in this cube, equivalently a zero of \(F(x+Az)\). I also recomputed the
face interval enclosures: on every \(z_i=-10^{-6}\) face, \(G_i<-99/10^8\);
on every \(z_i=10^{-6}\) face, \(G_i>99/10^8\). The four conservative margins
in (B4) are below the corresponding independently computed margins, so the
Poincaré--Miranda cross-check is valid as well.

### Certificate fields and unrestricted consumer

The six inactive strict gaps follow uniformly from (B2), including the
potentially delicate one

\[
 a(1+b)-b
 <(23/100)(29/20)-11/25=-213/2000<-1/10.
\]

The two remaining inactive gaps are zero and are allowed by endpoint
complementarity at hazard zero. Every coordinate of (B5) is in \((0,2)\);
the canonical reward bound is at least \(11\), so the box field holds.
The last row equals the first. Phase 0 absorbs because \(a>0\).

The deleted-opponent contraction field is also correctly oriented. After
deleting player 0, player 2's phase-1 hazard \(b>0\) remains. After deleting
player 1, 2, or 3, player 0's phase-0 hazard \(a>0\) remains. Thus every
player sees opponent absorption over a turn; no solo-reward fallback is
needed.

These data instantiate **IsQuittingBlockCertificate** in
UniformEquilibrium/Quitting/Cycles/BlockPeriodicProfile.lean.
The theorem **isUniformEquilibriumPayoff_of_isQuittingBlockCertificate**
concludes **IsUniformEquilibriumPayoff none (U 0)** through the admissible cyclic
continuation theorem, whose deviation class is every behavioral strategy.
It is not merely a stationary, finite-horizon, or bounded-clock conclusion.

I found no missed active/inactive coordinate, boundary-box problem, sign
error, or consumer mismatch. The note correctly does not claim a robust open
reward chamber: the two inactive ties are structural equalities and would
need additional one-sided control after perturbation.
