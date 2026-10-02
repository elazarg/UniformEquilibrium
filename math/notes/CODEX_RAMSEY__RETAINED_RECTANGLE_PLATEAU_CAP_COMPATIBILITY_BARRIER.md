# Retained rectangle plateau: the missing fixed-cap compatibility

Author: `CODEX_RAMSEY`

Status: **complete bounded producer audit; exact local separation model;
internal and awaiting independent review.**

The full common-response square which precedes
`QuittingStoppingLawVanishingDebtRectangleSequence` does not eliminate the
unique-all-Continue fixed-law plateau.  The square controls the observer's
response, prescribed payoff, and one terminal-law atom.  It supplies no Nash
condition for the mover or the other players against the fixed-law
minimizer's cap vector.  A two-player rational table below simultaneously has

- a positive normalized mover-to-observer debt slope;
- the complete common-response square with zero endpoint observer debt;
- a positive observer-containing collision atom and strict reverse toggle;
- an exact strict fixed-law/global observer-reset premium; and
- a fixed-law minimizer whose unique exact cap root is all Continue.

Thus the maximal exact-cap stack is literally inert even before the public
rectangle packet erases the square.  This is not a counterexample to the
positive-minimum theorem: the table has a zero-debt terminal profile and no
terminal exploitability witness.  It is a sharp separation of the proposed
*local* use of the witness.  Any proof from the genuine counterexample data
must use the ambient terminal witness/global minimum to produce new
source-matched information, not merely use the witness's supported-toggle or
local-debtor consequence.

The exact missing datum is fixed-cap Nash compatibility of the reached
rectangle row.  If the positive-mass rectangle rows had total Nash defect
tending to zero against the retained minimizer's cap, compactness would give
an absorbing exact cap root and contradict the plateau.  The existing source
controls only the observer coordinate; the example puts the entire defect on
the mover.

## 1. Producer question and answer

The requested producer starts with the actual positive-minimum tangent data,
the literal common-response square, its endpoint law, a terminal
exploitability witness, and the fixed-law/global reset bridge.  It should
produce one of:

1. an exact punishment-floor cap prefix entering the separated lower reset
   sublevel with fixed cumulative charge;
2. a re-extractable strict support-rank descent on the global minimum fiber;
3. a terminal approximate-Nash/uniform-payoff consumer.

The current fields do not prove any of the three in the all-Continue arm.
The strongest exact conclusion is the following interface separation.

> A positive response rectangle remains compatible with a unique
> all-Continue cap correspondence because its positive cross-effect is a
> one-player statement.  The non-observer coordinates may reject the
> rectangle row by a fixed cap-Nash defect.  The terminal outcome law and the
> response-square payoff identity do not constrain that defect.

This is stronger than observing that
`QuittingStoppingLawVanishingDebtRectangleSequence` drops fields: restoring
all fields of `QuittingStoppingLawCommonResponseWitness` still leaves the
same obstruction.

## 2. Declarations inspected

The audit was performed at
`main@29a172f34a919f925bd1109a55c75c9a55d4078c`.

### Full upstream square

In
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/VanishingDebtAtomAlternative.lean`:

- `QuittingStoppingLawCommonResponseWitness`;
- `exists_quittingStoppingLawCommonResponseWitness_of_endpointDebtRise`;
- `QuittingStoppingLawCommonResponseWitness.exists_endpointGainAtom`;
- `QuittingStoppingLawCommonResponseWitness.sourcePositiveGain_tendsto_zero`;
- `hasVanishingDebtAtomAlternative_of_endpointDebtRise`; and
- `exists_prescribedAtom_or_pureTimeRectangleAtom_with_debtBound`.

The full witness stores the observer endpoint debt, endpoint gain, difference
of endpoint/source gains, and the positive part of the source gain.  It has no
root-Nash condition for another player.

### Rectangle and reset bridge

In
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/OffDiagonal/AtomRectangleSequenceAlternative.lean`
and
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/RectangleResetFaceMinimizer.lean`:

- `QuittingStoppingLawVanishingDebtRectangleSequence`;
- `QuittingStoppingLawRectangleResetFaceDispatch`;
- `QuittingStoppingLawRectangleJointAtomLimit`;
- `QuittingStoppingLawRectangleJointAtomLimit.exists_fixedLawResetDispatch`;
- `QuittingStoppingLawRectangleMinimizerBridge`;
- `QuittingStoppingLawRectangleJointAtomLimit.nonempty_minimizerBridge`; and
- `QuittingStoppingLawRectangleMinimizerBridge.eventually_literal_lawPremium`.

The bridge retains the endpoint law and static atom/incidence at the fixed-law
selector.  It does not retain the common source/update square as a relation
between actual profiles realizing `bridge.fixed`.  In the strict branch it
also does not make the fixed selector globally minimal on the whole reset
face.

In
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceCapReturn.lean`,
`QuittingFixedLawResetDispatch.dynamic_exit` gives an absorbing strict-debt
prefix or an all-Continue cap fixed point.  The same file's checked namespace
`QuittingResetIncidenceCapRegression` already shows that positive incidence
and a supported toggle do not Nashify the other coordinate.  The model below
strengthens that boundary by including the entire common-response square and
a strict law premium.

The actual positive-row localization is already checked as
`QuittingStoppingLawVanishingDebtRectangleSequence.positiveTarget_reachedRowLocalization`
in `StoppingLaw/OffDiagonal/PureTimeReachedRowLocalization.lean`.  The compact
fixed-cap defect separation used below overlaps the checked
`exists_totalNashDefect_moat_of_unique_allContinue` in
`TerminalSemanticPlateauNashMoat.lean`.  The new point here is the producer
comparison: the upstream square supplies the former row but not the cap
compatibility needed to escape the latter moat.

The notes
`CHATGPT_EXTERNAL__RETAINED_LAW_PREMIUM_RETURN_DESCENT_PLATEAU.md` and
`CHATGPT_EXTERNAL__ALIGNED_RESET_MINIMUM_CLASSIFICATION.md` were also checked.
Their conditional lower-face entrance calculation is compatible with the
present result: the missing step is existence of the entrance.

## 3. Exact two-player square

Let the players be `o` (observer) and `m` (mover), and fix a rational
parameter

\[
  0<d<1.
\]

The nonempty-coalition rewards are

\[
\begin{array}{c|ccc}
 & \{o\}&\{m\}&\{o,m\}\\ \hline
r_o&0&0&1\\
r_m&1&d&0.
\end{array}
\tag{3.1}
\]

Infinite all-Continue play pays zero.  At one fixed date (or after any common
finite all-Continue delay) define four literal profiles:

\[
\begin{array}{c|cc|c}
 &o&m&\text{terminal law}\\ \hline
X&N&N&\delta_\varnothing\\
E&N&Q&\delta_{\{m\}}\\
Y&Q&N&\delta_{\{o\}}\\
Z&Q&Q&\delta_{\{o,m\}}.
\end{array}
\tag{3.2}
\]

Here `X` is the common source, `E` is its full mover replacement, `Y` is the
source response, and `Z` is the endpoint response.

### 3.1 The common-response inequalities

For the observer,

\[
 U_o(X)=U_o(E)=U_o(Y)=0,
 \qquad U_o(Z)=1.
\]

Against `E`, quitting at the mover's date gives one and every other pure
response gives at most one, so

\[
 d_o(E)=1,qquad d_o(Z)=0.
\tag{3.3}
\]

The response gain and square difference are

\[
 U_o(Z)-U_o(E)=1,
\]

\[
 [U_o(Z)-U_o(E)]-[U_o(Y)-U_o(X)]=1.
\tag{3.4}
\]

Moreover

\[
 \max(0,U_o(Y)-U_o(X))=0=d_o(X).
\tag{3.5}
\]

Thus the full fields of a common-response witness hold with charge one and
zero endpoint error (or with every positive error if one wants the literal
constructor's `error>0` premise).

The rectangle atom at `S={o,m}` is exactly

\[
 [\Pr_Z(S)-\Pr_Y(S)]r_o(S)=1.
\tag{3.6}
\]

It is an observer-containing positive collision.  It also has the strict
reverse toggle

\[
 r_m(\{o,m\})=0<1=r_m(\{o\}),
\tag{3.7}
\]

so the mover gains by leaving the collision.

### 3.2 The positive normalized slope is genuine

Mix the mover's stopping law between `N` and the displayed `Q`, using target
weight `lambda`.  Keep the observer at `N`.  The observer's prescribed payoff
is zero.  Quitting at the displayed date gives `lambda`: collision payoff one
on the target branch and singleton payoff zero on the Never branch.  Every
other pure time and Never give zero.  Therefore

\[
 d_o(M_\lambda)=\lambda,
 \qquad
 \frac{d_o(M_\lambda)-d_o(X)}{\lambda}=1.
\tag{3.8}
\]

The source mover is active because

\[
 d_m(X)=d>0.
\]

Hence this is not merely an arbitrary four-law identity: it has the exact
positive active-mover/off-diagonal normalized slope which produces the
common-response square upstream.

One may put the displayed row at date `n` and take any `lambda_n -> 0`.
Terminal laws, semantic coordinates, square gain, atom, and all calculations
above remain unchanged while the chronological row escapes to infinity.

## 4. Strict fixed-law premium and inert cap stack

The endpoint response has semantic pair

\[
 U(Z)=(1,0),\qquad B(Z)=(1,1),\qquad D(Z)=1.
\tag{4.1}

Indeed the mover can Continue while the observer quits and receive one.

Fix the endpoint law
\(\mu=\delta_{\{o,m\}}\).  Every actual profile with this law has prescribed
payoff `(1,0)`.  The mover can choose Never and receive one when the observer
quits, so every such point has total debt at least one.  The same lower bound
passes to the joint semantic/law carrier by the corresponding pure-deviation
inequality.  Thus `Z` is a fixed-law observer-reset minimizer of value one.

The literal profile `Y` has semantic pair

\[
 U(Y)=B(Y)=(0,1),\qquad D(Y)=0,qquad d_o(Y)=0.
\tag{4.2}

Therefore the global observer-reset minimum has value zero, and the
fixed-law/global reset premium is exactly

\[
 D(Z)-D(Y)=1.
\tag{4.3}

Nevertheless `Z` has only the all-Continue exact cap root.  Let `p` be the
observer's Quit probability at an arbitrary product root.  Against the cap
vector `(1,1)`, the mover's endpoints are

\[
 Q_m=d(1-p),\qquad K_m=1.
\]

Since `d<1`, the mover strictly prefers Continue at every root.  Once the
mover Continues purely, the observer's endpoints are

\[
 Q_o=0,qquad K_o=1,
\]

so the observer also strictly prefers Continue.  Complementarity therefore
forces both Quit probabilities to zero in every exact cap-Nash root.

Consequently every finite or infinite exact cap stack based at `Z` is
literally constant, has cumulative absorption charge zero, preserves the
response square and paid/toggle data, and never enters the lower reset-face
sublevel.  The mover's fixed defect is exactly what blocks the collision row
from being a Bellman root.

## 5. Why this is not a counterexample to the maintained branch

The table has a zero-debt terminal profile `Y`; hence its global terminal
semantic minimum is zero and it has no
`QuittingTerminalExploitabilityWitness`.  It does not instantiate
`QuittingPositiveMinimumDebtTangentFamily` or refute any result conditional on
the counterexample witness.

It does instantiate every local ingredient which a proposed plateau proof
was using:

- active mover and positive off-diagonal normalized slope;
- the complete same-source common-response square;
- zero observer debt at the response endpoint;
- positive retained collision law and static terminal toggle;
- strict fixed-law/global reset premium; and
- unique all-Continue exact cap roots at the retained point.

Therefore a proof which uses the terminal witness only to say “the retained
atom has a strict toggle,” “the literal endpoint has some positive debtor,” or
“there is a paid row somewhere at this profile” cannot close the plateau.
Those local conclusions hold here: `Z` has mover debt one and the collision
toggle (3.7).  The genuine witness/global-minimum hypotheses must instead
produce a new **co-realized cap compatibility or regeneration statement**.

Constructing a realizable version with positive global minimum and a terminal
exploitability witness would already construct the counterexample which the
main conjecture asserts does not exist.  The present regression deliberately
stops at the sharp local interface.

### 5.1 What the genuine terminal witness adds at the literal endpoints

There is one exact same-source consequence, but it points away from terminal
Nashification.  Let `Gamma` be the witness gap and let `Z_n` be the actual
common-response endpoints with

\[
 d_o(Z_n)\longrightarrow0.
\]

At every `Z_n`, terminal exploitability selects a player `k_n` and a
behavioral deviation with gain at least `Gamma`.  By the definition of the
unrestricted cap,

\[
 d_{k_n}(Z_n)\ge\Gamma.
\tag{5.1}
\]

For all late `n`, `k_n` is not the observer.  Finiteness permits a subsequence
with one fixed `k != o`, and semantic convergence gives

\[
 d_k(\text{endpoint cluster})\ge\Gamma.
\tag{5.2}
\]

This is fully co-realized with the response square.  It still does not make
the reached rectangle row Nash-compatible: (5.1) is a whole-profile
best-response debt, and the profitable pure time supplied by extremality need
not be the rectangle time or the original mover action.  Nor does (5.2)
transfer to the fixed-law minimizer's `k` coordinate, since fixed-law
minimization preserves the law/prescribed payoff but may alter every cap other
than the reset observer's zero-debt coordinate.

Thus the terminal witness supplies a fixed non-observer debtor, not a reverse
best-response condition at the rectangle row.  A useful next theorem must
align that debtor's profitable time with the causal rectangle root or turn
its failure to align into regenerated minimum support descent.  Neither is a
current declaration.

## 6. The exact sufficient consumer

The positive rectangle orientation supplies a reached causal row with a
uniform absorption floor.  What is missing is its compatibility with the cap
vector of the fixed-law minimizer.

Let `f` be a retained reset point whose exact cap-Nash root is uniquely all
Continue.  Suppose there are product roots `q_n` such that

\[
  \liminf_n A(q_n)\ge a>0,
\tag{6.1}
\]

and their total fixed-cap Nash defect satisfies

\[
  \sum_i \rho_i(f.2,q_n)\longrightarrow0.
\tag{6.2}
\]

Compactness of the finite product simplex gives a subsequential limit `q`.
Continuity gives

\[
 A(q)\ge a,
 \qquad
 \rho_i(f.2,q)=0\quad\text{for every }i.
\]

Thus `q` is an exact cap-Nash root with positive absorption, contradicting
the unique-all-Continue plateau.  Equivalently, uniqueness and compactness
give a positive total-defect moat on every root with absorption at least `a`.

There is also a direct lower-face consumer.  Write

\[
 \delta=D(f)-D(g)>0
\]

for the fixed-law premium.  If the tail/current pair generated by `q` is
already certified as a punishment-floor admissible exact edge (in
particular, both its tail and prefixed value meet the floor), and the limit
root above has

\[
 A(q)\ge \frac{\delta}{2D(f)},
\tag{6.3}
\]

then the exact cap-prefix identity gives

\[
\begin{aligned}
 D(\operatorname{Prefix}(q,f))
   &=(1-A(q))D(f)\\
   &\le D(f)-\delta/2
    =D(g)+\delta/2.
\end{aligned}
\tag{6.4}
\]

This is precisely consumer (i): one exact floor-admissible prefix enters the
separated lower half with fixed charge.  A finite stack version replaces
(6.3) by the same cumulative absorption inequality.  No claim is made that
floor admissibility follows from `f.2` alone.

The full response square supplies neither (6.2) nor an admissible floor edge
at `f`.  More sharply, the rectangle row in the example has absorption one and
observer defect zero, but mover defect bounded away from zero.  Hence no
improvement of the existing atom-mass estimate can repair the producer.

## 7. Support descent and terminal-consumer audit

The square constrains one observer debt difference and one observer payoff
moment.  It places no sign restriction on the debt changes of players other
than the observer.  The reset transfer identity is aggregate and permits a
new previously inactive debtor.  Therefore the full square does not supply
the no-new-support premise needed by the checked minimum-fiber support-drop
re-extraction.  This leaves regimes I/X in
`CHATGPT_EXTERNAL__ALIGNED_RESET_MINIMUM_CLASSIFICATION.md` unchanged.

Likewise, observer endpoint debt tending to zero is not total terminal
approximate Nash.  The example has exactly one unit of mover debt at the
response endpoint.  The ambient terminal witness can always select another
debtor; it does not identify that debtor's profitable deviation with the
rectangle row or make the row cap-Nash.

Thus neither consumer (ii) nor (iii) follows from the restored square.  The
minimal additional hypotheses are now explicit:

1. for (i), fixed-cap Nash compatibility (6.2), plus the existing absorption
   floor and floor admissibility;
2. for (ii), minimum-fiber membership and no-new-positive-debt support at the
   reset point; or
3. for (iii), an all-player defect consumer on the same actual response
   profile, not merely the observer's vanishing debt.

These are alternatives, not fields currently implied by the rectangle
producer.

## 8. Conjecture-facing conclusion

Restoring the upstream curvature/response square does not consume the
maximal all-Continue plateau.  Its useful content is orthogonal to the
missing Bellman condition: it proves a positive observer cross-effect, while
the cap root requires simultaneous complementarity for every player against
the retained cap.

The next admissible producer test is therefore narrow:

> Can the genuine positive global minimum plus terminal exploitability
> witness force the reached positive rectangle row's **total defect against
> the fixed-law cap** to vanish, or else regenerate a lower minimum source
> with no new debtor?

Without one of those two consequences, the retained-square route is exhausted
at an exact interface separation.  Another terminal atom, static toggle, law
premium, or observer-only response estimate cannot change the conclusion.

## Review request

Please check the four-profile payoffs and unrestricted caps, the normalized
slope (3.8), the fixed-law minimum and premium (4.3), the unique-cap-root
calculation, and the compact consumer (6.1)--(6.4).  The highest-risk scope
claim is the exact boundary between the realizable local regression and the
uninstantiated positive-global-minimum/terminal-witness hypotheses.
