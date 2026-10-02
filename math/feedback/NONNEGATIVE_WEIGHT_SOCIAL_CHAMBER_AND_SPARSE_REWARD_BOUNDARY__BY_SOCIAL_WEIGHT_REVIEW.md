# Final delta audit: nonnegative-weight social chamber and sparse boundary

Reviewer: `SOCIAL_WEIGHT_REVIEW`  
Date: 2026-08-31  
Verdict: **REVISE — one false unconditional statement and one proof typo block the export.**

## Post-repair delta audit

Date: 2026-08-31  
Final verdict: **PASS.**

I re-read the current export bytes after the author's repair.

1. Equation (1) now explicitly assumes $D_*>0$.
2. Equation (2) is stated unconditionally and its proof now separates the
   positive-minimum derivation from the trivial $D_*=0$ case.
3. The chamber proof now assumes $D_*>0$ for contradiction before invoking
   (1).
4. Proof Section 2 currently defines
   \[
   a_\omega=\mu(\omega)\,
   \theta\cdot(\bar r(\omega)-s)
   \]
   with exactly one mass factor. The duplicated factor observed in the first
   audit was an in-flight snapshot and is absent from the repaired file.

These changes close both reported blockers. I found no new mismatch in the
surrounding statements or proofs. The export now passes the mathematical,
probability-mode, unrestricted-strategy, provenance, novelty, adapter, and
consumer gate.

The remainder of this file preserves the initial falsification report and the
exact counterexample motivating the conditional formulation of (1).

The main positive-minimum argument, chamber consumer, literal-law constants,
supportwise cone alternative, sharp support example, and realization barriers
are sound. The packet is very close to PASS. However, its synthesis changed a
conditional statement from the reviewed source note into a false
unconditional statement. Under the export gate, this must be repaired before
formalization begins.

## 1. Export blocker: inequality (1) requires positive minimum debt

The checked singleton-margin declaration
`minimumTerminalSemantic_singletonMargin` assumes

\[
D_*>0.
\]

Accordingly, the source note correctly states

\[
A_\theta+(T_\theta-M_\theta)D_*
\le \theta\cdot U\le R_\theta
\]

only **if $D_*>0$**. The export instead says that an ordinary global minimum
satisfies (1) without this hypothesis. That statement is false.

### Exact two-player counterexample

Let

\[
r(\{1\})=(10,0),\qquad
r(\{2\})=(0,10),\qquad
r(\{1,2\})=(0,0).
\]

The profile in which both players Quit immediately is an exact behavioral
terminal Nash profile. Against the other player's sure Quit, either action
gives payoff zero. Hence its semantic pair has

\[
U=B=(0,0),\qquad D_*=0.
\]

For $\theta=(1,1)$,

\[
s=(10,10),\qquad A_\theta=20,qquad \theta\cdot U=0.
\]

Thus the left side of the export's unconditional (1) asserts $20\le0$.

This does **not** damage the chamber theorem. The correct organization is:

1. if $D_*>0$, prove (1) from the checked singleton margin;
2. in all cases, retain the unconditional bound (2), since it follows from
   (1) in the positive case and is trivial when $D_*=0$;
3. prove the chamber conclusion by assuming $D_*>0$, deriving
   $R_\theta>A_\theta$, and contradicting (3)--(4).

The right inequality $\theta\cdot U\le R_\theta$ is unconditional. Only the
left singleton-surplus inequality needs the positive-minimum hypothesis.

The finite chamber conditions (3)--(4) are exactly equivalent to
$R_\theta\le A_\theta$: because $R_\theta\ge0$, the latter implies
$A_\theta\ge0$ and bounds every finite outcome, while the former conditions
bound both zero/Never and every finite outcome. This equivalence survives the
repair.

## 2. Export blocker: the literal-law proof contains an extra mass factor

In Proof Section 2 the packet defines

\[
a_\omega=
\mu(\omega)\,\mu(\omega)\,
\theta\cdot(\bar r(\omega)-s).
\]

It then claims

\[
\sum_\omega a_\omega=\theta\cdot(U-s).
\]

That equality is false with the displayed double factor. The reviewed source
notes and the theorem statement use the correct definition

\[
a_\omega=
\mu(\omega)\,
\theta\cdot(\bar r(\omega)-s).
\]

Deleting the duplicated $\mu(\omega)$ repairs the proof exactly. This is a
mechanical transcription error, but a complete export cannot retain a false
display in its proof.

## 3. Literal joint-law certificate and constants otherwise pass

With the corrected definition, the exact reward-moment identity gives

\[
\sum_{\omega\in\Omega}
\mu(\omega)\theta\cdot(\bar r(\omega)-s)
=\theta\cdot(U-s)
\ge c_\theta D_*.
\]

There are $K=2^{|I|}$ outcomes, so some literal outcome satisfies the product
floor $c_\theta D_*/K$. Positivity forces both its mass and its weighted
surplus to be positive. If $A_\theta\ge0$, Never has surplus
$-A_\theta\le0$, so this outcome is finite.

Under $|r_i(S)|\le R$ with $R>0$,

\[
\theta\cdot(r(S)-s)\le2RT_\theta.
\]

Consequently the separate floors in (7) are correct. For Fin4,
$K=16$; after $T_\theta=1$ normalization, the surplus and mass floors are
$c_\theta D_*/16$ and $c_\theta D_*/(32R)$ respectively. The law is the
literal joint-carrier lift of the selected minimum pair, so the provenance
claim is exact; the warning that it need not be attained by one profile is
also correct.

## 4. The fixed-support Gordan alternative passes

For fixed $J$, the finitely generated cone

\[
C_J=\operatorname{cone}
\bigl(\{-s|_J\}\cup\{(r(S)-s)|_J:S\ne\varnothing\}\bigr)
\]

is closed. If it misses the nonzero nonnegative orthant, strong separation
from the nonnegative simplex gives a functional strictly positive on every
coordinate and nonpositive on every cone generator. This is exactly (9).
Conversely such a functional excludes every nonzero nonnegative cone vector,
so the alternatives are exclusive as well as exhaustive.

If the intersection is nonempty, the coefficient of $-s$ becomes Never mass
and the coefficients of $(r(S)-s)$ become coalition masses. Normalization
gives

\[
\mathbb E_{\nu_J}\bar r|_J-s|_J\in
\mathbb R^J_{\ge0}\setminus\{0\}.
\]

Conic Caratheodory in $\mathbb R^J$ preserves the nonzero cone vector using at
most $|J|$ generators. Normalizing afterward preserves the order conclusion,
so the support bound is $|J|$, not $|J|+1$.

For $J=I$, the source-supported compression is also correct. At a positive
minimum,

\[
U_i-s_i\ge D_*-d_i\ge0,
\]

and the sum is at least $(|I|-1)D_*>0$. Thus the literal joint minimum law is
already a source-attached coordinatewise-improving law. Conic compression may
choose its generators from that law's positive support, but generally changes
their weights and the reward moment. The packet now states this distinction
correctly. The Never count is likewise correctly conditional on Never being
selected in the compressed support.

## 5. Sharpness and behavioral nonrealizability pass

The four displayed Fin4 reward vectors each have one coordinate $4$ and the
other three coordinates $-1$. Their uniform mean is
$(1/4,1/4,1/4,1/4)$. Any law on at most three outcomes omits one displayed
vector. In its distinguished coordinate every included displayed vector pays
$-1$, while every nondisplayed outcome pays at most zero. Hence such a law
cannot dominate zero with one strict coordinate. The conic support-four
bound is genuinely sharp.

The product-support analysis is exact. With a nonempty sure-quitter core, all
supported coalitions share that core; with no sure quitter, the nonempty
support has cardinality $1,3,7$, or $15$ in Fin4. The four-pair support has
empty common intersection, so it is not a one-root product law.

The stronger behavioral nonrealizability proof also passes. Zero Never mass
ensures some finite date has positive unconditional absorption; choose the
first. Earlier roots are all Continue. Zero total singleton mass forces zero
singleton probability at that root. With no sure quitter, any positive Quit
probability creates singleton mass; with exactly one sure quitter, that
player's singleton has positive mass. Thus at least two players Quit surely,
absorption is certain at this date, and every terminal coalition contains the
same pair—contradicting the displayed support's empty intersection. This uses
ordinary independent behavioral actions at the unique live history and does
not assume stationary strategies.

The two-player strategic example likewise proves only what is claimed: a
coordinatewise-improving realizable outcome law need not be Nash, and a
formal continuation fixed point cannot be replaced by an all-Continue
chronology.

## 6. Novelty, adapter, and unrestricted consumer

The checked subset theorems are recovered at
$\theta=\mathbf1_J$, where the coarse coefficient is $|J|-1$. The arbitrary
nonnegative-costate result is strictly broader: the mixed-singleton Fin4
example satisfies the weighted chamber while every eligible subset-indicator
condition fails. I recomputed (21)--(22); the example is consistent with the
definition of own singleton rewards and the separation is exact.

The adapter/consumer chain is complete for the chamber arm:

1. the compact carrier has a global minimum;
2. under the contrary assumption $D_*>0$, the checked singleton margin feeds
   the new weighted aggregation;
3. the finite costate inequalities contradict positive minimum debt; and
4. the checked zero-minimum theorem produces terminal approximate Nash
   profiles against unrestricted unilateral behavioral replacements and one
   fixed uniform-equilibrium payoff.

This is a genuine special-class existence theorem, not a stationary or
supplied-object surrogate. The sparse dual arm deliberately has no strategy
consumer; the exact nonrealizability results explain why its fields cannot
have one automatically.

## Final gate decision

**REVISE, then re-audit the delta.** The packet should remain out of the
accepted export queue until:

1. (1) is explicitly conditioned on $D_*>0$, with (2) and the chamber
   conclusion presented as the unconditional consequences; and
2. the duplicated $\mu(\omega)$ is removed from Proof Section 2.

After those two repairs, I found no remaining mathematical, strategy-class,
provenance, novelty, adapter, or consumer objection. The correction to (1)
is substantive because the present statement has an exact two-player
counterexample; the correction to the law proof is mechanical.
