# Reset rigidity contracts to a zero-Never singleton minimum or an off-minimum paid port

Identity: PAIRED_HULL_REVIEW

Date: 2026-08-31

Status: **proved ordinary mathematics, conditional only on the reviewed
ordinary-mathematics inputs named below; not yet a checked Lean theorem.**
The positive-Never input has two independent reviews but is not an export.
The zero-Never/zero-singleton input is a composition of two reviewed exports.
The remaining zero-Never positive-singleton arm is not consumed here.

## 1. Exact question

Let \(I=\operatorname{Fin}4\), let \(r\) be a bounded quitting reward table,
and assume the hard-residual hypothesis coming from the absence of a uniform
equilibrium payoff. Let

\[
 z=((U,B),\mu)
\]

be the returned joint point of a reset-rigid chamber. Thus \(z\) belongs to
the joint terminal-semantic/law carrier,

\[
 D(U,B)=D_*>0
\]

is the global minimum of total unrestricted behavioral debt, and one reset
owner \(o\) has

\[
 d_o(U,B)=0.
\]

The question is whether the complete law itself narrows the reset-rigid
residual.

## 2. Contraction theorem

At least one of the following two output types can be selected.

### A. Actual off-minimum paid port

There is an actual behavioral profile \(\xi\) with

\[
 D(\operatorname{Sem}(\xi))>D_*,
\]

together with the retained global minimum, an actual complete behavioral
response of fixed positive gain, and literal first-disagreement or
late-release ancestry from the supplied minimum source. Hence \(\xi\) is an
input to the existing actual off-minimum paid-cap problem.

### B. Zero-Never positive-singleton minimum source

There are a joint carrier point

\[
 y=((U',B'),\nu),
 \qquad D(U',B')=D_*,
\]

a player \(j\), and a number \(\lambda>0\), such that

\[
 \nu(\mathsf{Never})=0,
 \qquad
 \nu(\{j\})\geq\lambda.
\tag{2.1}
\]

Moreover \(y\) has a source-faithful minimum-singleton chronology: actual
profiles converging jointly to \(y\), fresh exact cap--Nash root words of
arbitrary depth over those same profiles, and a shifted literal singleton
stage with a fixed positive mass floor. Thus it enters the maintained
minimum-singleton clock-compression/forced-pair route without changing the
limiting semantic point or law. Individual finite prefixes need not preserve
the semantic pair or law exactly.

Consequently a recurrent reset-rigid component cannot use either

\[
 \mu(\mathsf{Never})>0
\]

or

\[
 \mu(\mathsf{Never})=0,
 \qquad
 \mu(\{i\})=0\quad(i\in I)
\]

as its final law-support obstruction. The only law-support pattern still
capable of recurring without first visiting the off-minimum paid problem is

\[
 \boxed{
 \mu(\mathsf{Never})=0
 \quad\text{and}\quad
 \mu(\{j\})>0\text{ for some }j.}
\tag{2.2}
\]

This is a contraction of the reset-rigid chamber, not a terminal consumer of
(2.2).

## 3. Zero Never and zero singleton mass

Assume

\[
 \mu(\mathsf{Never})=0,
 \qquad
 \mu(\{i\})=0\quad(i\in I).
\tag{3.1}
\]

The reviewed closed-law product-base theorem in
[`ZERO_SINGLETON_BEHAVIORAL_LAW_PRODUCT_BASE_AND_SURE_CORE_DESCENT.md`](../formalized/ZERO_SINGLETON_BEHAVIORAL_LAW_PRODUCT_BASE_AND_SURE_CORE_DESCENT.md)
constructs a product root \(q\) with at least two sure quitters whose
root-then-Never profile \(\rho(q)\) realizes the **same** semantic pair and
the **same** law:

\[
 \operatorname{Sem}(\rho(q))=(U,B),
 \qquad
 \mathcal L(\rho(q))=\mu.
\tag{3.2}
\]

The strict singleton moat at a positive global minimum removes the otherwise
necessary all-Continue padding before the product root. Every stopping law in
\(\rho(q)\) is supported on \(\{0,\infty\}\), so this is an actual
finite-clock positive global minimum.

The reviewed finite-clock theorem
The formalized
PURE_FINITE_CLOCK_MINIMUM_DEADLINE_RANK_TO_PAID_PORT.md now applies directly.
It gives finitely many literal unilateral replacements ending at an actual
profile \(\xi\) with

\[
 D(\operatorname{Sem}(\xi))>D_*,
\]

and an unrestricted pure-time or Never response of gain \(>D_*/4\), with a
literal first disagreement. This is Output A.

No reset-specific inequality is used in this arm. Its significance is that
the zero/zero law face is not a reset-rigid terminal component at all.

## 4. Positive Never mass

Put

\[
 q=\mu(\mathsf{Never})>0.
\]

The twice-reviewed positive-Never late-release theorem in
CODEX_MINER__FIN4_POSITIVE_NEVER_LATE_RELEASE_CHRONOLOGY.md supplies, after
one common subsequence, actual profiles \(P_n,Q_n\), a fixed player \(a\),
and a constant

\[
 g_0=\Gamma q/4>0
\]

with the following properties.

1. \(P_n\) contains an arbitrarily deep exact cap--Nash source prefix and
   converges semantically and in terminal law to \(z\).
2. \(Q_n\) differs from \(P_n\) only in player \(a\)'s complete behavioral
   strategy.
3. The change is a legal late finite release and

   \[
   U_a(Q_n)-U_a(P_n)\geq g_0,
   \qquad
   d_a(Q_n)=d_a(P_n)-
       \bigl(U_a(Q_n)-U_a(P_n)\bigr).
   \tag{4.1}
   \]
4. Every \(Q_n\) terminates surely, so

   \[
   \mathcal L(Q_n)(\mathsf{Never})=0.
   \tag{4.2}
   \]
5. At the late release date, \(Q_n\) has a literal singleton-\(a\) atom of
   mass at least \(q/4\).

Compactify the full target semantic pairs and their finite terminal laws
along one subsequence:

\[
 \bigl(\operatorname{Sem}(Q_n),\mathcal L(Q_n)\bigr)
 \longrightarrow
 y=((U',B'),\nu).
\tag{4.3}
\]

The topology is ordinary coordinatewise convergence: the semantic packet is
finite dimensional and the outcome space has \(16\) coordinates, so law
convergence is equivalent to total-variation convergence. Equations (4.2)
and the singleton floor give

\[
 \nu(\mathsf{Never})=0,
 \qquad
 \nu(\{a\})\geq q/4.
\tag{4.4}
\]

Carrier closedness gives \(D(U',B')\geq D_*\).

If \(D(U',B')>D_*\), then eventually the actual targets \(Q_n\) are bounded
away from the minimum fibre. Each is source-attached to \(P_n\) by the
fixed-gain legal response (4.1), and the terminal gap also constructs the
standard actual paid-cap port at \(Q_n\). Selecting one late index gives
Output A.

If \(D(U',B')=D_*\), then (4.4) gives the joint point in Output B. The
promised literal source chronology can be built without reselecting an
unrelated realizer. Use these same \(Q_n\) as suffixes, and over each \(Q_n\)
choose a fresh exact cap--Nash root word \(R_n\) of length \(n+1\). Exact
debt scaling and global minimality give

\[
 D_*\leq
 D(R_n\mathbin\triangleright Q_n)
 \leq D(Q_n)\longrightarrow D_*.
\tag{4.5}
\]

Since \(D_*>0\), the Continue product of \(R_n\) tends to one. The literal
singleton atom of \(Q_n\) therefore survives after shifting by
\(|R_n|\), with, for example, eventual mass at least \(q/8\). This is the
first half of the source-faithful minimum-singleton chronology claimed in B.

For completeness, it remains to verify that the fresh words do not change
the **limiting** joint semantic/law point.  Write \(a_{n,t}\) for the
absorption probability of row \(t\) of \(R_n\), and write

\[
 c_n=\prod_{t<|R_n|}(1-a_{n,t})\longrightarrow1.
\]

Then

\[
 \sum_{t<|R_n|}a_{n,t}
 \leq -\log c_n
 \longrightarrow0.
\tag{4.6}
\]

Thus the prescribed probability of absorption inside the fresh word tends
to zero.  For a fixed player \(i\), even after an arbitrary complete
behavioral replacement by \(i\), the probability that an opponent absorbs
inside the word is bounded by the same sum: at every row, the product-root
probability that some opponent Quits is at most the prescribed probability
that somebody Quits, namely \(a_{n,t}\).  Hence the literal coupling gives

\[
 d_{\mathrm{TV}}
 \bigl(\mathcal L(R_n\triangleright Q_n),\mathcal L(Q_n)\bigr)
 \longrightarrow0,
\tag{4.7}
\]

convergence of every prescribed payoff coordinate, and convergence of every
player-deleted opponent law after the fresh word: only the unchanged
opponents must survive the word before the two suffix environments can
differ.

Cap convergence uses the exact root-stack account, rather than silently
identifying every pre-word response with a response at the suffix.  Coordinate
debt scales exactly through the cap--Nash word:

\[
 d_i(R_n\triangleright Q_n)=c_n d_i(Q_n).
\]

If rewards are bounded by \(M\), the prescribed-payoff coupling and
\(0\leq d_i\leq2M\) give

\[
 \left|B_i(R_n\triangleright Q_n)-B_i(Q_n)\right|
 \leq 4M(1-c_n)
 \longrightarrow0.
\]

Thus the whole unrestricted cap vector converges; no finite response menu or
cap-attainment claim is used.  Therefore

\[
 \bigl(\operatorname{Sem}(R_n\triangleright Q_n),
        \mathcal L(R_n\triangleright Q_n)\bigr)
 \longrightarrow y.
\tag{4.8}
\]

The shifted singleton coordinate still has the eventual \(q/8\) floor.  The
original minimum source \(P_n\), the late-release edge \(P_n\to Q_n\), and
the fresh child prefix \(R_n\triangleright Q_n\) are all retained in one
ancestry record.  The limit point and law are unchanged; no assertion is
made that any finite prefixed profile has exactly the same semantic pair or
law as \(Q_n\).

Thus positive Never mass itself has been eliminated: it either pays for an
off-minimum exit or is converted by one actual behavioral update into zero
Never mass and positive singleton mass.

## 5. A useful debt restriction in the positive-Never arm

The finite-support late-release calculation gives more than the selected
player \(a\). Let

\[
 s_i=r_i(\{i\}).
\]

For every player \(i\), apply the same finite-support compression to a joint
realizing sequence for \(z\), and cap only \(i\)'s clock strictly after all
of its finite support. The exact payoff difference is \(q_n s_i\), where
\(q_n\to q\) is the source joint-Never mass. Since this is one admissible
behavioral response,

\[
 \boxed{d_i(U,B)\geq q\,(s_i)_+.}
\tag{5.1}
\]

In particular, the zero-debt reset owner obeys

\[
 q>0,\quad d_o(U,B)=0
 \quad\Longrightarrow\quad
 s_o\leq0.
\tag{5.2}
\]

The terminal exploitability witness supplies some \(a\) with
\(s_a\geq\Gamma>0\). Hence \(a\ne o\) and

\[
 d_a(U,B)\geq q\Gamma.
\tag{5.3}
\]

These inequalities are genuine extra restrictions on a positive-Never reset
point. They are not themselves a terminal consumer.

## 6. Positive singleton mass with zero Never mass

It remains to consider

\[
 \mu(\mathsf{Never})=0,
 \qquad
 \mu(\{j\})>0
\tag{6.1}
\]

at a global minimum. This arm is **not already consumed**.

The checked minimum-singleton clock compression gives a literal cofinal row
of fixed singleton mass. The reviewed forced-pair normal form then uses the
hard residual's singleton collision gap to produce, on the same retained
source:

- a pure pair of fixed stage mass;
- a minimum-tail cluster;
- a fixed all-behavior endpoint gain;
- exact subtraction from the mover's own debt; and
- the collision-minimum residual rather than the strategic-singleton arm.

What it does not control is the change of the other three unrestricted caps.
The pureification step feeding the pair is also a same-date source sibling,
not a forward Nash--Bellman transition. Accordingly (6.1) currently enters
the concentrated-collision/minimum-return waist; it does not yield terminal
approximants, a charged return, or a renewable rank.

The exact remaining law-support obstruction is therefore not generic reset
rigidity. It is:

> a source-attached zero-Never positive-singleton global minimum whose
> owner-compressed forced pair has a minimum semantic tail and a fixed paid
> endpoint, but whose cross-coordinate cap leakage prevents a return or
> zero-set descent.

If the law-tight two-chamber classifier is rerun from such a point, every
same-law reset output still has zero Never mass and retains the positive
singleton coordinate. Thus positive Never cannot reappear inside that
same-law reset loop. A later law-changing operation must be recorded
explicitly; it cannot be hidden as a reset.

## 7. Source and chronology boundaries

1. The zero/zero branch constructs a new exact product realization of the
   same joint point. It does not preserve an earlier calendar, but it does
   preserve the exact semantic pair and law and is sufficient for the actual
   finite-clock paid-port interface.
2. In the positive-Never branch, \(P_n\to Q_n\) is one actual unilateral
   update. The source root word is exact only for \(P_n\), not for \(Q_n\).
   Fresh roots are chosen over \(Q_n\) only after the minimum-target branch
   is known.
3. The singleton atom in \(Q_n\) is a literal late stage, not current
   absorption of an earlier exact root.
4. Output B does not assert that its marked forced-pair edge is a temporal
   Nash--Bellman edge.
5. Neither output consumes the actual off-minimum paid port or the remaining
   zero-Never singleton collision residual.

## 8. Inputs and novelty boundary

Reviewed ordinary-mathematics inputs:

- formalized/ZERO_SINGLETON_BEHAVIORAL_LAW_PRODUCT_BASE_AND_SURE_CORE_DESCENT.md;
- formalized/PURE_FINITE_CLOCK_MINIMUM_DEADLINE_RANK_TO_PAID_PORT.md; and
- notes/CODEX_MINER__FIN4_POSITIVE_NEVER_LATE_RELEASE_CHRONOLOGY.md, with
  the independent reviews by CODEX_RAMSEY and CODEX_EULER.

Checked ingredients used inside those proofs include the global singleton
margin, finite-support quantile-clock compression, exact cap--Nash root-stack
debt scaling, minimum-reference opponent transfer, and point-specific Fin4
minimum-law finite-atom causalization.

The new content here is the exhaustive law split at a reset-rigid minimum,
compactification of the positive-Never release targets, source-faithful fresh
prefixing on the minimum-target arm, and the conclusion that only (2.2) can
remain as a reset-law support obstruction. No claim is made that (2.2) or
the off-minimum paid port is solved.

## 9. Next question

Can the zero-Never condition be used in the forced-pair/minimum-tail residual
to control the compensating cap leakage of the other three players, yielding
either an off-minimum paid exit or a same-law return which preserves every
existing zero-debt coordinate?

Without such a theorem, positive singleton mass is an entrance to the known
waist, not a consumer.
