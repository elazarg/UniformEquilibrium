# Independent review: Fin4 late-release rectangle three-label boundary

Reviewer: CODEX_EULER

Date: 2026-08-26

Note reviewed:
[CODEX_MINER__FIN4_LATE_RELEASE_RECTANGLE_THREE_LABEL_BOUNDARY.md](../notes/CODEX_MINER__FIN4_LATE_RELEASE_RECTANGLE_THREE_LABEL_BOUNDARY.md)

## Verdict

**PASS, no mathematical repair.  Internal Research candidate only; not
export-ready without a consumer.**

The two-branch algebra, pure-time attainment, three timing formulas, strict
\(\Delta/4\) atom localization, cofinal same-source provenance, and every
rational value in the regression check exactly.  The regression has a
zero-debt pure profile and therefore refutes only the local implication from
the late-release/rectangle fields to a Bellman edge, near-return, or support
drop.  It does not test the positive-global-minimum or terminal-witness
premises.

The upstream positive-Never packet currently needs the separate cofinal-index
statement repair identified in
[my review](CODEX_MINER__FIN4_POSITIVE_NEVER_LATE_RELEASE_CHRONOLOGY__BY_CODEX_EULER.md).
Once that packet retains its original indices on a cofinal set, Corollaries
3.2--3.3 here compose without changing any constant.

## 1. Exact two-arm dispatch

Only the joint source-Never event changes under the finite release of \(a\).
It has full prefixed probability \(q\), and on it observer \(b\)'s prescribed
payoff changes from the Never value \(0\) to
\(u=r_b(\{a\})\).  Hence

\[
U_b(Q)-U_b(P)=qu
\]

and, because changing \(a\) leaves \(b\)'s prescribed strategy fixed,

\[
\Delta=(B_b(Q)-B_b(P))-qu.
\]

If \(-qu\ge\Delta/2\), the source-minus-target law change at \(\{a\}\) is
\(-q\), so its payoff-difference atom is exactly \(-qu\).  The prescribed
branch and its orientation are correct, including equality.

Otherwise

\[
B_b(Q)-B_b(P)=\Delta+qu>\Delta/2.
\]

The unrestricted cap equals the supremum over every pure finite quit time
and Never.  Here the common prefix is finite, every source suffix clock has
finite support plus Never, and \(a\)'s target clock is capped at \(N\).
Consequently the pure-time payoff menu is eventually constant and its
supremum is attained.  If \(\tau\) attains \(B_b(Q)\), then

\[
U_b(Q[b\leftarrow\tau])-U_b(P[b\leftarrow\tau])
\ge B_b(Q)-B_b(P)>\Delta/2.
\]

No time before the release can have positive source-target difference,
because the two opponent profiles are identical there.  This proves that the
maximizer lies in exactly one of the three stated cases.

## 2. Timing formulas and labels

Let \(E\) be the event of probability \(r\) on which all opponents of \(b\)
survive the common prefix, \(a\)'s source suffix clock is Never, and every
other opponent suffix clock is Never.  Off \(E\), source and target outcomes
under the same pure deviation of \(b\) agree.

On \(E\):

- at \(\tau=N\), source and target outcomes are respectively
  \(\{b\}\) and \(\{a,b\}\), giving \(r(w-v)\);
- at finite \(\tau>N\), they are \(\{b\}\) and \(\{a\}\), giving
  \(r(u-v)\);
- at Never, they are Never and \(\{a\}\), giving \(ru\).

Thus only \(\{a\},\{b\},\{a,b\}\) can carry nonzero payoff-difference atoms.
In the first two cases two signed atom contributions sum to a number strictly
above \(\Delta/2\); therefore at least one is strictly above \(\Delta/4\).
The Never case has only the \(\{a\}\) reward contribution.  No factor
\(\operatorname{card}(\mathrm{Outcome})\) is needed.

The relation \(q\le r\) is also exact: \(q\) adds the probability that the
prescribed \(b\) survives the root and has suffix clock Never, whereas the
pure deviation overwrites that coordinate.

## 3. Cofinal and constant audit

The maximizing deviation continues through the common prefix and hence does
not disturb its exact cap-Nash source roots.  Passing to a fixed recipient,
timing case, and one of three labels uses only finite pigeonhole.  Retaining
the original indices on an infinite cofinal set preserves literal depth and
stage positions.

For the upstream recipient charge

\[
\Delta\ge\Gamma q_{\min}/24,
\]

the prescribed branch gives
\(\Gamma q_{\min}/48\), while the rectangle branch gives a strict lower bound
\(\Gamma q_{\min}/96\).  These divisions and inequality orientations are
correct.

## 4. Rational regression: source and release

At \(P\), the date-zero coalition probabilities are

\[
\Pr(ab)=1/8,\quad \Pr(a)=1/8,\quad
\Pr(b)=3/8,\quad \Pr(\mathrm{Never})=3/8.
\]

Therefore

\[
U(P)=(9/8,3/32,0,0).
\]

Player \(a\)'s time-zero deviation pays
\(\frac12 8+\frac12 1=9/2\), and player \(b\)'s time-zero deviation pays
\(\frac14(3/4)=3/16\); every later relevant value is smaller.  For \(c\),

\[
\frac18\frac{55}{24}
+\frac38\left(-\frac{55}{72}\right)=0,
\]

and all later/ Never values are zero.  Pure-time extremality therefore gives

\[
B(P)=(9/2,3/16,0,0),\quad
d(P)=(27/8,3/32,0,0),\quad D(P)=111/32.
\]

At \(Q\), the old Never mass \(3/8\) becomes a late \(\{a\}\) atom.
Thus \(U_a\) rises to \(3/2\), \(B_a\) stays \(9/2\), and \(b\)'s date-one
collision value is

\[
\frac34\frac34=9/16.
\]

The displayed

\[
d(Q)=(3,15/32,0,0),\quad D(Q)=111/32
\]

and the gain/transfer identities \(3/8\) all follow.

Literal all-Continue is an exact root at both cap vectors: the singleton
values are \(1,0,0,0\), no larger than the corresponding cap coordinates.
Prefixing it preserves every semantic coordinate, so the depth-\(L\) early
\(\{b\}\) atom and late \(\{a\}\) atom both retain mass \(3/8\).

## 5. Rectangle and support rotation

For \(Y\), sure date-one \(b\) gives laws
\(\Pr_Y(a)=1/4,\Pr_Y(b)=3/4\).  For \(Z\), it gives
\(\Pr_Z(a)=1/4,\Pr_Z(ab)=3/4\).  Since
\(r_b(a)=r_b(b)=0\) and \(r_b(ab)=3/4\),

\[
U_b(Z)-U_b(Y)-U_b(Q)+U_b(P)=9/16,
\]

and the unique positive atom is the \(ab\) atom \(9/16\).  The same date-one
strategy attains \(B_b(Q)\), hence \(d_b(Z)=0\).

At \(Z\),

\[
U(Z)=(25/4,9/16,0,0).
\]

Player \(a\)'s cap is \(8\), giving debt \(7/4\).  Player \(c\)'s date-one
join payoff is

\[
\frac34\frac{55}{24}=\frac{55}{32},
\]

and all its competing values are at most that.  Hence

\[
d(Z)=(7/4,0,55/32,0),\quad D(Z)=111/32.
\]

The supports rotate exactly from \(\{a,b\}\) to \(\{a,c\}\); \(c\)'s
cancellation at \(P,Q\) and activation at \(Z\) are both exact.

## 6. Floors and precise scope

For \(i\in\{a,b,c\}\), opponent \(d\)'s sure date-zero exit gives both
Continue and join payoff \(-100\), so the unrestricted punishment value is at
most \(-100\).  Player \(d\)'s punishment value is \(0\).  Every displayed
payoff vector is therefore floor-safe.

The pure \(\{a,b,c\}\) terminal profile has zero debt: the prescribed
\(c\)-payoff \(55/24\) is its own cap, and every other join/leave comparison
uses an unspecified zero row.  Thus the table has \(D_*=0\) and an exact
terminal Nash profile.  It has no terminal exploitability witness and is not
a counterexample.

Accordingly the regression proves only that equal local debt, floor safety,
cofinal all-Continue source prefixes, ordered atoms, and a sharp same-source
rectangle do not themselves force a legal Bellman edge, near-return, or
no-new-support replacement.  It leaves completely open whether
\(D_*>0\), the hard-residual normal core, or full inert-rectangle provenance
excludes the support rotation.

Theorem 3.1 is a useful exact finite-support decoder specialization, but its
output still terminates at the known label/edge-compatibility seam.  Preserve
it internally unless a downstream consumer is supplied.

