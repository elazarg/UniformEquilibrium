# Review of `gpt/PAIR.md`

Reviewer: `PAIRED_HULL_REVIEW`

## Verdict

**PASS as a normalized local strengthening; not a source adapter and not a
consumer.**

Most of the response duplicates the checked/local oriented-pair compiler in
[`PAIRED_HULL_REVIEW__ORIENTED_PAIR_TO_SINGLETON_OR_RENEWABLE_CHORD.md`](../notes/PAIRED_HULL_REVIEW__ORIENTED_PAIR_TO_SINGLETON_OR_RENEWABLE_CHORD.md).
There is, however, one genuine additional corollary: the quantitative
old-member leave from the joined triple does not require that triple itself to
remain on the minimum fibre.

## Duplicated content

For the normalized profile in which the pair \(P=\{a,b\}\) Quits surely at
date zero and everyone else plays Never, the following are already the local
oriented-pair calculation:

1. unrestricted behavioral caps reduce to the two endpoint values because a
   sure opponent quitter screens every unilateral response at date zero;
2. the incoming strict dropout makes the incoming outsider \(x\) debt-free;
3. if neither pair member profits by leaving, the other outsider \(y\) is the
   unique debtor at a minimum pair and joins with gain exactly \(D_*\);
4. the join is a literal full-profile horizontal response but cannot be an
   exact Nash--Bellman predecessor, since its one-stage defect is the positive
   reward difference independently of the proposed continuation value; and
5. if the joined triple is also minimum, cap convexity and global minimality
   make the whole response chord coordinatewise affine and leave positive
   debt support contained in the two old pair members.

In that last minimum-target branch, selecting a debtor among the two old
members already gives a triple-to-pair leave of gain at least \(D_*/2\).
Thus the response's \(D_*/2\) statement is not new when both endpoints are
minimum.

## Genuine additional statement

Section 2 proves a slightly stronger fact without assuming that the joined
triple \(P\cup\{y\}\) is minimum. Let \(\pi_\theta\) mix only \(y\)'s date-zero
action between staying out and joining. For each old member \(i\in P\), write

\[
 A_i=r_i(P\setminus\{i\})-r_i(P)\leq 0,
 \qquad
 C_i=r_i((P\setminus\{i\})\cup\{y\})-r_i(P\cup\{y\}).
\]

Exact screening gives

\[
 d_i(\pi_\theta)=[(1-\theta)A_i+\theta C_i]_+,
 \qquad
 d_y(\pi_\theta)=(1-\theta)D_*.
\]

The incoming outsider \(x\) remains debt-free for all sufficiently small
\(\theta>0\), because its endpoint difference is affine and strictly negative
at \(\theta=0\). Global minimality then yields

\[
 \sum_{i\in P}[(1-\theta)A_i+\theta C_i]_+\geq\theta D_*.
\]

After division by \(\theta\) and passage to \(0+\), the terms with \(A_i<0\)
vanish, so

\[
 \sum_{i\in P:A_i=0}[C_i]_+\geq D_*.
\]

Because \(P\) has two members, some old member was exactly leave-indifferent
at the pair and has a complete leave response from the joined triple of gain
at least \(D_*/2\). This proof is correct and the complete-response claim is
valid: another sure date-zero quitter remains after that member leaves.

The result is therefore a literal two-edge normalized square even when the
first target is off minimum:

\[
 P\xrightarrow[y\text{ joins}]{D_*}P\cup\{y\}
 \xrightarrow[i\text{ leaves}]{\geq D_*/2}
 (P\setminus\{i\})\cup\{y\}.
\]

I did not find this off-minimum-target derivative statement in the corrected
oriented-pair note. The existing pure-toggle promotion packets give a
qualitative old-member-leave alternative, while the minimum-triple note gives
the \(D_*/2\) floor only when the triple is itself a global minimum.

## Boundary and relevance

The response correctly stops short of a closure theorem:

- its input remains the normalized mass-one, date-zero, Never-tail pair;
- it does not transport the calculation to an actual screened endpoint with
  arbitrary earlier absorption or an arbitrary retained tail;
- the second pair is not shown to be minimum;
- neither horizontal edge is thereby a punishment-floor-admissible temporal
  edge; and
- no renewable rank follows from the square.

Consequently this does not repair the withdrawn actual-source adapter and does
not answer the source-faithful oriented-pair question. Its new value is a
useful local strengthening of the off-minimum paid-port passport: after the
forced outsider join, one old member has a uniformly paid literal response.
That may be worth retaining in notes, but by itself it is not a new export or
a terminal consumer.
