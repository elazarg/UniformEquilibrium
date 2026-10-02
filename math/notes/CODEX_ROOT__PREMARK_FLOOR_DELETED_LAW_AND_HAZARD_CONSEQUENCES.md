# Deleted-law consequences of a pre-mark cap floor

Status: proved consequences of the pre-mark absorption inequality. They apply
to arbitrary actual behavioral profiles. They do not assert that the
pre-mark roots are exact Nash--Bellman roots.

## Setup

Let \(I\) be finite, let rewards have absolute value at most \(M\), and let
\(\pi\) be an actual behavioral profile. Fix a player \(i\) and a mark \(m\).
Write

\[
P^{-i}_m=
\prod_{t=0}^{m}\prod_{j\ne i}(1-q_{t,j}),
\]

where \(q_{t,j}\) is player \(j\)'s Quit probability at the date-\(t\)
all-Continue history. This is the probability that all opponents of \(i\)
survive through the mark in the counterfactual profile in which \(i\) never
quits.

Suppose the whole-profile cap and the post-mark cap satisfy

\[
B_i(\pi)\le r_i(\{i\})+\sigma,
\qquad
B_i(\pi^{(m+1)})\ge r_i(\{i\})+\gamma,
\]

with \(0\le\sigma<\gamma\). The pre-mark absorption theorem gives

\[
P^{-i}_m\le\frac{2M+\sigma}{2M+\gamma}.
\]

Put

\[
a(\gamma,\sigma)
=\frac{\gamma-\sigma}{2M+\gamma}>0.
\]

Then

\[
1-P^{-i}_m\ge a(\gamma,\sigma).
\tag{1}
\]

## Finite deleted-law atom

In the profile with \(i\) fixed to Never, equation (1) is exactly a lower
bound on the probability of absorption by a nonempty coalition of
\(I\setminus\{i\}\) no later than \(m\). Summing first over dates and then
forgetting the date gives

\[
\sum_{\varnothing\ne C\subseteq I\setminus\{i\}}
\Pr(\text{terminal coalition }C\text{ by }m)
\ge a(\gamma,\sigma).
\]

Therefore some nonempty coalition \(C\subseteq I\setminus\{i\}\) satisfies

\[
\Pr(\text{terminal coalition }C\text{ by }m)
\ge
\frac{a(\gamma,\sigma)}{2^{|I|-1}-1}.
\tag{2}
\]

For four players the denominator is seven. Along any sequence of rows with
fixed \(i\), fixed positive \(\gamma\), and \(\sigma_n\to0\), one may pass to
a subsequence on which the same deleted terminal coalition \(C\) has a fixed
positive law-mass floor.

This is a law atom, not a one-date atom. No large original date atom follows
without a separate clock-compression or causalization argument.

## Marginal hazard consequence

By the union bound,

\[
1-P^{-i}_m
\le
\sum_{t=0}^{m}\sum_{j\ne i}q_{t,j}.
\]

Consequently

\[
\sum_{t=0}^{m}\sum_{j\ne i}q_{t,j}
\ge a(\gamma,\sigma),
\tag{3}
\]

and some opponent \(j\ne i\) satisfies

\[
\sum_{t=0}^{m}q_{t,j}
\ge\frac{a(\gamma,\sigma)}{|I|-1}.
\tag{4}
\]

In four players the denominator is three. Finite pigeonhole again freezes
one such opponent along a subsequence.

Equation (4) is counterfactual marginal hazard along one actual root word. It
is not yet persistent hazard along one infinite exact spine. In particular,
different normalized-return rows can be unrelated finite words, and their
hazard lower bounds cannot be concatenated without a source-renewal theorem.

## Interaction with a tight eager cycle

If a unique-all-Continue cap has a nonempty tight set, the checked collision
geometry supplies a directed eager cycle inside that tight set. Applying the
pre-mark floor to every tight coordinate gives one deleted-law atom and one
opponent-hazard floor for each cycle vertex.

This does not automatically give two persistent exact-spine labels. All
floors associated with a proper tight subset may be carried by one common
outsider, and the pre-mark words need not be exact. If the tight set is the
whole player set, however, the collection of exclusions forces at least two
distinct labels to carry hazard at least
\(a(\gamma,\sigma)/(|I|-1)\) in each row. Indeed, choose a label with maximal
total hazard; the inequality that excludes it forces a second label above
this floor, and maximality gives the same floor for the first. Making those
two labels uniform along a subsequence is finite pigeonhole; making the rows
consecutive pieces of one exact spine remains the missing producer.

## Precise available interface

The useful source-side packet is therefore:

- a fixed tight coordinate;
- a fixed post-mark cap margin;
- a fixed deleted terminal-coalition law atom, or a fixed opponent marginal
  hazard floor, before the mark;
- the original marked pair and literal post-mark tail;
- no exactness assertion for the pre-mark word.

A terminal consumer must either use this counterfactual absorption directly
or exactify the word while preserving a positive fraction of it.
