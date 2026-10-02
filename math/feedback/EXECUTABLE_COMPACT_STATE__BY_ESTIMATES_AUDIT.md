# Estimates audit of `EXECUTABLE_COMPACT_STATE`

## Status

The stopping-law calculations, the total-variation estimates, the tight-fusion
consumer, and the clock/tester nonattainment example are mathematically sound.
The note is not yet ready to be stated at its present full scope. The displayed
proof of Theorem 4 establishes finite-cylinder compatibility at the initial
source, not compatibility with every finite program in the proposed grammar.
There are also two theorem-surface repairs: the hypotheses behind (41)--(43)
must be made literal, and Lemma 3 needs a summable nonnegative budget.

The Lean declarations inspected for semantic comparison were
`quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact` and
`quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto` in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`,
and the pure-time stopping-law interface around
`quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime` in
`UniformEquilibrium/Quitting/Paths/StoppingLawMixture.lean`.

## 1. Stopping laws and the Late/Never split

Equations (1)--(6) are correct for ordinary behavioral quitting profiles. On
the unique unresolved public history at each date, a player's strategy is
equivalent to a law on

\[
K=\mathbb N\sqcup\{\infty\},
\]

and a complete behavioral replacement is a new law independent of the fixed
opponent laws. Expected payoff is affine in that replacement law, so pure
finite times and Never exhaust the cap.

The event partition in (7) is correct, provided the extended ordering is
understood so that \(\infty>n\). In particular, \(M_{-i}>n\) includes the event
that every opponent plays Never. Equations (8) and (9) then correctly separate

* `Late`, the limit of finite deadlines, which pays \(r_i(\{i\})\) if every
  opponent plays Never; and
* `Never`, which pays \(r_i(\varnothing)\) on that event.

The tie term in (7) tends to zero because the atoms of any probability law on
\(\mathbb N\) tend to zero. Hence the continuous extension to the compact
space

\[
(\mathbb N\cup\{\omega\})\sqcup\{\infty\}
\]

is valid, and adjoining \(\omega\) changes a supremum over finite dates into
a maximum without changing its value. Equation (11) is therefore correct.
The standard project game has \(r(\varnothing)=0\); allowing another bounded
Never payoff is a harmless generalization but should remain visibly separate
from the standard theorem statement.

## 2. Tail and strategic estimates

Equations (28)--(39) are correct with the note's convention that
\(\|\mu-\nu\|_1\) is the full \(\ell^1\) distance, twice the usual
probabilistic total-variation distance.

* Equation (28) is the exact finite-coordinate/tail decomposition followed by
  the triangle inequality.
* The product bound (30) follows by telescoping product measures.
* Since rewards have absolute value at most \(R\), (31) and (32) have constant
  \(R\) for full \(\ell^1\) distance. No extra factor two is missing.
* Taking suprema gives (33), including the Late and Never endpoints.
* For \(t>N\), the finite action \(t\) and Late differ only when
  \(N<M_{-i}<\infty\). This proves (35), and (36) follows by taking the
  supremum over all later finite dates.
* Fixed prefixing contracts \(\ell^1\). For varying words, common-uniform
  coupling gives the coarse term \(2\sum_{t<L}|x_i^t-y_i^t|\) in (38).
* Restriction and normalization on an event of mass at least \(\alpha\) gives
  the stated \(2/\alpha\) suffix constant.

There is, however, a statement mismatch in (41)--(43). As displayed, (41)
contains the numbers \(\eta_{\ell,i}\), but the theorem does not put into the
formula's hypotheses that **both** corresponding input tails are at most those
numbers. Without those hypotheses, (28) does not imply the claimed bound.
Likewise the prose permits varying prefix words, replacement laws, and other
operation parameters, but their error terms do not occur in the displayed
definition of \(E_P\). The result should be stated in one of two exact forms:

1. all operation parameters are fixed, and both input tails satisfy the
   displayed bounds; or
2. `E_P` is enlarged by the explicit parameter errors from (38) and the
   analogous replacement terms.

With that repair, a maximum of pathwise products of the suffix constants is
enough. The product over every suffix edge in (40) is a coarser valid bound.

## 3. Tight fusion and the terminal-Nash consumer

Theorem 1 is valid under its stated per-port eventual uniform tightness and
literal operation coherence. Coordinate convergence plus (44) prevents loss
of mass to \(\omega\), gives an actual probability law, and upgrades weak
coordinate convergence to \(\ell^1\) convergence. Positive reach margins then
make suffix conditioning continuous. Equations (31)--(33) give uniform
obstacle and cap convergence, not merely convergence at each fixed pure time.

Theorem 2 is consequently correct. Because the prescribed law is itself an
allowed unilateral replacement, \(B_i\ge U_i\); the limiting inequality gives
the reverse direction and hence exact terminal Nash. In the standard quitting
game this also feeds directly into the checked theorem
`quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact`. The note's
weaker statement that the constant profile supplies terminal approximants is
therefore safe.

The exact quantifier is important: the theorem assumes one increasing family
with eventual uniform tightness separately at every named port. It does not
derive that passport from mere membership in every finite compact carrier.

## 4. Lemma 3

The budget identity and inequality (54) are correct, but the statement needs
the assumptions

\[
\beta_n\ge0,\qquad \beta_\infty\ge0,
\qquad \sum_n\beta_n<\infty,
\]

unless the conclusion is deliberately formulated in the extended
nonnegative reals. With an ordinary real-valued infinite sum, summability
cannot remain implicit. Under these assumptions the proof is exact; indeed
the difference series is absolutely summable because both laws have total
mass one.

## 5. The clock/tester counterexample

The table calculation in Theorem 4 is exact.

For the prescribed profile, the outcome is always \(\{c\}\), hence

\[
U=(-1,0).
\]

Against tester \(a\)'s Never law, player \(c\) obtains \(-1\) at every finite
deadline and \(0\) by Never, so \(B_c=0\). Tester \(a\) earns one exactly on a
tie with one atom of the uniform clock and zero otherwise, so \(B_a=1/n\).
The stopping law converges to \(\delta_\omega\), while the obstacle and caps
converge to the displayed values.

The nonattainment proof is also correct. An actual profile with \(U_c=-1\)
must terminate at \(\{c\}\) almost surely. Thus \(T_c\) is a probability law
on the countable set \(\mathbb N\) and has a positive atom. Quitting at that
atom gives \(a\) a strictly positive payoff, contradicting \(B_a=0\).

Equations (60)--(65) correctly give the fixed \(1/2\) budget obstruction. In
particular, if every finite atom is at most \(2^{-t-2}\), the total probability
that \(c\) ever quits is at most one half, and so \(U_c\ge-1/2\).

## 6. Substantive scope gap in Theorem 4

The proof after (60) establishes

\[
\forall F\subset\mathbb N\text{ finite}\;\forall\delta>0\;\exists n
\]

such that the finitely many initial clock coordinates, \(U_c\), and \(B_a\)
meet the requested tolerances. This is a strong and useful finite-cylinder
nonattainment theorem.

It does **not**, by itself, establish the later claim

\[
\forall\text{ finite programs }P\;\exists\text{ an actual legal execution of
}P
\]

approximating every node and certificate in an arbitrary program trace. Such a
program may include derived suffixes, replacements, varying operation
parameters, reach certificates, and selected auxiliary roots. The displayed
clock estimate does not prove convergence or legal compatibility of all those
derived fields.

There are two honest repairs:

1. restrict Theorem 4 and item 7 of the architecture theorem to finite
   cylinder/semantic probe programs at the original source; this already proves
   that compact coordinate coherence does not imply executable realization; or
2. define a precise admissible program grammar and prove by structural
   induction that the uniform-clock family executes every fixed program and
   that all derived traces converge, treating positive-reach suffixes and
   chosen-root labels explicitly.

Until that extra theorem is supplied, “every fixed finite program” and the
full projective-family formulation are overclaims. The exact nonattainment
example, the summable-budget obstruction, and the tight-fusion positive theorem
remain intact after the narrower formulation.

## Final verdict

The note contains genuine mathematics and a viable formalization package.
The main quantitative constants are correct, and no Late/Never or unrestricted
deviation gap was found. Before export it should:

1. make the tail and operation-parameter hypotheses of (41)--(43) literal;
2. add nonnegativity and summability to Lemma 3; and
3. narrow Theorem 4 to finite-cylinder probes or prove the missing induction
   over the proposed finite-program grammar.

The third item is the only substantive scope issue. It does not undermine the
counterexample's core lesson: compact semantic coherence without a tightness,
budget, or executable passport can lose an order-one amount of strategically
relevant late mass.

## Revision check

The revised note addresses the three audit findings:

1. Before (41), it now assumes separately that both input tails obey the
   chosen bounds and initially fixes all operation parameters. It then states
   explicitly that varying prefixes, replacement laws, or roots require their
   own displayed parameter-error terms. This repairs (41)--(43).
2. Lemma 3 now assumes nonnegative \(\beta_n,\beta_\infty\) and
   \(\sum_n\beta_n<\infty\). This repairs the ordinary real-valued budget
   statement.
3. Theorem 4 is now titled and concluded as a finite-cylinder theorem. Its
   decisive quantifier is correctly restricted to finite probe families, and
   the final architecture conclusion no longer depends on arbitrary-program
   compatibility.

One minor wording qualification remains. The sentence after (62) also claims
compatibility for a fixed rooted elementary program by structural induction.
For that extension, “positive-reach domain” should mean an **eventual uniform
positive reach margin**, and operation parameters should be fixed or converge
with the hypotheses used in Theorem 1. Mere positivity at every approximant
does not make suffix normalization continuous. Alternatively, that sentence
can be deleted; the proved finite-cylinder statement already establishes the
advertised obstruction. The opening sentence of Section 7 should likewise say
“finite-cylinder coherence” rather than “projective coherence of all fixed
finite programs” unless this qualified structural induction is retained.

Subject to that wording repair, the three original objections are resolved.
