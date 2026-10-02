# Review of `AGKRS_3_4.md`

## Post-repair audit of the exported packet (2026-08-30)

The two gaps identified below were repaired in
`formalized/AGKRS_FORWARD_TRICHOTOMY_BY_REFUSAL_COMPACTIFICATION.md`.
I reread its S.3 construction against the actual path discretization in
`literature/AKRS.tex` (Lemma 4.7 and Proposition 4.6 in the pinned v1;
numbering differs in the published version).

The support statement used by the export is genuine, not an extra
assumption.  The product witness matches total absorption and the ratios of
the cell's singleton increments.  Consequently its coordinate `i` is
positive exactly when the cell has positive singleton-`i` mass, and every
coordinate is strictly below one on a small cell.  The export's split of such
mass into a small jump (SP.1) or a continuous component (SP.2b), followed by
the survival-weighted continuation telescope, gives a uniform row error
tending to zero.  The revised small-mass-interval refusal proof also repairs
the former atom-free-neighborhood error.  I found no remaining logical gap in
the ordinary-mathematics S.3 proof.

One displayed constant should be weakened.  The pinned technical lemma has a
factor `(|I|+1)`, and a small product jump supplies a collision/singleton
ratio bounded by `1/(k-1)` rather than literally `1/k`.  Thus the constant
called `K_d` in equations (18)--(23) is too small as written.  Replacing it by
an unspecified finite constant `C_d` (or, for large `k`, a sufficiently large
explicit multiple of `2^d(d+1)(2^d-1)`) makes every estimate valid and leaves
the conclusion unchanged.  This is bookkeeping, not a failure of S.3.

The implementation work described in this historical review was subsequently
completed by the checked chronological path, small-cell productization,
decoder, and table-level trichotomy declarations recorded in the packet's
formalization record.

## Claim reviewed

The note claims the unconditional implication

$$
\text{approximate equilibria at every positive tolerance}
\Longrightarrow \mathrm{S.1}\lor\mathrm{S.2}\lor\mathrm{S.3}
$$

for every finite quitting game, with the literal AGKRS quantifiers and with
arbitrary unilateral behavioral deviations.  Its new route is to complete a
vanishing-error equilibrium sequence to absorbing profiles, compactify their
absorption paths, and derive zero-perfectness directly from ordinary Nash by a
global refusal deviation.

## Sources inspected

- the published paper, *Absorption paths and equilibria in quitting games*,
  especially Theorem 3.4, Proposition 4.8, Lemma 4.9, Proposition 4.11,
  Definition 4.13, Proposition 4.14, and Theorem 4.15;
- `Literature/AshkenaziGolanKrasikovRainerAndSolan2022.lean`, including the
  branch equivalences and the `sorry`-marked general case of `theorem3_4`;
- `UniformEquilibrium/Quitting/Classification/ExistenceBranches.lean` for the
  exact S.1/S.2/S.3 production predicates; and
- `UniformEquilibrium/Quitting/AbsorptionPath/ContinuousPath.lean` for the
  absorption-path and zero-perfectness definitions.

The published numbering used in the note is correct.  The tracked literature
file is pinned to arXiv v1, whose corresponding results have different
numbers.

## Parts that survive adversarial checking

### Normalization and absorption

Coordinatewise subtraction of the never payoff preserves every relevant
gain and branch.  If all normalized solo rewards are nonpositive,
all-Continue is an exact stationary equilibrium.

If some solo reward $a_i$ is positive, the late-sure-Quit deviation gives

$$
\Pr_x(\theta=\infty)a_i\le\varepsilon.
$$

The remaining finite-tail and same-date collision contributions vanish as
the forced date tends to infinity.  Completing at a sufficiently late date
therefore produces an absorbing profile whose terminal law differs by
$o(1)$.  This is enough to retain every positive limiting absorption-path
jump and every payoff calculation below clock time one.

### Refusal lemma

The finite-set refusal inequality is correct.  If $D_n$ is the payoff change
from forcing Continue at the selected dates, then

$$
D_n=(1-q_n)d_nD_{n+1}
$$

at an unchanged date, whereas at a changed date

$$
D_n=C_n-V_n+d_nD_{n+1}.
$$

Since

$$
C_n-V_n=\frac{q_n}{1-q_n}(V_n-Q_n)\ge q_n\delta,
$$

and earlier refusals only increase the probability of reaching later dates,
the claimed lower bound

$$
\gamma_i(x^{i,B},x^{-i})-\gamma_i(x)
\ge \delta\sum_{n\in B}s_nq_n
$$

follows.  Finite exhaustion gives the countable version.  This is genuinely
stronger than a pointwise Nash estimate and is the important new idea in the
packet.

### Nonterminal jumps and the terminal S.2 branch

At a positive nonterminal limiting jump, the matching source stage has reach
bounded away from zero.  Its suffix is therefore an $o(1)$-equilibrium.
Both one-stage endpoints are bounded above by the mixed value; convexity then
forces equality for every endpoint in the limiting root's support.  This
correctly proves SP.1.

At a terminal jump, finite-product structure supplies one player whose Quit
probability tends to one.  Replacing that action by sure Quit and replacing
the continuation by an approximate min-max punishment is valid.  For every
other player, prescribed and deviating payoffs change only on the event that
the selected quitter would have Continued, giving the stated uniform
$O(1-q_k)$ regret perturbation.  For the quitter, the min-max inequality and
the local suffix Nash inequality give the required Continue-first bound.
This yields the literal arbitrary-behavior S.2 branch.

## Gap 1: the interval in the continuous support argument need not be atom-free

Section 4.3 says that, because the limiting path is continuous at $t$, one can
choose a neighborhood $J$ in which the limit has no atom, and consequently
all source one-stage absorption probabilities in $J$ tend uniformly to zero.
This is false as written.  A continuous point may be an accumulation point of
arbitrarily small jumps; there need not be an atom-free neighborhood.

The argument appears repairable by replacing "no atom" with a quantitative
small-mass interval.  If

$$
\gamma_t^i(\pi)-a_i=g>0,
$$

choose a one-sided compact interval $J=[t,t+h]$ with atom-free endpoints,
$t+h<1$, such that:

- all path payoffs in $J$ differ from $\gamma_t(\pi)$ by at most $g/8$; and
- the total absorption mass of $J$ is smaller than a constant multiple of
  $g(1-t-h)/R$.

The first property follows from continuity at $t$ after making $h$ small.
The second follows because $t$ itself is not a jump.  Weak convergence at the
two endpoints makes the total source mass in $J$ comparably small.  Hence
every source row in $J$ has small conditional absorption probability, so its
immediate-Quit value is uniformly close to $a_i$.  The conditional payoff at
every such row is uniformly close to $\gamma_t^i(\pi)$: anchor at one
continuity endpoint and bound all variation inside $J$ by the total mass of
$J$.  Thus, for all large $k$,

$$
V_n^k-Q_n^k\ge g/4
$$

at every relevant genuine source stage.

Applying the refusal lemma then forces the source singleton mass in $J$ to
zero.  Weak convergence contradicts a positive right derivative at $t$.
The vanishing-mass artificial completion must be removed explicitly from the
source singleton measure, but its contribution is already $o(1)$.

This repair is local and uses no new game-theoretic hypothesis, but it must be
written into the proof.  The current statement that $J$ has no atom is not
acceptable.

## Gap 2: small-block sequential perfection needs the support argument stated
quantitatively

Section 6 has the right mechanism, but one sentence is too strong: at a small
block beginning with a small discrete jump, zero-perfectness does not say
exactly that $a_i$ is below the post-jump path payoff.  SP.1 compares the
actual Quit endpoint with the mixed-row value.  Because the jump absorption
probability is at most $1/k$, this implies the desired solo inequality only
up to $O(R/k)$.

The final estimate can still be obtained.  It should be proved by separating
the two support clauses:

1. The product row has absorption probability $p\le1/k$.  Therefore its
   Continue endpoint and mixed value are $O(R|I|p)$ from the post-block
   payoff, and its Quit endpoint is $O(R|I|p)$ from $a_i$.
2. The support-preserving construction in the proof of Lemma 4.9 ensures that
   positive Quit probability for player $i$ implies positive singleton
   $i$-mass in the corresponding path block.
3. Such mass comes either from a small jump at which SP.1 gives equality for
   the used Quit action, up to the preceding $O(R|I|p)$ conversion, or from a
   continuous component.  On a continuous component the singleton
   coordinate is Lipschitz because the total clock grows at unit speed;
   positive increment therefore gives a point of positive derivative, where
   SP.2 gives $\gamma^i=a_i$.
4. The path payoff varies by only $O(Rp)$ across the block, and the actual
   discretized continuation adds the uniform error $e_k$.

These four statements give both no-profitable-action inequalities and both
support inequalities with one uniform error

$$
\eta_k\le C_{I,R}/k+C'e_k\to0.
$$

Thus the proposed S.3 conclusion appears sound, but the exact support
preservation from Lemma 4.9 and the small-jump $O(p)$ conversion must replace
the current exact wording.

## Verdict

This is not a lengthy restatement of the existing conditional capstone.  The
global refusal inequality is new and, if the two analytic repairs above are
completed, it gives a substantially simpler proof of the corrected forward
S.1/S.2/S.3 trichotomy in AGKRS Theorem 3.4.

The packet does **not yet pass the export gate** because Gap 1 is a genuine
false step as written and the uniform support estimate in Gap 2 is presently
only sketched.  Neither gap currently looks fatal.  A revised proof with the
small-mass interval argument and a quantitative small-block lemma would be a
high-priority export candidate and, because it settles the complete forward
trichotomy with unrestricted deviations, would still require a second
independent falsification review.  It does not establish the paper's printed
reverse implication or turn S.3 into approximate Nash; the printed error-
exponent theorem used for that direction is separately refuted in the
repository.
