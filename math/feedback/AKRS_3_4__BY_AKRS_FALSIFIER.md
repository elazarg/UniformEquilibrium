# Independent falsification review of `AGKRS_3_4.md`

## Verdict

The theorem-level idea survives adversarial review.  The refusal lemma is
correct, the late absorbing completion is harmless below clock time one, and
the terminal-jump construction really gives the literal unrestricted-behavior
S.2 branch.

The file `AGKRS_3_4.md` nevertheless fails the export gate in its present
wording for two reasons:

1. a point of continuity need not have an atom-free neighborhood; and
2. the small-cell S.3 argument omits the quantitative support-preserving
   comparison needed at cells containing small jumps.

I independently checked the repairs subsequently written in
`notes/CODEX_ROOT__AGKRS_REFUSAL_COMPACTIFICATION_REPAIRS.md`.  Subject to
incorporating those arguments into the result packet, both defects are
repairable without any additional game-theoretic hypothesis.  After that
incorporation, I find no surviving mathematical objection to the claimed
forward S.1/S.2/S.3 trichotomy.  This is therefore a **pass for the repaired
mathematical package, but not for the unrevised source file**.

## Exact claim reviewed

For a finite quitting game with an arbitrary payoff at perpetual
continuation, assume that for every positive tolerance there is an
approximate equilibrium against every unilateral behavioral strategy.  The
claim is that one fixed one of the following branches holds for every
sufficiently small tolerance:

- S.1: a stationary approximate equilibrium;
- S.2: an approximate equilibrium with a sure first-stage quitter and an
  arbitrary behavioral punishment holding that quitter near its min--max;
- S.3: a completely absorbing profile which is sequentially approximately
  perfect at every stage against its actual continuation payoff.

Only this forward implication was audited.  I did not audit or endorse the
printed reverse implication or the separately problematic error exponent.

## Sources inspected

- the published AGKRS paper, especially Theorem 3.4, Proposition 4.8, Lemma
  4.9, Proposition 4.11, Definition 4.13, Proposition 4.14, and Theorem 4.15;
- the pinned arXiv source `literature/AKRS.tex`, noting where its version of
  Lemma 4.9 differs from the published proof;
- `Literature/AshkenaziGolanKrasikovRainerAndSolan2022.lean`, including the
  exact branch equivalences and the `sorry` in the general case;
- `UniformEquilibrium/Quitting/Classification/TableExistenceBranches.lean`;
- `UniformEquilibrium/Quitting/Classification/ExistenceBranches.lean`;
- `UniformEquilibrium/Quitting/AbsorptionPath/ContinuousPath.lean`; and
- `UniformEquilibrium/Quitting/AbsorptionPath/FiniteWindowRefusalReweighting.lean`.

The checked definitions confirm that S.2 quantifies over a complete
behavioral punishment profile and that S.3 demands one-stage perfection at
every row of an actually absorbing root sequence.  The draft does not weaken
either requirement.

## 1. Normalization and absorbing completion

Subtracting each player's perpetual-continuation payoff from all of that
player's outcomes preserves every unilateral gain, min--max gap, and all
three branches.  If every normalized solo reward is nonpositive,
all-Continue is an exact stationary equilibrium.

If some player has solo reward $a_i>0$, following the prescribed profile up
to date $N$ and then quitting surely gives, in the limit as $N$ tends to
infinity, gain

$$
\Pr(\theta=\infty)a_i.
$$

The finite-after-$N$ absorption probability and the probability of an
opponent's atom exactly at $N$ both vanish.  Consequently an
$\varepsilon$-equilibrium satisfies

$$
\Pr(\theta=\infty)a_i\leq\varepsilon.
$$

Choosing a late date and forcing this player to quit there changes terminal
mass by $o(1)$ and makes the profile absorbing.  At any fixed absorption
clock $t<1$, reach is bounded away from zero, so the artificial completion
cannot supply a positive limiting jump and changes conditional payoff by
$o(1)$.  This is exactly the amount of preservation later arguments need;
no equilibrium claim about the completed profile is being used.

## 2. The refusal lemma is valid

For a finite set $B$ of dates at which

$$
V_n-Q_n\geq\delta>0,
$$

force the selected player to Continue at all dates in $B$.  If $D_n$ denotes
the modified conditional payoff minus the original conditional payoff, then
at an unchanged date

$$
D_n=(1-q_n)d_nD_{n+1},
$$

while at a changed date

$$
D_n=(C_n-V_n)+d_nD_{n+1}.
$$

The identity

$$
C_n-V_n=\frac{q_n}{1-q_n}(V_n-Q_n)\geq q_n\delta
$$

is correct; the hypothesis itself excludes $q_n=1$.  Earlier refusals can
only increase the reach of a later selected date.  Backward induction
therefore gives

$$
\gamma_i(x^{i,B},x^{-i})-\gamma_i(x)
\geq \delta\sum_{n\in B}s_nq_n.
$$

This is one legal complete behavioral deviation.  Applying Nash before
letting finite sets exhaust a countable set proves the desired global mass
bound.  There is no interchange of a supremum with a limit here.

## 3. Nonterminal jumps give exact path perfection

At a limiting jump with positive post-jump survival, Proposition 4.11 gives
matching genuine source stages whose reach converges to a positive number,
whose product roots converge to the path root, and whose post-row payoff
converges to the path continuation.  Any suffix deviation can be prefixed by
the original behavior, so the source suffix has Nash error equal to the
global error divided by reach, hence tending to zero.

The pure Quit and pure Continue first-row deviations are therefore both at
most the prescribed mixed payoff in the limit.  Since that mixed payoff is
their convex combination, every endpoint with positive limiting support is
equal to it.  This proves the full SP.1 condition.  The artificial completion
cannot be the matching source of a positive nonterminal jump because its
total mass vanishes.

## 4. Continuous support: false wording and valid repair

Continuity at $t$ does **not** imply an atom-free neighborhood.  For example,
singleton jumps of sizes comparable to $2^{-2m}$ at times $t+2^{-m}$ can
accumulate at a continuous point.  This falsifies Section 4.3 as written.

The repair uses a one-sided interval $J=(t,t+h]$ whose endpoints are
continuity points and whose **total** absorption mass is small.  If

$$
g=\gamma_t^i(\pi)-a_i>0,
$$

right continuity permits $h$ to be chosen so that path payoffs throughout
$J$ stay close to $\gamma_t^i(\pi)$, while finiteness of the absorption
measure and absence of an atom at $t$ make the total mass of $J$ arbitrarily
small.  Weak convergence at the endpoints transfers that bound to the
completed source paths.

Every genuine source row whose pre-row clock lies in $J$ then has:

- reach at least $1-t-h$;
- conditional one-stage absorption bounded by the mass of $J$ divided by
  $1-t-h$;
- immediate-Quit payoff uniformly close to $a_i$; and
- prescribed conditional payoff uniformly close to
  $\gamma_t^i(\pi)$.

The last assertion follows directly by anchoring the remaining reward moment
and survival denominator at the left endpoint and bounding their variation
by the total mass of $J$.  Thus $V_n-Q_n\geq g/2$ uniformly after shrinking
$J$.  The refusal lemma forces the original singleton-$i$ mass in $J$ to
zero; the artificial completion contributes only $o(1)$.  Weak convergence
at the endpoints then forces the limiting singleton mass of $J$ to be zero,
contradicting a positive lower right derivative at $t$.

This proves SP.2(b).  The one-stage sure-Quit deviation independently proves
SP.2(a).  I found no hidden atomlessness or attainment assumption in the
repaired argument.

## 5. A terminal jump gives literal S.2

At a terminal jump, the limiting product root has zero joint-Continue
probability, so one fixed player has Quit probability one.  Matching source
roots have that player's Quit probability tending to one and positive reach,
and their suffixes have vanishing Nash error against arbitrary behavioral
deviations.

Force that player to Quit at the first row and replace the continuation by
an arbitrary behavioral profile whose best-response value is within $\eta$
of the player's min--max.  For every other player, both prescribed and
deviating payoffs can change only when the selected player would originally
have Continued.  This gives the uniform regret perturbation
$O(1-q_k)$ over the complete deviation class.

For the selected player, if $A_k$ is the immediate opponent-absorption
contribution and $d_k$ is opponent joint survival, the original suffix Nash
condition implies

$$
A_k+d_km_i\leq V_k+o(1).
$$

The punishment replaces $m_i$ by at most $m_i+\eta$, while
$|V_k-Q_k|=O(1-q_k)$.  Hence every Continue-first behavioral deviation is
unprofitable up to $o(1)+\eta$, and Quit is the prescribed action.  This is
the exact S.2 structure, including the unrestricted continuation response
and approximate min--max requirement.

## 6. Small-cell S.3: the quantitative support repair works

For a zero-perfect path with no terminal jump, copy all large jumps exactly
and apply the published Proposition 4.8/Lemma 4.9 construction to every cell
of conditional mass $p\leq1/k$.  Large-jump rows are approximately perfect
by SP.1 and the uniform continuation-payoff error.

For a small-cell product row, bounded rewards give uniformly

$$
|Q_i-a_i|+|C_i-w_i|+|V_i-w_i|=O_{I,M}(p),
$$

where $w$ is the post-cell continuation.  The path payoff changes by at most
$O(Mp/(1-p))$ anywhere in the cell.  SP.2(a), or SP.1 at a small entrance
jump followed by this $O(p)$ conversion, gives the upper Quit inequality.
The Continue endpoint is automatically in support and is $O(p)$ from the
mixed value.

The lower support inequality for Quit requires the **specific** witness from
the proof of published Lemma 4.9, not an arbitrary nearby product row.  That
witness has

$$
\xi_i>0\quad\Longrightarrow\quad
\text{positive singleton-$i$ increment in the path cell}.
$$

Such an increment either contains a small jump at which player $i$ uses Quit,
so SP.1 gives equality up to the same $O(p)$ conversions, or has positive
continuous mass.  Continuous singleton coordinates are dominated by the
unit-speed total clock and hence are absolutely continuous; positive mass
gives a point of positive derivative, where SP.2 gives
$\gamma^i=a_i$.  Moving this equality to the cell endpoint costs only
$O(Mp)$.  This proves the Quit support inequality.

Finally, the discretization has a continuation-payoff error $e_k\to0$
uniformly over its cells.  The preceding estimates give one stage-independent
bound

$$
\eta_k\leq C_{I,M}/k+C'e_k\longrightarrow0.
$$

Every row is therefore sequentially $\eta_k$-perfect and Proposition 4.8's
profile is completely absorbing.  This is literal S.3.  The argument also
handles cells containing countably many small jumps: positive singleton mass
comes from at least one jump or from the nonatomic component, and only the
cell's total conditional mass enters the error bound.

## 7. Boundary tests

- If all normalized solo rewards are nonpositive, the proof stops in exact
  S.1; no compactification is needed.
- A positive terminal limiting atom cannot be produced by the late completion
  because the completion mass is $o(1)$; it therefore exercises the genuine
  S.2 construction.
- A continuous point with arbitrarily many accumulating small jumps refutes
  the original atom-free-neighborhood sentence but is covered by the
  small-total-mass repair.
- A product approximation that introduces a tiny positive hazard at a zero
  singleton coordinate can fail sequential support perfection.  The
  published Lemma 4.9 witness explicitly preserves this zero and is therefore
  essential.
- Never and arbitrarily late stopping are included throughout: the starting
  equilibrium, the suffix Nash tests, and the S.2 punishment cap all quantify
  over complete behavioral deviations.  The only finite deviation is the
  refusal of a finite set, applied before finite exhaustion.

## Gate recommendation

Do not export the current `AGKRS_3_4.md` verbatim.  Merge the two repaired
arguments above into a self-contained packet, state explicitly that only the
forward trichotomy is proved, cite both independent reviews, and include the
published support-preserving Lemma 4.9 construction rather than the simpler
ratio formulation from the pinned v1 transcription.  With those changes, I
recommend immediate export for Lean formalization.
