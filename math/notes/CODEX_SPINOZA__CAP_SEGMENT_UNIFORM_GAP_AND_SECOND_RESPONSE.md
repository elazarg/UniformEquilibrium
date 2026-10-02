# Near-full finite-cap installation exposes a source-attached second response

Author: CODEX_SPINOZA

## Status

**Exact ordinary mathematics; positive-global-gap response-chain reduction,
not Lean-checked and not a terminal consumer.** Randomizing one debtor between
its prescribed stopping law and an attained complete cap yields a labelled
dichotomy. Away from the cap endpoint, that named debtor retains a fixed
fraction of its original debt. Near the endpoint, a distinct full-gap
response selected at the cap child transports back along the same one-player
mixture with only a total-variation loss.

At one explicit mixture parameter, the original cap response and the new
response are both profitable at the same actual source. If the original cap
is a finite sure clock and a distinct sure anchor was already present, the
new response may also be chosen from one finite pure-time/Never menu. The
full cap update followed by the new cap update is then a literal two-owner
horizontal best-response chain. This is stronger than the tautological fact
that the global gap holds along the segment, but it is not a Nash--Bellman
chronology.

## Question

In the eventual shifted-cap ray, let \(b\) be the retained finite sure-clock
anchor and let \(k\ne b\) have positive debt with an attained finite/Never
cap. Can a controller obtain terminal approximate Nash profiles by
randomizing \(k\)'s prescribed law against that cap?

## 1. Exact cap-segment response theorem

Let \(I\) be a finite player set and let \(r\) be a quitting reward table.
Choose \(M>0\) such that every terminal reward lies in \([-M,M]\); Never pays
zero. Suppose there is a game-level terminal exploitability gap
\(\Gamma>0\):

\[
 \forall \rho\ \exists j\in I\ \exists\beta_j,\qquad
 U_j(\rho[j\leftarrow\beta_j])-U_j(\rho)\ge\Gamma .
 \tag{1}
\]

Let \(\sigma\) be an actual behavioral profile, let \(k\in I\), and suppose
one literal complete response \(A_k\) attains \(k\)'s cap at \(\sigma\).
Write

\[
 g=d_k(\sigma)
   =U_k(\sigma[k\leftarrow A_k])-U_k(\sigma)\ge\Gamma.
 \tag{2}
\]

For \(t\in[0,1]\), let \(\sigma^t\) be the actual profile obtained by replacing
\(k\)'s stopping law with its independent private mixture

\[
 (1-t)\,\operatorname{Law}(\sigma_k)
   +t\,\operatorname{Law}(A_k),
 \tag{3}
\]

and retaining every opponent strategy literally. Put

\[
 \tau=\sigma^1=\sigma[k\leftarrow A_k].
 \tag{4}
\]

Then \(d_k(\tau)=0\). Apply (1) at \(\tau\) and fix one response
\(\beta_j\) of gain at least \(\Gamma\). Necessarily \(j\ne k\).

For every \(t\in[0,1]\),

\[
 d_k(\sigma^t)=(1-t)g,                                    \tag{5}
\]

and the fixed response \(\beta_j\), copied back from \(\tau\), has gain at
\(\sigma^t\) at least

\[
 \Gamma-4M(1-t).                                          \tag{6}
\]

Since all terminal and Never payoffs lie in \([-M,M]\), (1) implies
\(\Gamma\le2M\). Define

\[
 \varepsilon_0={\Gamma\over8M},\qquad
 \delta_0=\varepsilon_0\Gamma={\Gamma^2\over8M}.
 \tag{7}
\]

Then \(0<\varepsilon_0\le1/4\), and:

1. if \(t\le1-\varepsilon_0\), player \(k\)'s cap response gains at least
   \(\delta_0\) at \(\sigma^t\);
2. if \(t\ge1-\varepsilon_0\), the fixed distinct response \(\beta_j\) gains
   at least \(\Gamma/2\ge\delta_0\) at \(\sigma^t\); and
3. at the single actual source

   \[
   \sigma^\star:=\sigma^{\,1-\varepsilon_0},               \tag{8}
   \]

   both literal responses are co-realized, with gains at least

   \[
   \operatorname{gain}_k(A_k;\sigma^\star)\ge\delta_0,
   \qquad
   \operatorname{gain}_j(\beta_j;\sigma^\star)
      \ge{\Gamma\over2}.                                   \tag{9}
   \]

Thus the whole segment has an explicit **labelled** cover: the old owner
\(k\) covers its first portion, while the one fixed distinct endpoint
response \(\beta_j\) covers its final portion. The positivity of
\(\max_i d_i(\sigma^t)\) alone was already assumption (1); the content is
that the two displayed responses, rather than freshly reselected debtors,
cover the segment and coexist at (8).

## 2. Proof

Player \(k\)'s opponents are fixed throughout the segment. Its complete cap
therefore has the same value \(B_k(\sigma)\) for every \(t\). Expected payoff
is affine in \(k\)'s own stopping law, and the endpoint \(A_k\) pays exactly
that cap. Hence

\[
\begin{aligned}
 U_k(\sigma^t)
  &=(1-t)U_k(\sigma)+tB_k(\sigma),\\
 B_k(\sigma^t)-U_k(\sigma^t)
  &=(1-t)\bigl(B_k(\sigma)-U_k(\sigma)\bigr),
\end{aligned}
\]

which proves (5). At \(t=1\) this also proves \(d_k(\tau)=0\), so the
full-gap response at \(\tau\) belongs to a distinct player \(j\).

Couple \(\sigma^t\) and \(\tau\) by using the cap law \(A_k\) in the common
branch of mass \(t\), and the old law only in the exceptional branch of mass
\(1-t\). For any fixed strategy of player \(j\), including \(\beta_j\), the
induced terminal outcomes differ with probability at most \(1-t\). Their
expected payoffs therefore differ by at most \(2M(1-t)\). The same estimate
holds for the two prescribed payoffs. Subtracting gives

\[
\begin{aligned}
 &U_j(\sigma^t[j\leftarrow\beta_j])-U_j(\sigma^t)\\
 &\quad\ge
 U_j(\tau[j\leftarrow\beta_j])-U_j(\tau)-4M(1-t),
\end{aligned}
\]

which is (6).

Every unilateral gain is at most the width \(2M\) of the payoff interval.
Thus \(\Gamma\le2M\), proving the numerical assertions after (7). If
\(t\le1-\varepsilon_0\), (2) and (5) give

\[
 d_k(\sigma^t)\ge\varepsilon_0 g
                  \ge\varepsilon_0\Gamma=\delta_0.
\]

If \(t\ge1-\varepsilon_0\), (6) gives

\[
 \operatorname{gain}_j(\beta_j;\sigma^t)
 \ge\Gamma-4M\varepsilon_0=\Gamma/2.
\]

Finally \(\delta_0\le\Gamma/4<\Gamma/2\), since
\(\Gamma\le2M\). This proves the labelled cover and (8)--(9).

## 3. Finite shifted-cap refinement

Return to the literal shifted-cap ray. Suppose:

1. a fixed player \(b\ne k\) is prescribed to Quit surely by a finite date
   \(H\) at \(\sigma\); and
2. \(A_k\) is a deterministic finite clock, surely quitting by date \(T\).

At the endpoint \(\tau\), both \(b\) and \(k\) are distinct prescribed sure
quitters. Therefore every complete cap at \(\tau\) is attained among the
finite pure times through \(\max\{H,T\}\) and Never: after any one player
deviates, at least one of those two sure opponents remains.

Choose \(\beta_j\) in (1) to be such a cap-attaining pure time/Never response.
Then (9) is a source-attached pair of two literal pure-time/Never responses.
The first label is the shifted-cap owner \(k\); the second is a distinct
terminal-gap debtor \(j\), and both comparisons live at the one actual
profile \(\sigma^\star\) on the cap-installation segment.

Replacing \(k\)'s mixture at \(\sigma^\star\) by \(A_k\) gives exactly
\(\tau\) and gains \(d_k(\sigma^\star)\ge\delta_0\). At \(\tau\),
\(\beta_j\) attains \(j\)'s complete cap and gains at least \(\Gamma\).
Therefore

\[
 \sigma^\star
 \ \dashrightarrow_k\ 
 \tau
 \ \dashrightarrow_j\
 \tau[j\leftarrow\beta_j]                                 \tag{10}
\]

is a literal two-step chain of complete cap responses with distinct owners
and the displayed positive gains. The dashed arrows are horizontal
whole-strategy replacements, not exact Nash--Bellman predecessor edges.

The profile \(\sigma^\star\) still retains \(b\)'s sure finite clock, because
only \(k\)'s law was mixed. Hence if \(j\ne b\), its complete cap is in fact
attained directly at \(\sigma^\star\) by a finite pure time/Never candidate.
If \(j=b\), (9) still supplies the literal finite/Never response selected at
\(\tau\) with the displayed gain at \(\sigma^\star\); it need not attain
\(b\)'s complete cap there.

If \(A_k\) is Never rather than a finite clock, the general theorem and its
uniform gap remain valid, but the endpoint has only the old sure anchor.
The response \(\beta_j\) in (1) is then unrestricted and need not have a
finite-clock representative.

## 4. Relation to the shifted-cap consumer

The theorem gives an exact structural answer to the direct temporal mixing
proposal. Installing only a fraction of \(k\)'s cap cannot hide the original
response without exposing one fixed distinct endpoint response:

- before the final \(\varepsilon_0\)-slice, \(k\) remains a fixed debtor;
- inside that slice, a distinct response inherited from the actual cap child
  remains macroscopically profitable.

At the boundary of the two slices both responses coexist at one
source-attached actual profile. In the finite-cap arm, both are explicit
finite pure-time/Never responses and the old sure clock remains prescribed.
This is suitable input for the checked common-prefix/two-response machinery,
but applying either response still changes an opponent law seen by the other.
The theorem does not make the two responses simultaneous best replies, an
exact product root, or a chronological block.

Consequently the cap-segment controller does not consume the projective ray.
It returns either the original far-end cap or the two-owner horizontal chain
(10) at the cap-child seam. This is a positive-global-gap reduction; it does
not rely on a \(D_*=0\) best-response-cycle regression.

## Sources inspected

- notes/CODEX_SPINOZA__UNIQUE_SURE_ACTUAL_CHILD_TO_LITERAL_SHIFTED_CAP_RAY.md,
  frozen and twice reviewed at SHA256
  dd1da90ccc9fafb7fbc994799d708148470e641d843849aaec0aab65f785133d;
- notes/CODEX_HAHN__TWO_RENEWED_SURE_CLOCKS_GIVE_FINITE_COMPLETE_SEMANTICS.md,
  independently reviewed at SHA256
  e596e78d2476e72d7cc561a77b4b7507c24a3ac682dc69946ffc23629bbc735d;
- formalized/FINITE_CLOCK_DOUBLE_FULL_GAP_COSOURCE.md;
- Section 15 of
  notes/CODEX_SPINOZA__NONCARRIER_EXCURSION_LOG_CLOCK_AND_EXIT_BUDGET.md,
  which proves the broader source-matched half-reset/receiver principle from
  a deleted-player quiet lift without cap attainment;
- UniformEquilibrium/Quitting/Paths/StoppingLawMixture.lean; and
- UniformEquilibrium/Quitting/Paths/StoppingLawOperationalDistance.lean.

The stopping-law mixture realizes (3) as an actual behavioral strategy. The
operational-distance coupling bounds are uniform in the fixed deviating law,
which is the only cap-continuity input used in (6).

The cap-segment identity (5) is the attained-cap specialization of the older
half-reset affine debt calculation. The additional point here is the
near-endpoint transport from the literal finite cap child, which keeps one
fixed second response and yields the sequential two-owner chain (10).

## Boundary tests

### The game-level gap is essential

If the endpoint cap child is terminal Nash, there is no distinct response
\(\beta_j\), and the segment may end at equilibrium. The exact two-sure-clock
response-cycle regression has \(D_*=0\) and an exact equilibrium elsewhere;
it therefore does not contradict this theorem.

### Attainment is used only for the moving player

Equation (5) uses the literal cap-attaining endpoint \(A_k\). The response
\(\beta_j\) need only realize the game-level gain (1). It need not attain
\(j\)'s complete cap unless the finite two-sure-clock refinement is invoked.

### Private mixture does not introduce correlation

Only player \(k\) mixes two of its own complete stopping laws. Every opponent
strategy and every cross-player independence relation is retained. The
coupling coin is a proof device for the resulting terminal-law estimate, not
a public recommendation.

## Scope and nonclaims

This theorem extracts a quantitative source-attached second response and,
in the finite-cap arm, a literal two-owner cap-response chain. It is not an
exact Nash--Bellman producer, a simultaneous
two-response equilibrium, a horizontal-seam compiler, or a projective-clock
consumer.

It does not show that the second response preserves the first debt after
installation, that either response returns to the original source, that the
two response times have a useful order, or that repeated response replacement
has a decreasing scalar rank. No uniform-equilibrium payoff is claimed.

## Next exact question

In the finite-cap refinement, apply the checked common-prefix two-cut dispatch
to the two literal responses at \(\sigma^\star\). Does the retained sure clock
and the explicit cap-segment ancestry eliminate any one of its residual
branches, or does the dispatch return exactly the already known paid-port
waist?
