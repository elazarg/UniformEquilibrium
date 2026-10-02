# Post-edit audit of the question roadmap

Reviewer: `GATE_STRENGTHENER`

## Verdict

**Not yet PASS.**  The index is now structurally accurate, contains no links
to conference ephemera, and no longer presents the strict inert search as an
exhaustive Fin4 normal form.  The incentive-gadget quantifier is correct.  The
general escape-aware search, strict-inert specialization, and the main Fin4
two-component roadmap are stated honestly.

Five P1 mathematical-specification issues remain:

1. the positive-social-surplus question does not assume global minimum-value
   nonattainment and accepts an unconsumed rank transition;
2. the cardinal question calls its pointwise existential outsider witnesses a
   compatible family, although compatibility is exactly what must be built;
3. the Jensen question does not define its disintegration, loss, constants,
   or terminal outputs precisely enough to be a mathematical question;
4. the response-reentry question accepts a common response or response square
   without requiring the promised downstream consumer; and
5. the Simon question requires a necessity implication from absence of long
   orbits but never requires the Lyapunov certificate to establish that
   absence.  A bounded Lyapunov function only bounds accumulated cost unless
   an additional coercivity or limiting argument is stated.

There are also four P2 wording/scope repairs.  After the P1 repairs, no further
essential top-level route appears missing.

## P1 issues

### P1.1 — Positive social surplus is not yet the exact nonattainment arm

File: `questions/POSITIVE_SOCIAL_SURPLUS_ESCAPE_CONSUMER.md`.

The hypothesis

\[
 \delta=D(\bar\sigma)-D(z)>0
\]

says only that the particular marginal-law limit \(\bar\sigma\) does not
attain the minimum.  It does **not** say that the global minimum value is
unattained by every actual behavioral profile.  A different actual profile
could have debt \(D(z)\).  In that case this selected escaping realization is
not the residual left by the attainment theorem.

To make the question exactly the advertised remaining arm, add

\[
 \forall\sigma\text{ actual},\qquad D(\sigma)>D(z).
\]

Equivalently, say explicitly that no actual behavioral profile attains the
global minimum debt value.  Keep \(\delta>0\) because it supplies the strict
quantitative escape account for the selected realization.

Output 3 also accepts “a renewable finite-rank transition” without requiring
an exhaustive successor question or consumers for the terminal states.  It
must instead require one of:

- a strict finite rank on a source-preserving transition system whose every
  terminal state yields terminal approximants, a uniform payoff, or a charged
  return; or
- an exhaustive source-preserving transition to a named open question.

Without this repair the question accepts precisely the kind of unconsumed
rank edge excluded by the README criterion.

### P1.2 — The cardinal question assumes the missing compatibility

File: `questions/CARDINAL_MINIMAL_OUTSIDER_CONSUMER.md`.

The supplied theorem has the quantifier order

\[
 \forall B\ \forall\varepsilon\ \forall\sigma_B\quad
 \exists d\in B\ \exists t<\infty
\]

with the full ambient gain.  It gives no compatibility as \(B\),
\(\varepsilon\), or the survivor profile changes.  The question then says:

> Use the compatible family of proper-block outsider witnesses ...

That is an extra hypothesis, and it assumes the principal missing producer.
Replace it by:

> Select and coordinate the universally available proper-block outsider
> witnesses, or prove that every failure of such compatibility has one of the
> listed terminal consequences.

The mathematical data should retain the original pointwise existential
quantifiers.  Compatibility of deleted player, date, survivor payoff, or
lifted profile must be an output, not supplied data.

### P1.3 — The Jensen question is not self-contained

File: `questions/FIN4_JENSEN_CLOCK_SELECTION_AND_CAP_LEAKAGE.md`.

Several quantities used by the desired alternative are not quantified or
defined:

- the singleton mass floor and whether it holds eventually or only in the
  limit;
- the stopping-law weights, including the Never atom;
- the exact infinite Jensen average;
- the anchored date interval on which the owner is replaced;
- the paid endpoint players, actions, mass floor, and gain floor which must be
  retained;
- the two response endpoints whose other-player cap increments must be
  controlled; and
- the terminal consumer of the selected response square or renewable
  transition.

A precise version should introduce a probability law
\(\alpha_n\) on \(\mathbb N\cup\{\infty\}\), actual deterministic-clock
completions \(P_{n,t}\), and

\[
 J_n=
 \sum_{t\in\mathbb N\cup\{\infty\}}
   \alpha_n(t)D(P_{n,t})-D(\sigma_n)\ge0.
\]

It should then pass to the exhaustive alternative

\[
 J_n\longrightarrow0
 \quad\text{or}\quad
 \exists\kappa>0\ \exists\text{ a subsequence},\quad J_n\ge\kappa.
\]

In the first arm it must quantify a selected \(t_n\), a fixed stage-mass
floor \(\lambda>0\), convergence \(D(P_{n,t_n})\to D_*\), fixed player/action
labels, and a fixed or explicitly scaled paid gain.  In the second arm it
must specify actual response endpoint profiles and either:

- place both endpoints on the minimum fibre by an upper bound on the total
  other-coordinate cap leakage; or
- send strict ascent to a named source-preserving terminal/rank consumer.

“Paid endpoint data required by a minimum-return consumer” and “convert it
into a response square” are interface descriptions, not quantified
mathematical conclusions.  As written, the file does not yet meet the
directory's own definition of a question.

### P1.4 — Response reentry accepts intermediate objects

File: `questions/FIN4_RESPONSE_REENTRY_ACROSS_REGENERATION.md`.

Outputs 1 and 2 are not terminal and are not stated as exhaustive transitions
to another question:

1. a response simultaneously asymptotically optimal on both sides is still
   only a common-response witness;
2. a response square whose charge “survives” is still only a local square
   unless it enters a charged-return or minimum-response-chord consumer.

The question should require **composition**, for example:

- the common response proves no-new-entry minimum-fibre replacement and hence
  a renewable support descent with consumed terminal states; or
- the selected hybrid seam contributes a fixed positive or summably retained
  first-disagreement charge to an admissible near-return; or
- failure of common-response compactness produces the stated escaping
  pure-time packet together with its consumer.

The asymptotic errors and positive charge floor must be quantified.  If the
outgoing and incoming sequences are \(x_n,y_n\), say exactly which subsequence
map identifies a regenerated incoming source with the outgoing endpoint
family.  “Next incoming source” is otherwise chronological language for an
object currently known only through subsequence reconstruction.

The bounded four-player hybrid chain is available between any two complete
profiles.  The missing theorem is not existence of that chain, but retention
of one observer response chart, marked continuation, and nonvanishing or
summable charge across it.  The question should state that as the output.

### P1.5 — The Simon output omits the central implication

File: `questions/SIMON_LYAPUNOV_CERTIFICATE.md`.

The self-loop correction \(c(x,x)=0\) is necessary and is now present.
However, Output 1 asks for:

- a Lyapunov certificate; and
- a proof that *absence* of arbitrarily long production orbits implies a
  positive gap.

It never asks for a proof that the certificate and branch exclusions imply
that absence.  The displayed inequality with bounded \(V\) gives only

\[
 \sum_k c(x_k,x_{k+1})
 \le
 \frac{\sup V-\inf V}{c_0}.
\]

Arbitrarily long or infinite orbits may still exist with zero or summable
cost.  Even if \(c(x,y)>0\) for every non-diagonal edge, there need not be a
uniform positive lower bound on that cost near the diagonal.

Output 1 must therefore require a complete implication of the form

\[
 \begin{array}{c}
 \text{certificate + stationary exclusion + punishment exclusion}
 \end{array}
 \Longrightarrow
 \begin{array}{c}
 \text{the exact production object required by necessity does not exist}
 \end{array}
 \Longrightarrow
 \text{positive all-behavior gap}.
\]

If the required production object is an orbit with unbounded cumulative
variation, state that.  If it is an arbitrarily long orbit, add the coercive
lower bound or compact-isolation theorem which converts length to cumulative
cost.  If convergence of every finite-cost orbit creates a stationary or
punishment branch, state and prove that limiting theorem.  Merely pairing the
certificate with the conditional sentence “absence implies gap” leaves the
main seam assumed.

## P2 issues

### P2.1 — Stopping laws converge to laws, not to a profile

In `POSITIVE_SOCIAL_SURPLUS_ESCAPE_CONSUMER.md`, replace

> the compactified marginal stopping laws converge to an actual product
> profile \(\bar\sigma\)

by

> the compactified marginal stopping laws converge weakly to laws
> \((\mu_i)_{i\in I}\), and \(\bar\sigma\) is the actual behavioral product
> profile reconstructed from those laws.

Also assume \(I\) is nonempty and write all sums over nonempty coalitions.
These are the hypotheses of the supplied escape account.

### P2.2 — Define cardinal minimality

In `CARDINAL_MINIMAL_OUTSIDER_CONSUMER.md`, say explicitly that \(r\) has no
uniform-equilibrium payoff, every quitting game with strictly fewer players
does have one, and \(r\) has the displayed terminal gap \(\gamma\).  The
phrase “cardinal-minimal finite quitting game” alone is not a mathematical
predicate.

### P2.3 — Scope the face-cycle finite subproblem to Fin4

`POSITIVE_MINIMUM_FACE_CYCLE_ALIGNMENT.md` begins with an arbitrary finite
player set.  Its claim that a terminal strict-toggle class reaches a pair is
the Fin4 specialization: in four players the class reaches cardinality at
most two and also at least two, hence contains a pair.  State:

> In the four-player specialization, ...

The file should also distinguish the exact Nash property in the deleted game
from the ambient lifted local error \(\varepsilon_n\).  At present “terminal
Nash profiles” and “their local Nash error” appear to refer to the same game.

Finally, say explicitly that the cyclic estimate yields terminal debts
tending to zero and, after payoff subsequence selection, one limiting payoff.
This records why Output 1 is a consumer rather than another cycle packet.

### P2.4 — Clarify the two pure-time responses

In `FIN4_RESPONSE_REENTRY_ACROSS_REGENERATION.md`, either quantify

\[
 q^0,q^1\in\mathbb N\cup\{\infty\}
\]

or say that one of the two responses is Never.  “Two complete pure-time
responses, including Never” is ambiguous between those meanings.

## Files which pass their post-edit audit

### `questions/README.md`

The two terminal Fin4 components agree with the source-preserving completion
atlas.  Focused producer questions are correctly separated from atlas nodes,
the direct hard-residual route is not conflated with the atlas, and the
strict-inert search is visibly subordinate to the general escape-aware
search.  After the P1 questions themselves are repaired, the index needs no
structural change.

### `questions/FIN4_INERT_MACHINE_CERTIFICATE_SEARCH.md`

PASS.  The scope paragraph now says exactly that eliminating this chamber
closes one minimum-return branch and that other Fin4 counterexample branches
may remain.  Local inert feasibility is separated from the global
all-behavior certificate, and finite failure is not treated as evidence.

### `questions/INCENTIVE_GADGET.md`

PASS.  The quantifier

\[
 \exists\alpha>0\ \exists\varepsilon_0>0\ \forall\sigma
\]

is explicit, \(a,b,\ell\) form an exhaustive first-outcome partition including
calibrators and Never, and the contradiction with
\(\ell^2\ge4ab\) gives a fixed positive all-behavior gap.  The architecture
screens are correctly treated as exclusions a successful table must evade,
not assumptions.

### `questions/ESCAPE_AWARE_FIN4_CERTIFICATE_SEARCH.md`

PASS, unchanged.  The soundness inequality has the correct direction, Never
and escaping clocks are represented, and nontermination or finite solver
failure proves nothing.

## Ephemera, duplication, and completeness audit

None of the edited question files relies on a note, feedback file, export
packet, or other ephemeral document.  References are confined to other open
questions and short Lean source pointers.

The positive-social-surplus question does not duplicate the proved
nonpositive-surplus chamber once P1.1 is repaired.  The cardinal question does
not duplicate canonical passive padding: it asks for arbitrary-table descent.
The Jensen and response-reentry questions are not new atlas components; they
are independent producer seams inside minimum return.  The inert search is a
specialization of the general escape-aware search, as the README now records.

No additional essential question is missing.  The remaining strong
note-mining connections—two-tier packet realization, paid/reset rank,
paired-cap uniqueness, fully screened charge, pair-base face alignment, and
strict inertness—already map to a maintained file.  Adding separate questions
for their intermediate algebraic screens would duplicate existing components
without improving the transition map.

## Pass conditions

This post-edit set passes when:

1. P1.1 adds global minimum-value nonattainment and consumes every rank exit;
2. P1.2 makes outsider compatibility an output;
3. P1.3 supplies the exact disintegration, constants, exhaustive Jensen split,
   and consumed outputs;
4. P1.4 composes common responses and response squares to named terminal or
   rank consumers; and
5. P1.5 supplies the missing certificate-to-production-obstruction theorem,
   with the correct cost/coercivity or limiting hypothesis.

The P2 changes should be made in the same edit because they affect the literal
quantifiers and player-count scope.
