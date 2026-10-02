# Review of the sufficient-state and Markov-completeness documents

## Claims reviewed

The two documents contain three logically distinct claims.

1. For the labelled pure-intervention hierarchy \(\mathcal K_k\), recursive
   unilateral replacement first closes at order \(|I|-1\). In particular, the
   exact Fin4 order is three.
2. Current payoff-response data, even when it contains the payoff law under
   every unilateral behavioral replacement, need not determine a literal
   suffix.
3. A compact metric state cannot make all calendar-indexed suffix probes
   uniformly continuous with one depth-independent modulus.

The first claim is a positive exact Markov-completeness theorem for one
operation. The second and third are negative statements about chronology and
topology. They are compatible and should not be presented as competing answers.

## Mathematical verdict

The core proofs of all three claims appear correct as ordinary mathematics,
subject to the qualifications below.

### Exact counterfactual order

The replacement formula is correct. Conditioning on the new stopping time of
the replaced player raises an order-\(k\) query to order \(k+1\). At the top
face, where all other players have already been fixed, the missing order-
\(|I|\) law is universal and independent of the source. This proves closure at
order \(|I|-1\).

The blocker construction is a valid separation for every
\(k\le |I|-2\). Any order-\(k\) intervention either removes the hidden player
or leaves an earlier blocker, while one replacement followed by a legal
order-\(k\) query removes all blockers and exposes the hidden stopping time.
It works with deterministic finite clocks and does not depend on a reward
table.

The equivalence between \(\mathcal K_{|I|-1}\) and the tuple of labelled
marginal stopping laws is also correct for \(|I|\ge2\). Fixing every opponent
except one anchor recovers each finite atom of a player's clock, and fixing all
opponents to Never recovers its Never atom. Conversely, independence and the
deterministic terminal map reconstruct every counterfactual law.

Accordingly, the exact information classification is:

| task | least information established here |
|---|---|
| current payoffs and unilateral behavioral caps | order one |
| recursively update the same pure-intervention state under unilateral replacement | order \(|I|-1\) |
| Fin4 recursive replacement | order three, equivalently four marginal stopping laws |

This answers the replacement-order core of
`QUITTING_COUNTERFACTUAL_RESPONSE_STATE.md`.

### Payoff-response collision

The four-player probe table and the two delayed profiles do have identical
laws of terminal **payoff vectors** under every current unilateral behavioral
replacement. Their positive-reach one-step suffixes have different prescribed
payoffs. The probe identity after suffixing and then forcing player 3 to Quit
correctly recovers player 2's hazard at the selected date.

This proves that current reward-pushforward response data are not sufficient
for labelled literal suffixing. It does not prove the same statement for the
complete current law of terminal dates and coalitions. The document should use
“terminal payoff-response law” consistently; “complete terminal response” can
otherwise be misread as the richer labelled outcome law used in the
\(\mathcal K_k\) hierarchy.

### Uniform-suffix compactness obstruction

The isolated-spike family is a valid uniformly separated family. If the state
supports the same labelled operation “take suffix \(n\), then apply the fixed
replacement” with one modulus independent of \(n\), the probe payoff forces a
fixed positive state separation. Sequential compactness is therefore
impossible. The binary-word version likewise rules out a finite global
strategic net at that resolution.

This theorem depends essentially on two exact readings:

- suffix operations are labelled, so the operation at depth \(n\) on one
  source must correspond to the operation at the same depth on the other; and
- the continuity modulus is common to all depths.

Neither follows automatically from a loose set-valued bisimulation statement.
The sufficient-state question should say explicitly whether labels must be
preserved. The no-go is decisive under the natural program-semantics reading,
but it should remain a conditional theorem under any weaker reading.

## Reconciliation of the two documents

There is no contradiction between exact Markov completeness and the compactness
no-go.

The exact order-three Fin4 state is losslessly equivalent, on actual profiles,
to the full tuple of marginal stopping laws. In the operational supremum/total-
variation metric it supports nonexpansive unilateral replacement and uniform
control of all static pure-time queries, but it is not compact. Isolated late
spikes stay a fixed distance apart.

The same underlying clock data are compact in a product or pointwise topology.
In that topology every fixed finite-depth query is continuous, but the family
of all suffix maps is not equicontinuous. A suffix chosen at the moving spike
depth exposes a fixed difference.

Thus the exact tradeoff is:

| state/topology | replacement | suffixes | compactness |
|---|---|---|---|
| marginal laws with operational TV/sup metric | exact and nonexpansive | stable on positive-survival regions | no |
| complete hazard stream with product topology | exact | each fixed suffix is continuous | yes |
| complete hazard stream with all-depth sup control | exact | one uniform modulus | no |

The positive theorem solves an algebraic information-closure problem. It does
not by itself solve global synthesis, recurrence, or the uniform-equilibrium
problem.

## Corrections and scope boundaries

### 1. “Minimal higher-order object” is presently a lower bound

The probe proves that any exact state supporting the labelled composition

\[
\text{suffix at }n\quad\text{then}\quad(3\leftarrow Q_3^0)
\]

must determine the scalar tower

\[
\left(U_2((S_n\sigma)[3\leftarrow Q_3^0])\right)_{n\ge0}.
\]

It does not prove that the entire suffix-indexed arbitrary-response tower is a
minimal complete representation. The exact phrase should be “a necessary
observable” or “an information lower bound,” not “the minimal state.”

The order theorem supplies a sharper classification for replacement:
\(\mathcal K_{|I|-1}\), equivalently the marginal stopping laws, is minimal
within the counterfactual hierarchy and up to lossless recovery. These are
different notions of minimality and should not be merged.

### 2. Positive-reach and literal off-path suffixes differ

The marginal stopping law determines a suffix by conditioning only while each
player has positive survival probability to the marked date. If a player's
survival probability is zero, its initial stopping law forgets its prescribed
actions after that unreachable history. A literal behavioral suffix can still
expose them.

Therefore `MARKOV_COMPLETE.md` proves closure under **positive-mass suffix
selection**, not under every literal suffix operation in the broader sufficient-
state question. Exact closure under arbitrary off-path suffixing requires the
full hazard policy, or an equivalent suffix-indexed conditional-law tower.

This is an important boundary, not a technicality: the collision/no-go document
is precisely about what happens when literal suffix access is retained as an
operation.

### 3. Two meanings of finite approximation must be separated

The rational finite-clock construction proves:

> For each actual profile and each accuracy, there is one rational finite-clock
> profile approximating all static pure-intervention laws uniformly.

It does not give a finite global state space or a finite epsilon-net for all
profiles. The packing theorem proves that no such global finite net exists in
the all-depth operational metric. Rename the section “per-profile rational
finite-clock approximation” and avoid saying that it settles a finite exact
approximation hierarchy without specifying the quantifiers.

### 4. The compact boundary construction is an architecture, not yet a global
consumer

The pointwise graph closure is a reasonable compact carrier. Fixed actual
replacement laws extend coordinatewise by dominated convergence, and storing
joint terminal boundary laws repairs the loss of relative escape ties from
marginal limits.

It still does not establish:

- continuity uniformly over varying or escaping replacement laws;
- a canonical suffix at zero survival;
- realization of every boundary transition by one executable source family;
- a finite uniform approximation of the entire carrier; or
- a terminal, recurrent, or ranked synthesis theorem.

The hyperspace extension for escaping intervention labels is a promising
proposal, but the present paragraph does not prove its transition formulas or
realization theorem. It should be placed with viable architectures rather than
inside the exact Markov theorem.

## Viable state architectures left open

The two results substantially narrow, but do not empty, the design space.

1. **Projective finite-program state.** Retain the full hazard stream or the
   counterfactual graph with the product topology. Require a modulus only for
   each fixed finite family of depths and operations. A synthesis proof must
   choose its finite program before invoking the corresponding modulus.

2. **Positive-reach operational state.** Use the marginal stopping laws and
   allow suffixing only where every relevant survival probability is at least
   a supplied \(\eta>0\). Conditioning then has an explicit
   \(O(\eta^{-1})\) stability bound. A separate dispatch must consume the
   vanishing-survival boundary.

3. **Two-tier state.** Keep a compact semantic or pointwise carrier for
   recurrence and a noncompact, source-attached chronological passport for the
   finitely many operations currently being executed. Compactness is required
   only of the core; the passport is controlled by explicit budgets, tightness,
   or a renewable rank.

4. **Inverse system of finite-depth states.** Store every finite-depth response
   packet with compatible restriction maps. Each level is finitely
   approximable and the inverse limit is compact, but continuity is only
   levelwise. The missing theorem is a diagonal controller whose requested
   depth grows slowly enough for its error budget.

5. **Absorption-clock quotient.** Quotient calendar time and expose only
   operations stable in accumulated absorption mass. This is viable only if
   arbitrary literal suffixing is removed from the legal language or recovered
   by a separate realization theorem.

6. **Noncompact exact state with a compact/ranked projection.** Use the exact
   marginal or hazard state for operations, but prove recurrence or termination
   only after projection to a compact semantic carrier or a well-founded rank.
   The projection must retain enough source data to lift a recurrent return.

These architectures identify where new mathematics is needed. Merely taking
the pointwise compact closure does not solve the controller problem.

## Recommended `meta/` organization

The folder should separate exact results from architectural interpretation.
A minimal clean organization is:

1. `SUFFICIENT_STATE.md`
   - a short synthesis and comparison table;
   - the precise tradeoff between exact replacement, suffix access,
     compactness, and uniform approximation;
   - the viable architectures and the remaining global question;
   - no long proofs.
2. `COUNTERFACTUAL_MARKOV_ORDER.md`
   - the exact \(|I|-1\) theorem;
   - the blocker separations;
   - equivalence with marginal stopping laws;
   - payoff/cap evaluation and exact replacement stability.
3. `SUFFIX_INFORMATION_OBSTRUCTION.md`
   - the terminal-payoff-response collision;
   - the isolated-spike compactness theorem;
   - the packing consequence and exact quantifiers.
4. `STATE_TOPOLOGIES_AND_APPROXIMATION.md`
   - operational versus pointwise topology;
   - positive-reach suffix conditioning;
   - per-profile rational approximants;
   - split-clock/joint-boundary architecture, with proved facts separated from
     proposed extensions.

The two open questions should then be adjusted as follows:

- `QUITTING_COUNTERFACTUAL_RESPONSE_STATE.md` should record the order-
  \(|I|-1\) replacement classification as resolved and ask only for the
  topology, zero-survival suffix, boundary realization, and synthesis
  consequences that remain open.
- `QUITTING_COMPOSITIONALLY_SUFFICIENT_STATE.md` should replace the impossible
  all-depth common modulus by one explicitly chosen architecture: fixed finite-
  program moduli, a positive-reach modulus, or a two-tier compact-core/passport
  formulation. If the original common-modulus formulation is retained, it is
  now a no-go theorem rather than an open construction question.

The files should omit provenance narratives and workflow language. A single
mathematical status sentence distinguishing exact theorem, proposed topology,
and open synthesis is enough.

## Final assessment

The exact order-three Fin4 replacement theorem is the strongest item. It is a
clean answer to a well-posed information question and should be preserved as a
standalone result.

The suffix collision and compactness obstruction are also substantive. They
show that exact recursive information and compact uniform control are distinct
requirements, and they explain why a compact semantic carrier repeatedly
fails to support source-faithful chronology.

The documents do not yet construct a compositionally sufficient state for
global quitting-game synthesis. Their correct combined conclusion is a
classification of the design tradeoff and a short list of viable
architectures—not a solution of the controller problem.
