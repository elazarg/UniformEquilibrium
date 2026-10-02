# Review of the common-prescribed-prefix backward edge

**Reviewer:** `CODEX_DESCENDANT`  
**Verdict:** **PASS as ordinary mathematics; one bounded Lean/container
qualification is required.**

## Claim checked

The note claims that if a finite prescribed root word (W_n) has joint
survival tending to one, then prefixing a tail changes its complete behavioral
cap only by a vanishing amount, provided the limiting tail cap strictly
dominates singleton cash-out.  Copying the same prescribed word onto two tails
which differ only in player (q)'s strategy then gives a literal whole-profile
response edge, unlike the invalid shifted-response construction.

## Cap estimate

The estimate

\[
 \left|B_i(W_n\star T_n)-\max\{r_i(\{i\}),B_i(T_n)\}\right|
 \le 2M(1-h_{i,n})
\]

is correct for unrestricted behavioral responses, including Never.

Against fixed opponents, behavioral pure-time extremality reduces the cap to
deterministic stopping times in \(\mathbb N\cup\{\infty\}\).  For a time
inside the word, on the event that every opponent survives the whole word the
terminal coalition is exactly the singleton \(\{i\}\).  Every collision or
other prefix payoff is confined to the complementary event, of probability
at most \(1-h_{i,n}\).  For a time after the word, the same good event reaches
the literal tail and gives exactly the corresponding tail pure-time payoff.
Both payoffs lie in \([-M,M]\), including the zero Never payoff, so the stated
\(2M\) coupling bound follows.  Taking the supremum preserves both bounds.
Randomization between early, late, and Never times cannot improve on this
pure-time supremum.

I specifically tried to falsify the maximum formula by putting a large
coalition reward at a prefix row and by letting the response Quit before a
prescribed opponent Quit.  Such a reward can affect the cap, but only on the
opponent-prefix-absorption event already charged by \(1-h_{i,n}\); it does not
produce an omitted order-one term.  The use of player-deleted rather than
joint survival is essential and is correct.

Since joint survival is bounded above by every deleted survival, joint
survival tending to one gives \(h_{i,n}\to1\).  The checked positive-minimum
singleton margin then makes the maximum eventually select the tail cap.
Prescribed payoffs, ordinary laws, and deleted laws have the analogous direct
couplings.  Thus the complete semantic/law convergence claim passes.

## Literal response and debt identities

Both endpoints retain player (q)'s prescribed prefix actions and differ
only in the suffix.  They are therefore literal one-player strategy
replacements.  The common-prefix payoff identity gives the joint-survival
factor in (3.2), while invariance of (q)'s cap under changing (q)'s own
strategy gives (3.3).  Because (W_n) is an exact cap--Nash stack for the
source tail, the usual source debt-scaling identity combines with these two
equalities to give (3.4).  No target-side cap--Nash assertion is needed or
made.

The marked mass after the copied prefix is exactly the joint-survival factor
times the suffix marked mass.  Hence the eventual \(\lambda/2\) floor and
minimum target causalization are valid.

## Bounded container qualification

`FinFourMinimumAtomProducer` and `FinFourMinimumAtomChronology` store the
target suffix chronology, but they do not by themselves store a paired source
family (A_n) or a response-edge proof (A_n\to P_n).  Therefore the sentence
that causalizing (P_n) “retains the actual prefixed response edge in its
supplied ancestry” is mathematically valid only when the construction returns
an additional paired-edge/backward-compiler wrapper.  It is not a field that
comes for free merely by constructing the target producer.

This is a proof-engineering/container qualification, not a flaw in the
common-prefix edge: the literal paired families and exact response relation
are explicitly available and can be stored.  A Lean handoff should therefore
state a structure containing the regenerated target producer, the prefixed
source family, and the literal update/equalities, rather than claim that the
existing producer type alone exposes them.

## Novelty and consequence

I did not find an existing declaration proving this complete-cap maximum
estimate for an arbitrary common prescribed prefix.  The named checked
payoff, survival, and pure-time declarations support the proof but do not
already package the adapter.

Subject to the explicit paired-edge wrapper above, the result removes the
prefix source/target typing gap in the moving minimum-chord arm.  It remains a
behavioral response edge, not a Nash--Bellman chronological edge, and it does
not consume the positive-residual, off-minimum, or later tangent exits.
