# Adversarial gate review of `HARD_RESIDUE.md`

Reviewer: `CODEX_GATE_FALSIFIER`

## Verdict

**FAIL as an export packet.**

The first part contains two useful and apparently correct ordinary-mathematics
results:

1. the displayed four-player table is an exact counterexample to the local
   implication “positive paid row plus retained atom implies a nontrivial exact
   cap root”; and
2. canonical maximal-root regeneration can be iterated while retaining a
   uniform positive lower bound on the paid-row scale and on an inherited
   terminal atom.

The follow-up `Two-clock diffuse boundary theorem` is false under its stated
hypotheses.  There is a two-player exact Nash--Bellman counterexample with the
same strictly negative off-diagonal sign pattern as a hard card-two principal.
Accordingly, the claimed elimination of the two-clock diffuse arm and the
four-way hard-residual dispatch do not survive.

The packet should not be repaired in place for export.  The valid maximal-orbit
reduction should be separated into a self-contained packet, and the two-clock
section should be replaced by the counterexample and a correctly strengthened
conditional lemma if that lemma has a source adapter.

## Claim audited

The document makes three logically separate claims.

1. A cap, a later paid pure-time edge, and a retained finite atom do not by
   themselves exclude unique all-Continue at the cap.
2. Repeated canonical positive-absorption maximal roots give either eventual
   unique all-Continue or an infinite literal paid/reset orbit with summable
   root absorption and noncollapsing paid gain and inherited atom mass.
3. An exact two-clock diffuse Nash--Bellman tail with positive conditioned
   singleton shares and boundary values equal to solo rewards forces both
   normalized off-diagonal solo entries to vanish.

Claims 1 and 2 survive, subject to the qualifications below.  Claim 3 is
false.

## 1. Exact audit of the local unique-root example

The example is correct, with Never payoff zero as in the project semantics.
Let players 0 and 2 Quit at date 1 and let everyone Continue at date 0.  Players
1 and 3 may Continue forever after the absorbing date.

For each of players 0, 2, and 3, the reward is 2 when that player is absent
from the terminal coalition and 0 when present.  Hence:

- player 0 can Continue into coalition `{0,2}` and receives 0 as prescribed,
  but can instead Continue while player 2 alone Quits and receive 2;
- the same calculation applies to player 2;
- player 3 receives 2 from `{0,2}`; and
- player 1 receives 2 from `{0,2}`, can receive 1 by Quitting at date 0, and
  receives 2 by Quitting at date 1 with 0 and 2.

No unilateral behavioral strategy can exceed 2.  Thus the complete
unrestricted cap is exactly `(2,2,2,2)`, the outcome law has unit mass at
`{0,2}`, and player 1's date-0/date-1 pure-time values are 1 and 2.

At cap `(2,2,2,2)`, players 0, 2, and 3 have Quit value 0 and Continue value 2
against every opponents' root.  They therefore Continue surely in every exact
root Nash profile.  Against those three continuing players, player 1 has Quit
value 1 and Continue value 2.  All Continue is consequently the unique exact
root.  The pure singleton `{1}` is an exact terminal Nash profile, so the table
is not a hard-residual or positive-gap example.  It is nevertheless a valid
exact falsifier of the stated local implication.

This calculation uses the full behavioral cap, not a stationary cap.

## 2. Renewable maximal descent: strongest surviving theorem

The following reduction is mathematically sound.

Let `S_0` be an actual `QuittingPaidCapLiftedSource` with positive global
minimum `D_*`, a reset owner of zero terminal debt, and positive retained
opponent incidence.  As long as the source does not have unique all-Continue
at its cap, choose the canonical maximal-absorption exact cap root `x_n` and
prefix it to the actual source profile.  Put

```text
c_n = joint all-Continue mass of x_n,
beta_n = all-opponents-Continue mass for the paid observer.
```

Global positive minimality rules out `c_n = 0`; nontrivial maximal absorption
gives `c_n < 1`.  Exact cap-prefix semantics gives

```text
D(S_{n+1}) = c_n D(S_n).
```

The shifted pure-time payoff difference is multiplied exactly by `beta_n`,
and `beta_n >= c_n`.  One may therefore define the next stored positive lower
bound either as `beta_n g_n`, using a strengthened canonical wrapper, or as
`c_n g_n`, exactly as the current construction in
`Research/Quitting/PaidCapMaximalOneStepRegeneration.lean` does.  The latter is
already enough.  In either convention,

```text
g_N >= g_0 * product_{n<N} c_n.
```

Since every descendant is an actual profile,

```text
product_{n<N} c_n = D(S_N) / D(S_0) >= D_* / D(S_0) = kappa > 0.
```

It follows that `g_N >= kappa g_0`.  An atom inherited from the original
suffix survives all new prefix roots with mass at least its old mass times the
same product, so its mass is at least `kappa mu`.  Also

```text
sum_n (1-c_n) <= -log(kappa).
```

The reset debt, positive incidence, actual joint carrier membership, and a
fresh fixed-law reset dispatch are preserved by the checked one-step theorem.
Thus dependent iteration gives the honest alternative:

```text
eventual unique all-Continue at a descendant cap
or
an infinite literal left-prefix orbit with summable root absorption,
uniformly positive paid lower bound, uniformly positive inherited atom,
and renewable paid/reset source data.
```

### Necessary wording correction

`MaximalOneStepPaidResetRegeneration` does not currently store an equality
between an arbitrary descendant's `gain` field and `beta_n` times the parent's
field.  Its constructor selects the conservative lower bound `c_n g_n`.
Therefore the packet must not call `g_{n+1}=beta_n g_n` an existing structure
identity.  It is a valid strengthened canonical construction, not a theorem
about every inhabitant of the present structure.  Alternatively, retain the
already checked `c_n g_n` choice; it proves the same noncollapse bound with no
new mathematical lemma.

This result is still not a well-founded rank, a near-return, a UE consumer, or
a contradiction.  It narrows the regeneration problem to consuming either
the paired unique-cap endpoint or the noncollapsing left-infinite orbit.  The
statement about applying the construction to both sides of a double port must
mean two independent alternatives; it does not preserve any new equality or
coherence between the two descendant orbits.

## 3. Exact counterexample to the two-clock theorem

Take a two-player quitting game with players `p` and `q`.  Set, symmetrically,

```text
r_p({p}) = 0,       r_p({q}) = -1/2,   r_p({p,q}) = -1,
r_q({q}) = 0,       r_q({p}) = -1/2,   r_q({p,q}) = -1.
```

For every `t >= 0`, let

```text
h_t = 1 / (2 + 2^t),
```

and let both players Quit at root `t` with probability `h_t`.  Define the
continuation value by

```text
v_t(p) = v_t(q) = -h_t.
```

The elementary recurrence

```text
h_{t+1} = h_t / (2(1-h_t))
```

gives, for player `p`,

```text
Quit_p(t) = (1-h_t) * 0 + h_t * (-1) = -h_t,

Continue_p(t)
  = (1-h_t) * v_{t+1}(p) + h_t * (-1/2)
  = -(1-h_t) h_{t+1} - h_t/2
  = -h_t.
```

The same holds for `q`.  Hence the displayed product root at every date is an
exact endpoint Nash root and the displayed `v_t` satisfies the exact Bellman
equation.  Since `v_t -> 0`, iterating the Bellman equation also identifies it
with the actual terminal payoff of this infinite behavioral root sequence;
the all-Never outcome has payoff zero.

All hypotheses in the written theorem hold:

- eventual support is exactly `{p,q}`;
- root absorption is `alpha_t = 2h_t-h_t^2 -> 0`;
- every suffix has positive eventual absorption (already its first root has
  positive absorption);
- the two singleton stage masses are equal, and each player's conditioned
  singleton share is uniformly bounded away from zero in every tail and every
  block; and
- `v_t -> (0,0)`, exactly the vector of own solo rewards.

Nevertheless,

```text
normalizedSoloMatrix(p,q) = -1/2,
normalizedSoloMatrix(q,p) = -1/2.
```

This is not merely a counterexample with the wrong sign.  Both entries have
the strictly negative sign forced by a card-two nonprojective hard principal.
The example need not itself satisfy the complete Fin4 hard residual: it
falsifies the universal two-clock theorem used as the adapter to that
residual.

## 4. Exact failure in the proposed block proof

The estimate `C_n = o(A_n+B_n)` is correct.  The invalid step is:

> Boundary tightness makes the left side `o(A_n+B_n)`.

Ordinary convergence

```text
v_t(p) -> r_p({p})
```

only makes the boundary error `o(1)`.  The block singleton mass `A_n+B_n` may
also tend to zero, and may do so on exactly the same scale.  In the explicit
counterexample, both the boundary error and the remaining singleton absorption
are of order `h_{s_n}`.  Their ratio does not vanish.

The Lean target makes the gap even more visible: it introduces `boundary` but
does not include a hypothesis that `value t` tends to `boundary`, let alone
the relative convergence required by the proof.

A correct conditional version may assume, for the chosen conditioned blocks,

```text
|v_{s_n}(p)-r_p({p})|
  + L_{e_n}|v_{e_n}(p)-r_p({p})| = o(A_n+B_n),
```

and the analogous condition for `q`.  Under this relative-tightness
hypothesis the displayed telescope proves the desired zero entries.  A simpler
sufficient condition is a fixed positive lower bound on the block singleton
mass together with ordinary boundary convergence.  Neither strengthening is
presently derived from the hard-residual source.

The block notation must also specify whether `L_t` is survival relative to
`s_n` or absolute survival from date zero.  The written telescope is correct
only after the corresponding normalization is made explicit.

## 5. The claimed hard-residual dispatch does not survive independently

Even aside from the counterexample, the four successor interpretations are
not established by the stated hypotheses.

- A vanishing conditioned singleton share is a clock/occupation statement,
  not automatically a strict positive-debt-support drop or a regenerated
  minimum source.
- Failure of boundary tightness is not automatically a uniform one-sided
  refusal gap.  `summable_selectedRefusalCharge_of_nash` requires one fixed
  player, a selected set of dates, one positive `delta`, the correct sign of
  `value - Quit`, and a global root-sequence Nash hypothesis.  Mere failure of
  convergence to a solo value supplies none of these quantifiers.
- Nondiffuse absorption may provide a concentrated row, but a connection from
  that row to the named positive-charge/cap-return consumer must be stated and
  proved with its source fields.  It is not a consequence of the four abstract
  hypotheses as written.
- No actual-source theorem is supplied which turns an arbitrary Fin4 hard
  residual and its card-two nonprojective principal into the exact infinite
  Nash--Bellman chronology assumed by the two-clock theorem.

Therefore the conclusion that only a three-or-more-clock diffuse tight
chronology remains is unsupported.

## Source audit

The relevant checked declarations are:

- `maximalOneStepPaidResetRegeneration_or_uniqueAllContinue` and the canonical
  descendant construction in
  `Research/Quitting/PaidCapMaximalOneStepRegeneration.lean`;
- the unrestricted terminal semantic debt prefix identities used there;
- `normalizedSoloMatrix_eq_zero_of_fencedSoloWindows` in
  `UniformEquilibrium/Quitting/Cycles/DiffuseTailSoloStructure.lean`, which has
  a genuinely stronger recurrent charged-window input than the false theorem;
- `negative_offDiagonal_of_pair_nonprojective` (private, used by the public
  card-two crossing theorem) in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportHardPrincipalDispatch.lean`;
  and
- `summable_selectedRefusalCharge_of_nash` in
  `UniformEquilibrium/Quitting/Classification/Existence/GlobalRefusalLedger.lean`.

The checked card-two sign calculation agrees with the counterexample's sign
pattern.  No declaration found supplies the missing relative boundary
tightness or the claimed hard-residual chronology adapter.

## Required repairs before any export

1. Remove the current follow-up theorem and every claimed consequence derived
   from it.
2. Split the local unique-root example and renewable maximal-orbit reduction
   from the false diffuse-tail section.
3. State the maximal-orbit gain field honestly: use the existing canonical
   `c_n g_n` lower bound, or build and prove a new `beta_n g_n` wrapper.
4. Give the reduced orbit object every actual source, row, atom, reset, and
   fixed-law dispatch quantifier explicitly, and state that its consumer
   remains open.
5. If a two-clock theorem is retained, add relative boundary tightness (or an
   equivalent nonvanishing absorption condition), include actual convergence
   to `boundary`, and provide an arbitrary-hard-residual source adapter.
6. Re-audit the support-drop, concentrated-charge, and refusal-ledger branches
   separately; none follows merely by negating the current five hypotheses.

## Strongest surviving export candidate

After separation and review, the defensible new result is:

> Every canonical maximal paid/reset regeneration chain either reaches a
> descendant whose exact cap-root set is uniquely all Continue, or is an
> infinite literal source-preserving left-prefix orbit whose total prefix
> absorption is summable while one paid-row lower bound and every chosen
> inherited suffix atom remain uniformly positive.  This still requires a
> causal return/realization consumer.

Together with the exact four-player local model, this strictly identifies why
the paid row and atom alone cannot consume the unique-cap endpoint.  Whether
that reduction alone meets the export gate should be judged against the named
regeneration question after it is rewritten as a standalone packet; the
present `HARD_RESIDUE.md` does not.
