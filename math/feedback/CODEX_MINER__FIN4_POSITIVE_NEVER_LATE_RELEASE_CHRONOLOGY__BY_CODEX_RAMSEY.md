# Review of `CODEX_MINER__FIN4_POSITIVE_NEVER_LATE_RELEASE_CHRONOLOGY`

**Reviewer:** `CODEX_RAMSEY`  
**Verdict:** **REVISE -> PASS after bounded statement/proof-handoff repairs**  
**Mathematical core:** PASS  
**Export assessment:** internal Research/formalization candidate only; the release row is not an exact Nash--Bellman or punishment-floor edge.

## Claim reviewed

I independently checked the claimed passage from a globally minimizing `Fin 4`
joint semantic/law point with positive `Never` mass to a same-source packet
consisting of:

1. an arbitrarily deep exact cap--Nash prefix on an actual near-minimum source;
2. the previously selected finite suffix atom before a late cutoff;
3. a legal finite-cap replacement of one fixed positive-solo owner;
4. a later singleton atom of mass at least `q/4` and prescribed-payoff gain at
   least `Gamma*q/4` after the common exact prefix;
5. signed opponent debt transfer at least `Gamma*q/8`, hence one fixed
   recipient of increase at least `Gamma*q/24`; and
6. application of the checked endpoint atom decoder, without claiming that
   the moved endpoint is another exact Bellman state.

## Independent calculation

Let `T_i` be the independent live-path stopping clocks of one supplied
profile and cap player `a` at date `N`.  The discrepancy partition is:

- if **some** opponent stops before `N`, source and capped target agree up to
  absorption;
- if every opponent is `Never`, the only changed payoff occurs when `a` was
  also `Never`, and is exactly the singleton reward `s_a`; and
- every remaining possible discrepancy lies in
  `E_N={N <= min_{j != a} T_j < infinity}`.

Thus, with `Omega` bounding terminal payoff differences,

```text
U_a(capped_N)-U_a(source) >= s_a*q_source-Omega*P(E_N).
```

The events `E_N` decrease to the empty event.  The target singleton mass at
date `N` is

```text
Surv_a(N) * product_{j != a} Surv_j(N+1),
```

up to the repository's equivalent survival indexing, and tends to the joint
`Never` mass.  This verifies the late-release limit, including arbitrary
diffuse clocks and clocks with finite mass below one.  The finite cap is a
legal behavioral strategy by
`quittingStoppingLawFiniteCapBehaviorStrategy`.

The mover's unrestricted envelope depends only on the opponents.  Since the
replacement changes only `a`, its cap is unchanged and

```text
d_a(target)=d_a(source)-(U_a(target)-U_a(source))
```

is exact.

For the root word, exact transport through the common prefix multiplies every
suffix event mass and every source--target payoff difference by its joint
Continue product `c_n`.  From
`capNashStack_continueProduct_lowerBound`,

```text
D_*/D(sigma_n) <= c_n <= 1,
```

and `D(sigma_n)->D_*>0`, so `c_n->1`.  Eventually `c_n>=1/2`, giving exactly
the stated `m/4`, `q/4`, and `Gamma*q/4` constants.

Finally, `minimumReference_opponentTransfer_of_coordinateDecrease` is indeed
the signed-transfer statement needed here, not merely a positive-part bound:

```text
g_n <= D(P_n)-D_* + sum_{j != a}(d_j(Q_n)-d_j(P_n)).
```

With `D(P_n)-D_*<=Gamma*q/8` and `g_n>=Gamma*q/4`, the opponent sum is at least
`Gamma*q/8`.  Among the three other `Fin 4` labels, one signed increase is at
least `Gamma*q/24`; finite-label subselection fixes it.

For `card (QuittingTerminalOutcome (Fin 4))=16`, the direct decoder arm has
atom at least

```text
(Gamma*q/24)/(2*16)=Gamma*q/768,
```

and the rectangle arm at least

```text
(Gamma*q/24)/(4*16)=Gamma*q/1536.
```

The scales and inequality orientations in the note are correct.

## Source/provenance checks

- `finFourHardResidual_minimumLaw_causalSuffixAtom` applies to the **same
  supplied minimum-law point**, so the positive finite atom is available even
  in the positive-`Never` arm.  This is stronger than the generic exclusive
  `Never`-or-atom dispatch and resolves the apparent conjunction risk.
- Joint convergence gives both `Law(sigma_n)(none)->q` and
  `D(sigma_n)->D_*`.
- The finite atom remains in the declared suffix.  Prefix transport does not
  promote it into one of the exact root rows; the note preserves this scope.
- `Q_n` changes only player `a` relative to `P_n`, so it is a legitimate
  endpoint deviation and the direct theorem
  `hasQuittingEndpointDebtRecipientAtom_of_pos` applies to the fixed positive
  recipient after subselection.
- No statement in the proof makes `Q_n`, its release row, or the returned
  decoder atom an exact Nash--Bellman edge.  The final nonclaim is essential
  and correct.

## Required repairs

1. In Section 3 replace “If every opponent stops before `N`” by “If **some**
   opponent stops before `N`.”  The displayed event partition and proof use
   the latter statement.

2. Qualify Theorem 4.1(2).  The finite-cap strategy copies the original
   **live-path hazard** before `N`; it need not equal the original arbitrary
   behavioral prescription at unreachable histories.  State that `P_n` and
   `Q_n` share the literal root word and agree on the live path through the
   suffix window, hence have identical stage-event/payoff contributions
   there.  Do not claim unqualified equality of the two behavioral strategies
   through that window.

3. Preserve indexing under recipient subselection.  Either retain an infinite
   cofinal set `J` of the original indices, so `(R_n).length=n+1` for `n in J`,
   or reindex and weaken the displayed depth statement to
   `(R'_k).length>=k+1`.  Relabeling a subsequence does not literally preserve
   equality with the new index.

4. In Corollary 4.2 explicitly set the endpoint target strategy to `(Q_n)_a`
   and record `Function.update P_n a (Q_n)_a=Q_n`.  If a single fixed decoder
   alternative as well as a fixed coalition label is desired, take one more
   finite subsequence over the two alternatives.  The uniform weaker atom
   scale `Gamma*q/1536` itself does not require fixing the alternative.

These are bounded repairs; none changes the theorem's constants or its
source-matched mathematical conclusion.

## Exact disposition

After the four repairs, I find no mathematical objection.  The result is a
genuine positive-`Never` chronological producer: it aligns a deep exact
**source** prefix, an earlier retained atom, and a later fixed-gain endpoint
move on one literal profile.  It remains internal because the final release
is only an unrestricted endpoint deviation.  The note correctly does not
claim a punishment-floor edge, cumulative charged return, regenerated
minimum source, or uniform payoff.

---

## Delta review: common-quantile finite-support strengthening

**Delta verdict:** **PASS; no mathematical repair required.**  The exact
finite-support release identities are a valid strengthening of the reviewed
asymptotic splice.  One duplicated line in Corollary 4.2 should be deleted
ministerially.

### Compression and law provenance

Start with any joint-law realizing sequence `rho_n` for the same supplied
minimum point `(z,mu)`.  Apply
`quittingQuantileClockCompressedProfile reward rho_n level_n` with positive
`level_n -> infinity`.  The checked bound
`hasEscapeAwareQuantileClockCompressionAtRewardBound` is uniform in the
source profile, so its semantic radius tends to zero.  Hence

```text
Sem(compress(rho_n,level_n)) -> z.
```

For every player, `quittingQuantileClockCompressedLaws_none` preserves that
player's `Never` atom exactly.  Independence therefore preserves the joint
all-`Never` coordinate exactly at every `n`, before passage to the limit:

```text
Law(compress(rho_n,level_n))(none)=Law(rho_n)(none) -> q.
```

The fixed finite-coalition coordinate also converges, although this exact
indicator statement is not itself the displayed payoff-compression theorem.
Couple the original product clocks to their coordinatewise active quotient.
Off `hasEvenSomeCollision` in a common unmarked cell, the quotient preserves
the order of distinct cells, preserves marked-date ties exactly, and hence
preserves the earliest coalition.  Thus the two indicators of the event
“terminal coalition is `S`” agree off the bad event, and

```text
|Law(compress(rho_n,level_n))(some S)
    - Law(rho_n)(some S)|
  <= P(hasEvenSomeCollision)
  <= quantileClockCollisionBudget (Fin 4) level_n -> 0.
```

Together with `Law(rho_n)(some S)->m`, this proves the claimed compressed-law
convergence.  This is a direct ordinary corollary of the checked active
quotient, product pushforward, and collision-mass declarations in
`EscapeAwareQuantileClockHierarchy.lean` and
`EscapeAwareQuantileClockCollision.lean`; formalization should package it as
an explicit outcome-indicator lemma rather than cite the payoff bound alone.

`quittingQuantileClockCompressedLaws_isFiniteClock` gives one common finite
bound: every positive finite clock atom is strictly below
`quantileClockSupport (Fin 4) level_n`, with `Never` retained separately.
Consequently a cutoff `K_n` above the entire finite support exists exactly as
claimed.

### Fresh roots and exact release

The note correctly chooses a **fresh** exact cap--Nash word only after the
profilewise compression.  No root selected for the original realizer is
reused.  For each compressed suffix `sigma_n`, choose a word of length
`n+1`.  Since `D(sigma_n)->D_*`, the exact debt scaling and global-minimum
lower bound squeeze the freshly prefixed debt to `D_*`; equivalently,

```text
D_*/D(sigma_n) <= continueProduct(R_n) <= 1,
```

so the Continue product tends to one.  The finite-support replacement does
not lose minimum provenance.

If every finite atom is strictly below `K_n` and player `a` is capped at
`N_n>=K_n`, the source and target differ only on the literal joint-`Never`
event.  Therefore both strengthened identities are exact:

```text
U_a(sigma_n^[a,N_n])-U_a(sigma_n)=s_a*q_n,
Mass_{ {a} }(sigma_n^[a,N_n],N_n)=q_n.
```

Likewise all original finite `C`-mass is realized before `K_n`, where the
live hazards are unchanged, proving (3.2').  Prefix transport multiplies
these exact suffix quantities by the same Continue product.  The previously
reviewed `m/4`, `q/4`, `Gamma*q/4`, transfer, and decoder constants therefore
remain valid without alteration.

### Ministerial/source-handoff comments

1. Corollary 4.2 currently repeats the sentence fragment “at least
   `Gamma*q/768` in the prescribed-difference arm). The counterfactual”
   twice.  Delete one copy.
2. In a Lean handoff, distinguish the checked collision coupling from the
   new outcome-law indicator corollary just described.  The latter is fully
   justified but should not be presented as an already named declaration.

The strengthened result retains the same strict scope: the exact late cap is
a legal endpoint deviation after an exact **source** chronology, not an exact
Nash--Bellman release row.

### Final ministerial delta: reindexed depth and source wording

**Verdict:** **PASS.**  Defining
`ell_n=(R_n).length=subseq(n)+1>=n+1` resolves the former subsequence defect.
The theorem now uses the actual length `ell_n` in both shifted stage formulas,
`ell_n+t` and `ell_n+N_n`; no stale `n+1` stage offset remains.  The source
word is still exact for its compressed suffix, and its depth remains cofinal.

The revised introduction and Theorem 4.1(2) also make the correct assertion:
source and target share the literal live-path root word and pre-cutoff
live-path hazards, while no equality at unreachable histories is claimed.
Section 9 now labels the outcome-indicator coupling as a proposed new Lean
declaration rather than an existing checked fact.  These changes discharge
all substantive repairs in the base and delta reviews.

Two phrases are now merely redundant and may be cleaned up without further
review: because Theorem 4.1 is stated after the recipient subsequence and
common reindexing, item 6 can replace “after a further subsequence there is
one fixed `b`” by “there is one fixed `b`”; similarly Corollary 4.2 can say
“use the fixed recipient `b`” rather than select it again.  This redundancy
does not affect the theorem's quantifiers or correctness.
