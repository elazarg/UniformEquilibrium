# Review of maximum-support common-chord exchange collapse

Reviewer: **CODEX_RAMSEY**  
Source:
[`CODEX_EULER__MAXIMUM_SUPPORT_COMMON_CHORD_EXCHANGE_COLLAPSE`](../notes/CODEX_EULER__MAXIMUM_SUPPORT_COMMON_CHORD_EXCHANGE_COLLAPSE.md)  
Verdict: **REVISE -> PASS after one routine Corollary 2.2 hypothesis repair;
Theorem 2.1 PASS; internal/no export**  
Date: 2026-08-26

## 1. Claim checked

Theorem 2.1 considers varying actual profiles `sigma_n` and one fixed mover's
complete replacement strategies `tau_n`, with

```text
Sem(sigma_n) -> X,
Sem(sigma_n[o <- tau_n]) -> Y.
```

Both limits lie on the same positive global minimum-debt fiber.  The theorem
forms the literal half stopping-law chord at every index, passes to a carrier
cluster `Z`, proves

```text
d(Z)=(d(X)+d(Y))/2,
supp_+(Z)=supp_+(X) union supp_+(Y),
```

and uses maximum support at `X` to conclude that a mover killed at `Y` gives
`supp_+(Y) ⊊ supp_+(X)`.

This theorem is correct.  It yields literal source regeneration through the
checked tangent-family re-extraction theorem when its hypotheses are actually
produced.  It does not by itself show that the forced-owner transfer output of
Miner's Proposition 8.1 has minimum-fiber endpoints.

## 2. Varying-source chord compactification: PASS

For each `n`, mix the two complete stopping laws of mover `o` with weight
`1/2`, leaving every opponent strategy equal to its strategy in `sigma_n`.
This is the actual behavioral profile produced by
`quittingStoppingLawMixtureBehaviorStrategy`, not a correlated random choice
between the two whole profiles.  Its semantic pair `Z_n` therefore belongs to
the actual semantic image.  Compactness supplies a subsequence converging to
some `Z` in the terminal-semantic carrier.

Coordinatewise stopping-law debt convexity gives

```text
d_i(Z_n) <= (d_i(X_n)+d_i(Y_n))/2.                 (2.R)
```

Semantic convergence of `X_n,Y_n` and continuity of each debt coordinate
allow passage to the limit.  Summing (2.R) gives `D(Z)<=D_*`, because both
endpoint limits have total debt `D_*`.  Carrier minimality gives `D_*<=D(Z)`.
Thus equality holds in the sum.

Every coordinate gap in (2.R) is nonnegative.  A finite sum of those limiting
gaps is zero, so every gap is zero.  Hence

```text
d_i(Z)=(d_i(X)+d_i(Y))/2
```

for every player.  This direct argument already proves (2.4).  The cited
near-minimum chord-gap theorem gives the same conclusion: take source excess
`D(X_n)-D_* -> 0` and endpoint rise `D(Y_n)-D(X_n) -> 0`.  There is no hidden
uniformity issue from the varying sources or replacements.

## 3. Support maximality and strictness: PASS

Every carrier debt coordinate is nonnegative.  Therefore the positive support
of the half chord is exactly the union:

```text
A(Z)=A(X) union A(Y).
```

The cluster `Z` lies on the minimum fiber.  Since `A(X)` was chosen with
maximum cardinality among minimum-fiber supports,

```text
|A(Z)| <= |A(X)|.
```

But `A(X) ⊆ A(Z)`, so finiteness forces equality of the two sets and therefore
`A(Y) ⊆ A(X)`.  The killed-mover assumptions give

```text
o in A(X),   o notin A(Y),
```

making the inclusion strict.  No attainment of `X` or `Y` by one fixed
profile is used.

The maximum-cardinality choice itself needs no compactness of a strict-support
stratum.  The minimum fiber is nonempty, and the set of support cardinalities
actually occurring there is a nonempty subset of the finite set
`{0,...,card I}`.

## 4. Literal regeneration: PASS under the stated hypotheses

Once `Y` is on the same positive minimum fiber, the theorem supplies exactly
the inputs of
`exists_reextracted_of_minimumFiber_of_supportSubset_of_vanished`:

- `Y` is in the carrier;
- `D(Y)=D(X)>0`;
- every positive debt label of `Y` lies in `A(X)`; and
- mover `o` belongs to `A(X)` but has zero debt at `Y`.

Starting with any tangent family based at `X`, the checked declaration returns
a new tangent family based at `Y` with strict positive-debt-support inclusion.
This is a genuine natural-valued rank decrease and is stronger than a static
label graph.  The new tangent array is re-extracted; no equality with the old
array or chronological continuation is asserted.

## 5. Mandatory Corollary 2.2 statement repair

As written, Corollary 2.2 says to keep hypotheses 1, 3, 4, and 5, dropping
hypothesis 2 wholesale and assuming only `D(Y)>=D_*`.  Its proof still needs
the following parts of hypothesis 2:

```text
X,Y belong to the carrier,
D(X)=D_*.
```

Convergence in hypothesis 4 can reprove carrier membership by closedness, but
`D(X)=D_*` must remain explicit.  The intended corrected statement is:

> Keep hypotheses 1 and 3--5, retain `X,Y` in the carrier and `D(X)=D_*`, and
> replace only `D(Y)=D_*` by `D(Y)>=D_*`.

Then a newcomer in `A(Y)\A(X)` excludes equality by Theorem 2.1, while global
minimality excludes `D(Y)<D_*`; hence `D(Y)>D_*`.  The eventual fixed positive
excess along an actual target subsequence follows from convergence.  This is a
routine statement repair, not a gap in Theorem 2.1.

## 6. Exact relation to the Proposition 8.1 transfer survivor

The theorem identifies the correct regeneration condition, but current
Proposition 8.1 does not automatically produce it.

At a selected forced-owner row, Proposition 8.1 has:

- a normalized actual source profile `S_n` with the terminal owner forced to
  Quit;
- a **half** best-endpoint reset `H_n` of an outsider; and
- either total debt descent or a signed aggregate transfer from `S_n` to
  `H_n`.

The common-chord theorem instead needs the full endpoint `E_n` and limits

```text
Sem(S_n)->X,  Sem(E_n)->Y,
D(X)=D(Y)=D_*.
```

The full endpoint does kill the selected outsider's debt at a sure-owner-Quit
root, but the transfer estimate was proved at the half endpoint.  Convexity
alone does not transport the half-endpoint opponent transfer to the full
endpoint.  More importantly, the forced-owner source pairs need not approach
the global minimum fiber at all.  Compactness gives clusters, but not
`D(X)=D_*`; the packet's original near-minimum semantic source was lost when
conditioning and forcing the owner to Quit.

Therefore the theorem gives a genuine consumer for the **common-chord,
two-minimum-endpoint subarm**, and exact re-extraction there.  Outside that
subarm, it leaves a fixed off-minimum forced-root or full-endpoint cluster,
which no current return/regeneration theorem consumes.  Finite player labels
cannot repair this source mismatch.

## 7. Cycle and novelty audit

Section 3 correctly distinguishes a literal reset cycle from a Nash--Bellman
cycle.  The checked finite full-best-endpoint word has positive root defects;
signed debt telescoping and semantic/profile recurrence do not supply exact
root Nash or successor-value identities.  Finite repetition of support labels
under independent re-extraction supplies neither equality of semantic points
nor target-to-next-source chronology.

The abstract tableau in Section 4 has the displayed scalar properties, and is
honestly labeled as neither a carrier nor a quitting-game realization.  It is
not evidence for or against `D_*>0` game existence; it only demonstrates why
the common-chord hypothesis is essential at the algebraic interface.

The support-union mechanism is already present in the reviewed positive-Never
four-corner theorem, and exact minimum-fiber chord affinity is checked in
`TerminalSemanticStoppingLawMinimumFiberAffine.lean`.  The reusable new
ordinary statement is the concise varying-source one-chord corollary together
with its direct strict-support re-extraction consequence.  This is a useful
internal lemma, but not a new resolution of the transfer survivor.

## 8. Disposition

**REVISE -> PASS after the Corollary 2.2 hypothesis wording is repaired.**
Theorem 2.1 and its re-extraction consequence pass without mathematical
repair.  I recommend internal status and optional direct formalization as a
small corollary of the checked minimum-fiber affinity and re-extraction
declarations.  No export is warranted until an actual producer proves that
the forced-owner source and full reset endpoint both converge to the global
minimum fiber, or consumes the resulting off-minimum excursion.
