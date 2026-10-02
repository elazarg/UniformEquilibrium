# Review of periodic complementarity and passive padding

**Reviewer:** `CODEX_NEGATIVE_CERTIFICATE`  
**Verdict:** **PASS**, with one mandatory wording correction and two useful
proof-expansion requests  
**Object reviewed:**
`notes/CODEX_SPINOZA__PERIODIC_COMPLEMENTARITY_AND_PASSIVE_PADDING_NO_GO.md`

## Claim checked

The note claims the following ordinary-mathematics projection result.  If a
one-dummy passive padding of a zero-Never quitting game has an exact finite
`IsQuittingBlockCertificate`, then deleting the dummy from its periodic rows
and values gives a bounded completely absorbing inverse iterate of the old
game.  Applying this to Solan's three-player table, for an existentially
chosen sufficiently small rational positive perturbation, produces a
four-player rational table with no exact admissible finite cyclic
Nash--Bellman certificate of any period.

I checked the projection independently against the current definitions in
`BlockPeriodicProfile.lean`, `AdmissibleCycleTerminalEquilibrium.lean`,
`PassivePlayerPadding.lean`, and `UnboundedInverseIterate.lean`, and checked
the source-dependent last step against
`../literature/SOLAN_2001__CLEANED_TEXT.md` and the boundedness diagnosis in
`UnboundedInverseIterate.lean`.

## Projection audit

### 1. Dummy admissibility gives old-player contraction

At the dummy coordinate the second branch of `admissible` is

```text
0 <= paddedReward({d})_d = -P,
```

which is false for `P>0`.  The first branch is exactly the product of the
phase continuation masses after deleting the dummy's coordinate.  For one
dummy this is `prod_k A_k<1`.  This use is correct and cannot be replaced by
the certificate's full-profile `absorb` field.

### 2. Dummy refusal and the identity `x_k A_k=0`

The certificate's `absorb` field makes the finite padded cycle absorbing:
one phase has continuation mass below one and all phase masses lie in
`[0,1]`.  Consequently its cyclic Bellman solution is the terminal mixture.
All dummy terminal rewards are `0` except dummy-only absorption, which pays
`-P`; hence every displayed dummy value is at most zero.

If the dummy switches to Never, its opponents are precisely the old players.
Their one-turn product is below one by the previous paragraph, so their
periodic repetition absorbs almost surely.  Every old-containing terminal
coalition pays the dummy zero, hence this refusal has value exactly zero.
The checked admissible cyclic response comparison therefore bounds the
dummy's refusal by its prescribed value, phase by phase, giving the reverse
inequality.  Thus every dummy value is zero.  Substitution in the dummy
Bellman equation gives

```text
0 = -P*x_k*A_k,
```

and `P>0` gives `x_k*A_k=0` at every phase.  I found no dummy-refusal
counterexample, including phases with `A_k=0`: those phases already make the
identity automatic.

For a formal handoff, the note should name the exact route used here rather
than compressing it to "exact cyclic complementarity": convert the block
certificate to its cyclic continuation block/root Nash data, identify the
displayed values with cyclic terminal values using absorption, and apply
`quittingCyclicHazardTerminalValue_le_of_isZeroRootNash_of_admissible` to the
dummy's identically-Never hazard.  This is an exposition request, not a gap.

### 3. Bellman projection

Conditioning on whether the old part is empty gives, for every old player,

```text
F_padded((p^k,x_k),v^(k+1))
  = F_old(p^k,v^(k+1)) + x_k*A_k*(H_i-v_i^(k+1)).
```

The last term vanishes by `x_k*A_k=0`.  This matches the checked old-part and
fresh-only reward identities in `PassivePlayerPadding.lean`.

### 4. Complementarity projection and the sure-Quit boundary

For an old player `i`, its forced-Quit endpoint is unchanged because the old
part of the terminal coalition is then nonempty.  Its Continue endpoint has
the extra dummy-only term, so

```text
g_old = g_padded + x_k*A_(k,-i)*(H_i-v_i^(k+1)).
```

The displayed old value is a terminal mixture of old rewards bounded above
by `H_i` and the dummy-only reward `H_i`, hence `v_i^(k+1)<=H_i`.

If `p_i^k<1`, the identity

```text
x_k*A_k=x_k*(1-p_i^k)*A_(k,-i)=0
```

forces `x_k*A_(k,-i)=0`; the old and padded gaps coincide.  If `p_i^k=1`,
the projected Continue clause is vacuous, while the padded Quit clause gives
`g_padded>=0` and the correction is nonnegative, so `g_old>=0`.  Thus the
sure-Quit case is handled correctly.  This is exactly the case that would be
lost by an on-path-mass-only argument.

### 5. Boundedness and complete absorption

Periodic repetition of the projected values inherits the certificate's
finite reward-box bound.  Repetition of the old rows has one-turn survival
factor `A<1`, so its survival prefixes tend to zero.  The projected Bellman
and complementarity equations are exactly the fields of
`IsQuittingInverseIterate`.  Theorem 3.1 is therefore sound.

## Source-dependent Solan step

The source table in (4.1) matches Solan's Figure 1 without the factor-three
normalization used by `UnboundedInverseIterate.lean`.  For a sufficiently
small positive parameter, the corrected **bounded** content of Theorem 2.1
excludes a bounded completely absorbing admissible sequence.  That is the
only source result the projection uses.  The known unbounded inverse iterate
does not affect a finite periodic certificate because its repeated values
are bounded.

Choosing the parameter rational by density is legitimate, and `epsilon<2`
makes `(3,3,3)` a coordinatewise upper bound.  The padding table is then
rational and the projection contradiction excludes every finite period,
not only periods at most four.

## Mandatory correction

The sentence after (4.3), "This is an explicit rational four-player quitting
table," overstates what the source supplies.  No numerical sufficiently-small
threshold, and hence no particular rational parameter, is identified.  The
result is an **existence theorem for a rational table given by an explicit
parametric formula**, not a displayed concrete rational table.  Replace that
sentence accordingly and avoid the word "explicit" for the selected table in
the headline/status unless the parameter is later isolated numerically.

## Scope confirmed

The result excludes exact finite absorbing punishment-admissible block
certificates.  It does not exclude approximate cycles of growing period,
non-admissible exact blocks, or uniform-equilibrium payoffs.  The final
counterexample remains literature-dependent and is not currently a checked
Lean theorem.  Subject to the wording correction above, I found no
mathematical objection.

## Final candidate delta and freeze review

**Verdict: PASS** for the export-format candidate
`/tmp/PASSIVE_PADDING_PERIODIC_CERTIFICATE_NO_GO.md` at exact SHA-256
`81f516947626dbd2c426b06a1d2e5f166e86c510d5ae700193c8c01259810101`.

I rechecked the complete candidate, not only the prose delta.  The mandatory
wording repair is present: Theorem B asserts an existentially chosen rational
parameter in an explicit parametric formula and does not pretend that the
source supplies a numerical threshold.  The dummy-refusal step now names the
checked conversion to a cyclic continuation block, identification of the
displayed Bellman word with cyclic terminal values under absorption, and the
admissible unrestricted cyclic response comparison.  This is the correct
orientation and yields `w^k >= 0`; the terminal mixture gives `w^k <= 0`.

The old-player complementarity identity retains the favorable nonnegative
correction in the sure-Quit case.  Theorem C now explicitly selects the
canonical upper endpoint required by the checked retraction theorem.  Its
pointwise exploitability inequalities imply the stated infimum sandwich and
the minimal-period inequalities, including the declared `+infinity` value
when the relevant period set is empty.  Projection and quiet lift preserve a
literal periodic live-hazard word without weakening the unilateral deviation
class.

The Solan dependency is restricted to the corrected bounded content of
Theorem 2.1.  Theorem 2.2 is explicitly untrusted and unused.  The positive
and negative boundary tests, consumer, Lean handoff, and nonclaims match the
proved scope.  All mandatory export headings are present, every relative link
resolves from `exports/`, and the file contains no control byte.  I found no
remaining mathematical, source, quantifier, or format objection at this
hash.

### Final two-line delta

**PASS** at corrected SHA-256
`47188fbd995d586305ff52a768808d99c78628a73d21a24465f5a07db0b23edd`.
Relative to the fully reviewed `81f51694...` body, the candidate adds the
resolved CODEX_SNELL review link and expands the canonical endpoint/width
notation as
`L_i=min(0,min_S r_i(S))`, `H_i=max(0,max_S r_i(S))`, and
`W=max_i(H_i-L_i)`.  These formulas exactly match the checked canonical
definitions.  No mathematical proof line changed; the new review link
resolves and the control-byte scan remains clean.
