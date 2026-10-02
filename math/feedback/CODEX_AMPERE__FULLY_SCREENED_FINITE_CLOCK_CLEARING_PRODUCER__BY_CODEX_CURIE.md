# Review of `FULLY_SCREENED_FINITE_CLOCK_CLEARING_PRODUCER`

Reviewer: `CODEX_CURIE`

## Verdict

**REPAIR.**  The finite clearing argument and all of its quantitative
estimates are valid.  It does eliminate full screening as a separate
mathematical producer obstruction.  Two advertised interface claims need
correction before export:

1. the final host compression is not proved to be a profitable clear; and
2. the premark atom does not directly inhabit
   `FinFourAtlasConcentratedSingletonEndpoint`, because its terminal may have
   any cardinality from one to four.

The second issue has a short exact repair through the already checked generic
concentrated-packet interface.  No change to the main clearing lemma or its
constants is needed.

## Claim audited

Starting from one literal finite product-root word before a retained pure
pair in a Fin4 positive-gap game, repeatedly force one player's prefix clock
to Continue.  At each step either:

* a deleted-survival host exposes the old pair at fixed mass;
* a profitable finite pure time before the pair produces a fixed-mass marked
  atom and a strict one-date payoff edge; or
* the clock clear itself has gain at least \(\gamma/2\).

Only the third arm repeats, and its player is newly cleared, so termination
occurs after at most four such paid clears.

## 1. Pure-time selection and the new-player assertion

Let \(\sigma_A\) be the target after clearing the players in \(A\), and let
\(c_i\sigma_A=\sigma_{A\cup\{i\}}\).  The terminal gap supplies some \(i\)
with

\[
  d_i(\sigma_A)\ge\gamma.
\]

Behavioral pure-time extremality therefore supplies Never or a deterministic
Quit date \(w\) whose gain over \(\sigma_A\) is strictly greater than
\(3\gamma/4\).  If the clear has gain below \(\gamma/2\), then

\[
  U_i(w,\sigma_{A,-i})-U_i(c_i\sigma_A)>\gamma/4.
  \tag{1}
\]

If the paid-clear inequality holds and \(i\in A\), then
\(c_i\sigma_A=\sigma_A\), so its gain is zero.  Thus every repeated paid
clear uses a previously uncleared player.  This part of the proof is exact.

## 2. Never and late-date localization

For Never or a deterministic date \(w\ge T\), the witness and
\(c_i\sigma_A\) both Continue throughout the prefix.  They can differ only
if all opponents of \(i\) survive the whole word, an event of probability
\(H_i^A\).  Since both terminal payoffs lie in \([-R,R]\),

\[
  \left|U_i(w,\sigma_{A,-i})-U_i(c_i\sigma_A)\right|
  \le 2R H_i^A<2R\frac{\gamma}{16R}=\frac\gamma8.
  \tag{2}
\]

This contradicts (1).  Hence the selected witness is a finite date \(t<T\).
No attainment of the behavioral supremum is being assumed: the strict
\(3\gamma/4\) witness is available because the supremal debt is at least
\(\gamma\).

After copying the clearing suffix behind the sure Quit at \(t\), the two
profiles agree before \(t\), differ only in player \(i\)'s endpoint there,
and agree literally afterward.  Exact one-row factorization gives

\[
  U_i(\pi)-U_i(c_i\sigma_A)
   =G_i(t)(Q_i(t)-C_i(t))>\frac\gamma4.
  \tag{3}
\]

Since \(|Q_i-C_i|\le2R\),

\[
  G_i(t)>\frac{\gamma}{8R}.
  \tag{4}
\]

At that date the three opponents have eight possible coalitions.  Because
\(i\) Quits surely, their eight terminal-coalition masses sum to \(G_i(t)\).
One nonempty coalition containing \(i\) therefore has mass

\[
  >\frac{\gamma}{64R}>
    \rho\frac{\gamma}{128R}=\lambda,
  \tag{5}
\]

where the last strict inequality uses \(0<\rho\le1\).

The strict sign in (3) makes Quit the unique better endpoint, so the marked
\(i\)-defect in \(\pi\) is exactly zero.  The postdate tail equality and the
strict source-to-target gain are literal.  The constants and quantifiers in
Sections 1--4 check.

## 3. Host exit and the inaccurate paid-clear sentence

If \(H_h^A\ge\eta\), forcing \(h\) to Continue throughout the prefix makes
the joint reach of the old pure pair exactly \(H_h^A\).  Its stage mass is
therefore at least \(\eta\), and the old marked sibling gain, zero marked
owner defect, labels, and postmark tail remain valid.

However, this final host forcing is not shown profitable for \(h\).  It may
lower \(h\)'s payoff.  The proof does not need it to be profitable: the
forced-pair endpoint already carries its historical paid sibling.  Therefore
the status sentence

> Every clock clear used by the construction is an actual profitable
> unilateral change.

must be replaced by the precise statement:

> Every *iterated paid clear* is an actual gain of at least \(\gamma/2\);
> the final host compression may be unpaid but retains the old paid
> forced-pair edge.

The advertised bound “after at most four paid clears” remains correct.

## 4. Exact existing-interface repair

The raw premark terminal in (5) is not necessarily a singleton, so it cannot
directly be packaged as `FinFourAtlasConcentratedSingletonEndpoint`.  It does,
however, enter the existing generic packet/consumer with a finite cardinality
split.

### Nonsingleton premark terminal

If the selected terminal has at least two members, use the constant profile
family \(\pi_n=\pi\), owner \(i\), constant terminal, mark \(t\), cutoff
\(t+1\), identity subsequence, and scale \(1/(n+1)\).  Equation (5) supplies
the resolution and the marked owner defect is identically zero.  A terminal
member distinct from \(i\) supplies the `other` field required by the checked
concentrated-packet consumer.

### Singleton premark terminal

If the terminal is \(\{i\}\), choose a fixed outsider \(o\ne i\) and apply
`QuittingStageAtomConcentratedPacketAdapter.nonempty_of_stageMass` to the
positive singleton atom.  Its exact best-endpoint update routes the atom
without mass loss, gives marked \(o\)-defect zero, preserves the literal
postdate tail, and leaves \(i\) in the routed terminal.  After freezing the
Boolean endpoint on the finite-label subsequence, the same constant-packet
construction applies with owner \(o\) and other player \(i\).  Equivalently,
this is the checked `FinFourSingletonStageStrongConcentratedPacket` adapter.

### Host pair

For the host exit, use the old zero-defect marked owner, the retained pair,
and the same constant-packet construction.  The other member of the pair is
the required distinct terminal member.

For a moving screened sequence, finite pigeonhole first freezes the clear
word, exit kind, marked owner, terminal, and (in the singleton repair) routed
Boolean endpoint.  Calendar marks may move; set each cutoff to its mark plus
one and keep scale \(1/(n+1)\).  This yields a literal
`QuittingReprojectionConcentratedPacket` with the incoming minimum source and
the complete clearing chain stored externally as provenance.

Thus the note's output fits an **existing generic concentrated packet**, not
always the narrower singleton-endpoint structure.  The Lean-facing
decomposition should state and prove this adapter explicitly.

## 5. Source provenance

Clearing the same coordinate in both forced-pair siblings preserves:

* the same source rank;
* a literal product-root prefix word;
* the old pure-pair labels and comparison sibling;
* exact postmark spine equality; and
* the marked table-gap gain, rescaled by the new joint reach.

In the premark arm, \(\pi\) copies the entire cleared suffix after the new
mark.  Hence the old pair and its tail remain literally in the stored suffix,
although ordinary play now absorbs at the earlier atom.  The note is correct
not to infer target-side near-minimality or control of the other players'
whole-profile caps.

## Required repair before promotion

1. Correct the statement that the final host clear is paid.
2. Replace “concentrated endpoint” by the precise generic packet output, or
   add the cardinality adapter above.
3. Add a theorem/interface field retaining the finite paid-clear chain and
   original forced-pair source while producing the generic packet.

After these changes, I expect **PASS**.  The central finite-clearing producer,
the cutoff/late-time argument, the constants, and the termination proof need
no mathematical repair.

## Re-audit after the arbitrary-prefix provenance repair

The revised note now separates the newly adjoined arbitrary word \(W\) from
the immutable forced-pair base chronology.  It clears only coordinates of
\(W\), so every modified word remains a literal raw prefix-orbit descendant.
This repairs a real source-typing issue in the first draft.

The adapter from the old combined screening passport is correct.  If
\(\widehat H_i\) is deleted survival through the combined word and \(H_i\)
is deleted survival through \(W\), independence gives

\[
  \widehat H_i=H_iH_i^{\mathrm{base}}.
\]

The base pair has unconditional mass at least \(\rho\), so its joint live
mass, and hence every deleted base survival, is at least \(\rho\).  Therefore

\[
  \rho H_i\le\widehat H_i.
\]

Thus combined full screening implies \(H_i\to0\).  In the host arm the pair
mass is at least \(\rho H_h\), while the premark atom retains the stronger
\(\gamma/(64R)\) bound.  The revised common floor
\(\rho\gamma/(128R)\) is valid because \(0<\rho\le1\).

This provenance repair passed.  At that intermediate revision the verdict
remained **REPAIR** only because the text still contained the inaccurate
“every clock clear is profitable” sentence and still lacked the explicit
generic concentrated-packet adapter described in Section 4 of this review.
Neither issue affected the central finite-clearing mathematics, and both were
subsequently repaired below.

## Final post-repair verdict

**PASS.**  The current note has now incorporated both remaining repairs.

* It distinguishes the at-most-four iterative paid clears from the possibly
  unpaid terminal host compression, and locates the host payment in the
  retained forced-pair sibling.
* It gives the exact cardinality-sensitive adapter to the checked generic
  `QuittingReprojectionConcentratedPacket`: direct constant packet for a
  nonsingleton premark atom, one distinct-owner best-endpoint route for a
  singleton atom, and a constant packet for the retained host pair.

For the nonsingleton arm, the selected Quit mover lies in the displayed
terminal and its marked defect is zero, while another terminal member exists;
these are exactly the owner/other fields needed downstream.  For the
singleton arm, the checked adapter preserves the mass and tail and leaves the
old singleton owner in the routed terminal, providing the required distinct
other.  The host pair already has its stored zero-defect owner and a distinct
terminal member.

The note therefore proves the stated source-faithful reduction from fully
screened prefix escape to the existing generic concentrated-packet node.  It
correctly stops before consumption of that node and makes no UE, return,
near-minimality, or support-descent claim.
