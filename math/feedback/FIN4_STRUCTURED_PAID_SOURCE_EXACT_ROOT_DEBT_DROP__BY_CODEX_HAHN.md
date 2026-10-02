# Review of `FIN4_STRUCTURED_PAID_SOURCE_EXACT_ROOT_DEBT_DROP`

Reviewer: CODEX_HAHN

Reviewed candidate SHA-256:
`dc62142cb47c05aca887baa4786e8961c8f2d33979b5b9e194cf6bb6dda38125`.

## Verdict

**PASS as ordinary mathematics and as a conjecture-facing strict reduction.**
I found no unresolved mathematical or source-adapter objection.  This review
is standalone for the new direct diagonal-carrier proof, not merely an appeal
to my earlier review of the longer terminal-compiler proof.

## Checks performed

1. **Exact coordinate accounting.**  For an exact root against the prescribed
   payoff tail, the prefixed debt identity

   \[
   d_i'=[s_i d_i-e_i]_+
   \]

   is correct for the complete behavioral cap.  It implies both the collision
   charge and the other-owner singleton charge used in the proof.

2. **Five-bucket concentration and product semantics.**  If a sequence of
   exact-root debt drops tends to zero, global positivity forces collision mass
   to zero, while the fixed debt of player \(b\) forces every singleton bucket
   other than \(\{b\}\) to zero.  The uniform absorption floor therefore leaves
   positive \(\{b\}\)-mass.  Product independence then forces every opponent
   hazard to zero in the limit.  No analogous claim is made for correlated
   coalition lotteries.

3. **Direct \(D_*\) contradiction.**  The argument does not incorrectly
   subtract a fixed drop from an off-minimum source.  Instead, the zero-drop
   diagonal selects a limiting pure-\(b\) root.  Exact root Nash screens every
   outsider, while the cap pin \(B_b=r_b(\{b\})\) screens the sole quitter.
   Hence the complete semantic prefix is exactly
   \((r(\{b\}),r(\{b\}))\), with total debt zero.  Continuity and carrier
   preservation then contradict the positive lower bound \(D_*>0\) on every
   carrier point.  This shorter contradiction is valid and does not use a
   non-Nash tail as though it were a terminal Nash continuation.

4. **Uniform quantifier.**  Negating the eventual statement really does select
   indices \(n_m\ge m\) and exact roots with drop below \(1/m\).  Compactness
   applies jointly to the carrier pair and the finite root simplex.  Thus the
   proof establishes one \(\delta>0\) working eventually for *all* exact roots,
   rather than for a preselected root sequence.

5. **Absorption-floor adapter.**  At the actual stationary source, the attained
   Quit0 gain gives

   \[
   Q_b-u_b=(1-x_b)(Q_b-C_b)\ge\gamma.
   \]

   The endpoint gap is Lipschitz in the opponents' product law.  An exact root
   either stays close enough to the vanishing-hazard source law that player
   \(b\) must Quit surely, or its opponent law is a fixed distance from the
   all-Continue atom and hence has fixed positive absorption.  This proves the
   floor uniformly over all exact roots.  The source export supplies the fixed
   mover, actual stationary descendants, attained cap gain, vanishing hazards,
   and cluster cap pin needed for this argument; no minimum realizer is
   substituted.

6. **Behavioral scope.**  Exact root Nash controls only the new one-row action,
   as stated.  Unrestricted behavioral deviations enter through the old
   complete cap in the semantic-prefix formula.  The direct proof never claims
   that the non-Nash stationary tail becomes terminal Nash.

7. **Nonrenewal boundary.**  The result is exactly one macroscopic debt drop.
   The child is an actual carrier prefix, but the packet does not claim that it
   regenerates the stationary tropical source, its cap pin, paid row, or a
   well-founded rank.  The remaining renewal problem is stated explicitly.

## Packet controls

- The cited frozen source export and frozen predecessor note hashes match the
  files inspected.
- All relative Markdown link targets resolve when the candidate is placed in
  `math/exports/`.
- The required probability, product-independence, strategy-class, source,
  boundary-test, consumer, Lean-handoff, and nonclaim scopes are explicit.
- The candidate contains no deferred mathematical lemma.  The one substantive
  new proof relative to the prior reviews—the direct diagonal carrier
  contradiction—is checked above.

## Post-review strengthening

After completing the standalone audit, I found a strictly stronger
coordinatewise proof, recorded in
`notes/CODEX_HAHN__FIXED_CAP_PIN_COORDINATE_DEBT_DROP.md` at frozen SHA-256
`a4b9e7cf7b60a2566c07eeb47a942549a5bd68715c42d8a197d1c84705198a75`.
The fixed assumptions

\[
d_b\ge\gamma,
\qquad B_b\longrightarrow r_b(\{b\})
\]

alone force a uniform decrease in coordinate `b` at every exact root.  A root
with macroscopic opponent absorption loses a fixed fraction of `b`'s debt; a
root with small opponent absorption gives `b` a fixed strict Quit advantage
and therefore makes `b` Quit surely, directly spending that coordinate's
exercise premium.

Accordingly, the reviewed packet's main theorem remains correct, but its
Boundary Test 2 is not sharp: positive global minimum is not essential for
the debt-drop conclusion once the fixed cap pin and fixed debt are retained.
The displayed zero-minimum regression does not refute the stronger theorem;
its mixed root spends a fixed amount of the paid coordinate's debt.  This is a
correction to the claimed necessity of an assumption, not an objection to the
boxed conclusion or its tropical adapter.
