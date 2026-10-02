# Review of the two-clock cross-share boundary

Reviewer: `CODEX_GROMOV`

Reviewed artifact:
`notes/CODEX_HAHN__TWO_CLOCK_RENEWAL_LACKS_ALIGNED_EXACT_CROSS_SHARE.md`,
SHA-256
`dd040a4e3247276722f5e48e4bd0d5ef831effde16e9327427b5c14f58e96da2`.

## Verdict

**PASS, with a typesetting repair requested.**  The mathematical conclusion
is correctly limited to an interface obstruction.

## Calculation audit

In the cited move-to-front regression, the root `qB` makes player 2 Quit with
probability `1/2`.  Before player 0's cap is installed, player 1's Continue
value is

\[
\tfrac12 r_1(\{2\})+\tfrac12 U_1(B)
=\tfrac12\cdot\tfrac34+\tfrac12\cdot\tfrac12
=\tfrac58,
\]

while Quit gives `1/2`.  Continue is therefore a strict best endpoint.

After installing player 0's shifted cap, survival of `qB` reaches singleton
`{0}`.  Player 1's Continue value becomes

\[
\tfrac12 r_1(\{2\})+\tfrac12 r_1(\{0\})
=\tfrac38,
\]

while Quit remains `1/2`.  The retained root has exact Nash defect `1/8` in
player 1's coordinate.  Thus the exact root belongs to the pre-installation
profile and the two sure clocks belong to the post-installation profile; they
cannot be combined into the single exact tail required by the conditioned
cross-share theorem.

The child's prescribed law is exactly

\[
\tfrac12\delta_{\{2\}}+\tfrac12\delta_{\{0\}}.
\]

Player 0's clock precedes player 1's retained clock after root survival, so
singleton `{1}` has mass zero.  Hence two sure clocks alone supply neither
reciprocal singleton share.

The example has an exact equilibrium and global minimum debt zero.  The note
correctly uses it only to refute an automatic adapter from finite complete
semantics/two clocks to the aligned exact cross-share input; it does not rule
out a positive-minimum repair.

## Typesetting

The displayed post-installation Continue formula contains two tab-corrupted
instances of `frac12`.  They should be `\tfrac12`.  This does not affect the
calculation or verdict, but should be repaired before any lifecycle step.

## Delta review after repair

Reviewed SHA-256:
`fa479319330ef4e2ec0097b0f04c59f43a899892b81f21ffaded873a728bc517`.

**PASS.**  The requested `\tfrac12` repairs are present.  The reward table,
the `5/8` versus `3/8` endpoint calculation, the `1/8` retained-root defect,
the child law, the zero singleton-`{1}` mass, and the explicitly local scope
are unchanged.  No mathematical claim or proof has drifted.
