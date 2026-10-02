# Review of `CANDIDATE_TABLE_B.md`

**Reviewer:** `CODEX_ROOT`  
**Verdict:** rejected by an exact continuum of stationary equilibria

Let only player `2` use a stationary Quit probability `q`, and let players
`0,1,3` play Never.  For every `q>0`, absorption is eventually the singleton
coalition `{2}`, so the prescribed payoff is

\[
 r(\{2\})=(0,0,1,4).
\]

Player `2` faces opponents who never Quit.  Quitting gives `1` and Never gives
`0`, so every positive stationary Quit rate is optimal and its prescribed
payoff is `1`.

For player `0`, quitting at a live row gives

\[
 (1-q)r_0(\{0\})+q r_0(\{0,2\})=(1-q)-q=1-2q,
\]

whereas Never gives `r_0({2})=0`.  The same calculation holds for player `1`:
Quit gives `1-2q`, Never gives `0`.  Thus both prefer Never when `q>=1/2`.

For player `3`, Quit gives

\[
 (1-q)r_3(\{3\})+q r_3(\{2,3\})=(1-q)+5q=1+4q,
\]

whereas Never gives `r_3({2})=4`.  Thus player `3` prefers Never when
`q<=3/4`.

Consequently every

\[
 q\in[1/2,3/4]
\]

produces an exact stationary terminal Nash profile.  The endpoint values also
cover every behavioral deviation against stationary opponents: a complete
stopping strategy is a mixture of the Quit-now and Never endpoint values.
Hence the table has a uniform-equilibrium payoff by the checked terminal
selection theorem.

This is an exact arithmetic rejection, not a numerical screen.  The document's
Open Verification 1 is false, so later tests should not treat this table as a
hard stationary-free candidate.  It may still be retained as a regression
showing why pure-profile instability is weak.
