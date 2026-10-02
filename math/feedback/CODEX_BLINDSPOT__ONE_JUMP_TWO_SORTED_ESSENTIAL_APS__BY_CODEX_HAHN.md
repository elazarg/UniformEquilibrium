# Review of one-jump, two-sorted essential APS

Reviewer: `CODEX_HAHN`

Source reviewed at SHA-256:
`2710c02fc5c134e9e6036e4537399d8cf03a290b8c68cf088c28e07a2c82d3b7`.

## Verdict

**PASS.** The two supplied-object closure theorems, the exact nonconvexity
example, and the execution-order qualifications are mathematically sound. The
note cleanly separates them from the proposed unrestricted two-sorted fixed
point.

## Checks

1. If terminal approximate-Nash realizers converge semantically to the
   diagonal pair `(y,y)`, continuity of exact root prefixing sends them to the
   diagonal `(F(x,y),F(x,y))`. Thus an exact root in front of a supplied
   uniform-equilibrium payoff preserves both payoff convergence and
   unrestricted behavioral exploitability. No absorption assumption is used.
2. In the proper singleton-flow mesh, `z_i=s_i` and `0<p<1` force `y_i=s_i`.
   The owner cap is therefore within the claimed tail error. For an outsider,
   the ideal continuation at every row lies on the viable segment from `y` to
   `z`; a pure Quit at that row gains at most `2Mh+eta`. Any complete
   behavioral stopping rule is a mixture over its first quitting row and the
   reached tail response, so there is no factor of `N` in the error.
3. A finite singleton-flow prefix reaches the exact jump tail with probability
   `1-p>0`. By contrast, a completed terminal-free unique-live component has
   zero limiting survival, so a jump placed after the entire component is
   payoff-invisible unless a new transfinite execution object is supplied.
4. In the two-player example, the endpoint difference is `-1+3p` against the
   opponent's Quit probability. The exact root set is precisely `(0,0)`,
   `(1/3,1/3)`, and `(1,1)`, with jump payoffs `(0,0)`,
   `(-1/3,-1/3)`, and `(1,1)`. This jump image is nonconvex even though all
   three points are uniform-equilibrium payoffs by root closure.
5. The note does not infer non-UE of convexified points. It correctly concludes
   only that convexification loses the joint root/continuation witness needed
   by the current supplied-object compiler.

## Scope retained

The proved grammar has a finite jump budget. Nothing here establishes
nonemptiness, coherent witness selection, or executable soundness for the
greatest fixed point of the unrestricted alternating jump--flow operator.
