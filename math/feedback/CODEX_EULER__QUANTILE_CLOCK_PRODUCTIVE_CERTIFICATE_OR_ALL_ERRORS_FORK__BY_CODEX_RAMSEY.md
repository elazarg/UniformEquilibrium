# Review of the quantile-clock productive certificate-or-all-errors fork

**Reviewer:** `CODEX_RAMSEY`  
**Object reviewed:**
[`CODEX_EULER__QUANTILE_CLOCK_PRODUCTIVE_CERTIFICATE_OR_ALL_ERRORS_FORK.md`](../notes/CODEX_EULER__QUANTILE_CLOCK_PRODUCTIVE_CERTIFICATE_OR_ALL_ERRORS_FORK.md)  
**Verdict:** **PASS as ordinary mathematics; retain internal as an operational
corollary of the exported hierarchy.**

## Claim checked

At a finite outer level `R_M`, decide the exact semialgebraic query

\[
 z\in R_M,\qquad F(z)=0.
\]

Feasibility retains the current-scale actual finite-clock center `a_M` and
therefore emits an executable profile of exploitability at most
`2 n(n-1)/M`.  Infeasibility gives an effective positive rational lower
certificate on `R_M`.  Running this at the cofinal scales
`M_k=max(1,2n(n-1)2^k)` halts exactly when the actual terminal
exploitability infimum is positive; otherwise it emits an all-errors stream
consumed by the checked terminal-Nash-to-uniform-payoff theorem.

## Independent checks

### 1. Exact zero query, including negative raw outer debts

The equality query is correct.  The outer systems do not impose
`B_i-U_i>=0`, so `F(z)=0` means only

\[
 B_i(z)-U_i(z)\le 0\quad\text{for every }i.
\]

This causes no gap.  The extended `R_M` witness contains an actual center
`a_M` with `||a_M-z||_infty<=delta_M`.  Since `F` is `2`-Lipschitz,

\[
 F(a_M)\le F(z)+2\delta_M=2n(n-1)/M.
\]

At the actual center the raw debts are nonnegative and `F(a_M)` is exactly
unrestricted terminal exploitability.  Thus the argument does not silently
interpret a negative-debt outer point as an executable semantic pair.

Compactness of `R_M` and continuity of `F` also justify the converse finite
alternative: infeasibility of `F=0`, together with `F>=0`, is equivalent to
`L_M>0`.

### 2. Current-scale source attachment

The construction uses the center belonging to the `m=M` neighborhood
witness, not an independently reselected point.  Its marginal simplex
variables define a genuine finite product stopping law.  Exact `Never`, the
product coalition monomials, the after-support pure time, and the finite max
graph are all retained from the exported hierarchy.  Stopping-law
reconstruction therefore gives a behavioral profile, and pure-time
extremality upgrades its displayed cap to arbitrary behavioral deviations.

The source claim is consequently valid but deliberately weak: the centers
at different scales are not Bellman-linked or profile-prefix-related.

### 3. Effective rational certificate

Once `F=0` is infeasible, `L_M>0`.  Enumerating positive dyadic rationals and
deciding

\[
 \exists z\in R_M:\ F(z)<\gamma

\]

must eventually find a dyadic `0<gamma<=L_M`; strict inequality is harmless,
including when `gamma=L_M`.  Each query is a finite rational RCF sentence.
The feasible branch likewise has an algebraic sample containing all of the
current-scale marginal variables.  Thus the claimed finite certificate and
algebraic reconstruction are effective; no optimizer for `eta` is hidden in
the argument.

### 4. Halting semantics

If the process halts, its certificate gives `eta>=gamma>0`.  If it runs
forever, the emitted actual profiles have exploitability at most `2^-k`, so
`eta=0`.  Conversely, `eta=0` forces every `L_M=0` from
`0<=L_M<=eta`, hence every equality query is feasible.  If `eta>0`, monotone
convergence `L_M -> eta` and cofinality of `M_k` force a positive finite
level, so the process halts.  There is no circular choice of a scale from
unknown `eta`.

For `n=1`, `c_n=0` and the constant scale `M_k=1` is appropriate: a lone
player has an exact terminal best response (Quit immediately when its
singleton reward is nonnegative, Never when it is nonpositive), so
`eta=0`; the emitted bound is exactly zero.

The named declarations in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`
do give both required directions between terminal approximate Nash profiles
at every positive error and existence of a uniform-equilibrium payoff.

## Novelty and disposition

The theorem is not a new mathematical approximation hierarchy and not a
terminating zero test.  The exported hierarchy already contains the finite
centers, the lower/upper bracket, and convergence.  The new contribution is
the clean online algorithmic packaging: query exact zero, retain the
co-realized current-scale center in the zero arm, and prove the exhaustive
finite-certificate/infinite-all-errors operational semantics.

That is useful and source-correct, but it is best retained as an internal
consumer or formalization corollary rather than exported as a second
standalone research packet.  It neither decides the zero branch in finite
time nor changes the live Fin4 hard-residual question.

