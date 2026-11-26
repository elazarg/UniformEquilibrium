# Final independent review of retained global finite-block regret rate

Reviewer: GLOBAL_BLOCK_REVIEW. Date: 2026-10-28.
Artifact: `math/notes/CODEX_COORDINATOR__GLOBAL_FINITE_BLOCK_REGRET_RATE.md`.
SHA-256: `723b3b0c08c2e6c12b8749e18af415233688788b29d06616fee2119e6aca7072`.
Repository HEAD at retained review: `6b896ade6225e41d612de00d17c3dfb14fd81e30`.

**Verdict: pass as conditional ordinary mathematics, for internal retention.**
I reread these exact retained bytes. Relative to the independently reviewed
original draft, the sole change is its attribution/status sentence. There
is no unresolved mathematical objection; no Lean check or export is claimed.

The hypothesis is a genuine positive global minimum m of maximum full
unilateral regret over the closure of actual independent stopping-law
payoff/cap pairs. At every such minimizing pair, every h in
[0,m+m^2/(64M)]^4 and every finite normal-form timing block at continuation
W=B-h satisfy z>=a m^2/(64M), where z is complete block regret and a is
absorption probability. The same bound holds for all infinite auxiliary
stopping laws with literal AllNever payoff W.

The complete-cap ledger includes every block date, every tail response,
and Never. Whole-law repair preserves independence; its owner contraction
and outsider 4M theta bound are valid. The latter controls the extra late
response exposed by the repair. The finite-controller target index
K+L+1 is correct. In the ledger H_i means the absorbing contribution to
Continue, excluding the displayed D_i W_i continuation term.

Finite actual approximants exist by censoring remote finite mass to Never;
total variation controls all response payoffs uniformly and therefore
controls their supremum. Fixing the block while varying W avoids any
unsupported continuity assumption on equilibrium selection. Every repaired
actual law remains above m, which gives the claimed contradiction estimate.

Finite Nash existence first implies W_i>=r_i({i}). This makes all omitted
post-support finite responses weakly dominated by Never in each censored
auxiliary profile. Hence the finite cap is complete and the infinite-law
limit is valid. Zero absorption forces every marginal to be delta_Never;
uniqueness is at the stopping-law level, modulo irrelevant behavior after
absorption. No convergence of weakly escaping clocks is being asserted.

The bounded overlap audit found the one-stage repair in FRECHET's critical-
box note and whole-block transport for a different bonus-source objective
in NOETHER's whole-block note, but no duplicate of this exact all-block
unrestricted-MAX rate. HAHN's KKT notes and NOETHER's two-law checkpoint do
not supply its missing full-response producer. This is a modest extension
of existing accounting, not an independently new equilibrium mechanism.

Ordinary existence, index, or small perturbations do not force activation:
existing all-player ties and harmonic restrictions even imply W_i-s_i>=
95m^2/(64M)>0 throughout this box, so all Continue is uniformly strict.
That supporting observation is not needed for the reviewed theorem.

The remaining obligation is unchanged: use the same genuine global source
to produce h in the box and a finite independent block with a>0 and
z/a<m^2/(64M). Neither local bonus-source facts nor KKT stationarity can
replace global minimality. No such producer, source-class closure, or m=0
calibration is supplied. This review changes no tracked file or Git state.
