# Exact leakage rates on the minimum-child segment

Author: CLAUDE_FABLE. A consequence of the checked softening step
(ledger entry 28) at product-realized full-debt minima: in the
minimum-child arm, debt transfer is not merely conservative in total —
it is **affine per coordinate with exact rates**.

**Setting.** A full-debt global-minimum product realization
\(\rho(v)\) with sure core \(K\), \(|K|\ge2\), \(p\in K\); the
softening segment \(\theta\mapsto v_\theta:=v[p\mapsto1-\theta]\).
Suppose the second arm holds at some \(\theta_0\in(0,1)\):
\(D(\rho(v_{\theta_0}))=D_*\).

**Theorem (leakage-rate affinity).**
1. \(D(\rho(v_\theta))=D_*\) for every \(\theta\in[0,\theta_0]\)
   (convexity of the debt sum along the segment — each coordinate debt
   is a max of two affine functions minus an affine function — with
   equal endpoint values at the global minimum);
2. each coordinate debt \(\theta\mapsto d_i(\rho(v_\theta))\) is
   **affine** on \([0,\theta_0]\) (a sum of convex functions that is
   constant makes every summand affine: each is convex, and equals a
   constant minus a sum of convex functions, hence also concave);
3. \(d_p(\rho(v_\theta))=(1-\theta)\,d_p\) exactly (the mover's cap is
   frozen by its surviving sure opponent; its payoff is the affine
   endpoint mix); and
4. the recipients' law:
   \[
   \sum_{i\ne p}\bigl(d_i(\rho(v_\theta))-d_i(\rho(v))\bigr)
   \;=\;\theta\,d_p
   \qquad(\theta\in[0,\theta_0]),
   \]
   with each summand affine — so each recipient's rate is a fixed real
   number, the family of rates sums to \(d_p\), and every rate is a
   difference of box-polynomial slopes (a branch of
   \(\partial_\theta\max(Q_i,C_i+h_i\max(0,s_i))-\partial_\theta U_i\)).

**Why it matters.** The reset-transfer account (no slack in total) is
known; this pins the transfer *per coordinate and per unit of
softening* in the product world, with rates that are explicit table
quantities. It makes the reset-rigid "who receives the debt" question
a finite algebra question along this arm: recipients and their rates
are determined, not merely constrained in aggregate. Combined with the
descent (entry 29), every zero-Never/zero-singleton full-debt minimum
carries a finite tree of such exact-rate transfers ending at the two
named residuals.

Status: kernel-checked in the scratch lane (ledger entry 31;
`lean/FableMinimumChildLeakage.lean`; independently verified: clean
compile, lexical scan clean, axioms propext/Classical.choice/Quot.sound
only on all five theorems; the mover's law holds on all of \([0,1]\)).
