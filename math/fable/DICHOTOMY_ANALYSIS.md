# The dichotomy question: statement and solution

Attempt document (analysis, with proofs). Fact base:
`FIN4_COUNTEREXAMPLE_DOSSIER.md` in this folder; facts are cited as R1–R14
and Facts 2.1–5.6 from there. Incorporates the corrections of
`../feedback/FIN4_COUNTEREXAMPLE_DOSSIER__BY_CODEX_ROOT.md`.

## Problem

Let \(P(4)\) be: every four-player quitting game has a uniform-equilibrium
payoff. Let \(\mathcal L=\{R1,\dots,R14\}\) be the dossier's list of
necessary conditions on a counterexample.

**Question Q.** Is \(\mathcal L\) contradictory, or does it delimit a very
small class of counterexamples? Decide, and identify exactly what separates
the two outcomes.

## Solution

**Proposition 1 (Q is the conjecture, verbatim).** The conjunction
\(\bigwedge\mathcal L\) is realizable by some four-player table iff
\(\neg P(4)\).

*Proof.* Each \(R_k\) is a theorem of the form
\(\operatorname{Gap}(r)\Rightarrow\psi_k(r)\), and \(R1\) contains
\(\operatorname{Gap}(r)\) itself. If some \(r\) has a gap, that same \(r\)
satisfies every \(\psi_k\), hence the whole conjunction. Conversely a
realization of the conjunction realizes \(R1\), a gap. ∎

*Corollary.* "\(\mathcal L\) is contradictory" is not a separate, possibly
easier statement: it is \(P(4)\). A list built by deriving consequences of
one hypothesis can never be refuted by inspection before the hypothesis is;
its length carries no evidence of inconsistency. The informative content of
\(\mathcal L\) is the shape of its unconsumed residual, and nothing else.

**Proposition 2 (the checkable fragment decides nothing).** The sublist of
finitely checkable table conditions — rationality (R2), the regime-5 matrix
geometry with full core and all players normal (R3), colliders (R4) — is
jointly satisfiable, and jointly satisfiable **with** equilibrium
existence.

*Proof.* Table \(W\) of dossier §8 satisfies all of them and has a
uniform-equilibrium payoff. ∎

*Corollary.* No contradiction can be extracted from the checkable
fragment; any proof of \(P(4)\) through \(\mathcal L\) must consume the
dynamic facts R5–R13.

**Proposition 3 (as a set of tables, the class is not small).** If a
counterexample exists, the set \(\{r:\eta(r)>0\}\) of counterexample
tables contains an open ball in \(\mathbb{R}^{15\cdot4}\), and rational
points of it.

*Proof.* Fact 3.2: \(\eta\) is 2-Lipschitz in
\(\lVert\cdot\rVert_\infty\), so \(\{\eta>0\}\) is open. ∎

*Corollary.* The "very small class" horn is false in its naive reading. A
counterexample cannot be one exceptional table or a thin variety of
tables; smallness, if anywhere, is in the dynamics each such table must
carry.

**Proposition 4 (where the smallness lives).** Under \(\neg P(4)\), every
counterexample table \(r\) satisfies simultaneously:

1. every canonical exact spine has all marginal clocks summable and
   converges to an all-Continue phantom, and is constant all-Continue from
   time zero if its limit has an open uniqueness basin (R8, Fact 5.3);
2. the total hazard of canonical exact blocks is uniformly bounded by a
   finite \(H(r)\) (R9);
3. exact cap–Nash prefixing above \(D_*\) has summable absorption (R10);
4. every paid minimum-fibre descent attempt ends in support drop, support
   entry, or off-minimum exit, and support drop can occur at most three
   times (R11);
5. its minimum laws carry finite atoms realized only through the
   forced-pair stream with fixed roles and floors, entering one of two
   terminal modes (R5–R7).

*Proof.* Conjunction of the cited dossier facts. ∎

So under \(\neg P(4)\) all *exact* backward-consistent structure is
asymptotically inert, while a fixed positive amount of debt must
circulate forever: the entire life of a counterexample is inexact or
semantic motion threaded between the two ports of dossier §7.

**Theorem (solution of Q, to the decidable extent).**

1. Q is equivalent to deciding \(P(4)\) (Proposition 1); no intermediate
   verdict exists.
2. Both naive horns fail: contradiction-by-inspection is impossible
   (Propositions 1–2), and the class of counterexample tables, if
   nonempty, is open, hence not small (Proposition 3).
3. The residual form of the dichotomy: co-realization of the two ports of
   dossier §7 by one extension-compatible source history is a necessary
   feature of any counterexample. Proving co-realization impossible,
   together with consuming uniform escape, yields \(P(4)\). Co-realization
   alone would **not** construct a counterexample: it would remove the
   known obstruction and leave the gap itself to be certified (R2). The
   separation between the horns is contained in: the two-port coupling
   problem, the uniform-escape consumption, and the two leakage closures
   of R11(b),(c).

## What the analysis rules out as next steps

- Searching for an inconsistency among R1–R14 by combining their
  statements: impossible short of \(P(4)\) (Proposition 1).
- Concluding from Proposition 2 that finitely checkable conditions can
  never carry a contradiction: Proposition 2 covers the **current**
  fragment only. A future finitely checkable necessary condition could in
  principle be jointly unsatisfiable with the others and prove \(P(4)\);
  its necessity proof would itself have to consume the dynamic facts, so
  the priority order below is unchanged, but no obstruction theorem
  excludes that route. What Proposition 3 does exclude is thinning the
  table class to a small set.

## Ranked attack list (that the analysis does justify)

Frontier note (`../notes/CODEX_ROOT__FIN4_TWO_CHAMBER_PAUSE_STATUS.md`):
the singleton/Never chamber is eliminated by the global singleton moat,
so items 1-3 below are subsumed by the two capstones
`../questions/FIN4_FULL_DEBT_CHAMBER_CONSUMER.md` and
`../questions/FIN4_RESET_RIGID_CHAMBER_CONSUMER.md`; the reviewed
debt-to-actual-reach fork theorem — now kernel-checked in the scratch lane
(ledger in
`../feedback/CODEX_SOURCE_GATE__FULL_DEBT_MOAT_PAID_BLOCK_EXACT_PORT__BY_CLAUDE_FABLE.md`) —
supplies the full-debt chamber's actually reached paid fork. Every
formalization-sized statement of that note's Section-10 list, and the
packaged common-prefix fork, is now kernel-checked in the scratch lane
(see the ledger). Also kernel-checked: the support-clause
   strengthening, the word-level graft action, the pure-time continuity
   groundwork, and the recentering note's §13 — cap upper
   semicontinuity, the escape decomposition, the bubble sign theorem,
   and attainment for socially nonpositive tables.

1. **No-new-debtor closure** (R11(b) at the aligned limit): prove that the
   aligned double-reset limit admits no support entry, making the descent
   rank effective; this kills minimum return except through R11(c).
2. **Off-minimum consumer** (R11(c)/R12 strict chamber): a consumer for the
   killed-face off-minimum endpoint; jointly with 1 this consumes minimum
   return.
3. **Uniform escape consumer** (R7 mode 1); exact checked inventory,
   per-rank dispatch, and open composition points:
   `ESCAPE_CAPSTONE_FRONTIER_MAP.md`.
4. **Two-port coupling** through the kernel program of
   `NONLOCAL_RECENTERING_ATTACK.md` (its §16 one-round screening system
   is probed: the calculus self-test passes exactly and an exact
   rational feasible point exists, so one-round screening at its current
   fidelity cannot consume the branch; the escalation order is recorded
   there). Proved
   there: kernel existence with inert past; the exact graft calculus and
   semantic sewing; the purity obstruction; the scalar train extraction
   with median-recentered actual-car kernels and typed deleted-player
   trains; residue solo domination; cap upper semicontinuity under
   nonnegative solos; the escaped-payoff decomposition and the bubble
   sign theorem (escaping mass carries nonnegative aggregate social
   value; attainment of the exploitability infimum for socially
   nonpositive tables); and the exact window-deletion identity with its
   per-window screening inequality for minimizing sequences. Open
   there: the typed train-assembly theorem (full cap convergence); the
   residue on-path classification (R13, recorded not checked); the
   cap-mediated leakage bookkeeping, now equipped with the deletion
   ledger; boundary identification with the saturation port.
5. On the negative side: candidate tables in the hard chamber, screened
   at minimum by the solo covering criterion and by exact
   stationary-system infeasibility over all support patterns
   (`NONLOCAL_RECENTERING_ATTACK.md` §2), and now also by the **social
   moat screens** (`SOCIAL_MOAT_CHAMBER.md`, kernel-checked): a
   candidate with nonnegative solos and all coalition socials
   nonpositive has an equilibrium outright, and every candidate must
   defeat the costate family — no strictly positive \(\theta\) with
   \(\theta\cdot r(S)\le0\ \forall S\) and \(\theta\cdot s\ge0\) may
   exist (an LP check per table). Table \(B\) of `CANDIDATE_TABLE_B.md`
   is refuted by a continuum of solo stationary equilibria:
   pure-profile audits are far too weak a screen.
