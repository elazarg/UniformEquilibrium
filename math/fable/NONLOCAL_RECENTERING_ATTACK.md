# Nonlocal attack: covering constraints and recentered kernels

Attempt document. Fact base: `FIN4_COUNTEREXAMPLE_DOSSIER.md` (cited as
R1–R14, Facts 2.1–5.6). All corrections from the reviews in
`../feedback/NONLOCAL_RECENTERING_ATTACK__BY_CODEX_ROOT.md`,
`..._REV3__BY_CODEX_ROOT.md`, and `..._REV6__BY_CODEX_ROOT.md` are
incorporated.

Status: §13, Lemma 12.3, and the semantic-pair action form of the graft
identities are kernel-checked (`lean/FableBubbleSign.lean`,
`lean/FablePureTimeContinuity.lean`, `lean/FableWordAction.lean`); the
fork, entrance, regression, and full-debt geometry theorems are
kernel-checked in the sibling `lean/` files; the per-file inventory is in
`../feedback/CODEX_SOURCE_GATE__FULL_DEBT_MOAT_PAID_BLOCK_EXACT_PORT__BY_CLAUDE_FABLE.md`.
Everything not annotated as checked is PROOF_DRAFT: rigorous ordinary
mathematics, reviewed where a feedback file records it, not
machine-checked.

## 1. Why the attack must be nonlocal

**(i) No off-the-shelf fixed point.** The terminal payoff is not continuous
on profiles in the weak topology: "quit at date \(n\)" converges weakly to
Never while the payoff jumps from \(r_i(\{i\})\) to \(0\). Best replies are
not upper hemicontinuous; classical existence arguments break exactly here.

**(ii) Anti-equilibrium constraints are coverings.** Already the cheapest
instability requirement — no stationary one-owner equilibrium — is a
condition on a continuum of rates (§2): finitely many affine functions must
be positive jointly over a whole interval. Pointwise sign conditions
(colliders, preemption) are only the interval's endpoints; candidate \(B\)
satisfied every endpoint and failed in the middle.

**(iii) Exact structure is inert; relative timing is the life.** By R8–R10
all exact Bellman structure of a counterexample is Zeno and phantom-bound,
and the ordinary law compactification forgets where marks sit (R14). A
limit notion keeping relative timing is mandatory; §4 builds one.

## 2. The solo screen and the covering criterion

For an owner \(j\) and rate \(q\in(0,1]\) let \(\pi_{j,q}\) be: \(j\) quits
with probability \(q\) at every live stage, everyone else Never. Absorption
is almost sure at \(\{j\}\), so \(U(\pi_{j,q})=r(\{j\})\).

**Lemma 2.1 (solo screen).** \(\pi_{j,q}\) is an exact terminal Nash
profile iff \(r_j(\{j\})\ge0\) and for every \(o\ne j\)

\[
g_{j,o}(q):=q\bigl(r_o(\{j,o\})-r_o(\{j\})\bigr)
+(1-q)\bigl(r_o(\{o\})-r_o(\{j\})\bigr)\;\le\;0 .
\]

*Proof.* Owner: a deviation quits eventually (payoff \(r_j(\{j\})\)) or is
Never (payoff \(0\)); cap \(=\max(r_j(\{j\}),0)\), on-path payoff
\(r_j(\{j\})\). Outsider \(o\): quitting at a live date meets \(j\)
simultaneously with probability \(q\), so the quit-now value is
\(A_o(q)=q\,r_o(\{j,o\})+(1-q)\,r_o(\{o\})\), the same at every live date;
"quit at \(t\)" is worth \((1-(1-q)^t)r_o(\{j\})+(1-q)^tA_o(q)\), on the
segment between \(A_o(q)\) and \(r_o(\{j\})\), and behavioral mixtures stay
on it; cap \(=\max(r_o(\{j\}),A_o(q))\), on-path payoff \(r_o(\{j\})\). ∎

**Corollary 2.2 (covering criterion, margin form).** If \(r\) has a
terminal gap \(\gamma\) (R1), then for every owner \(j\) with
\(r_j(\{j\})>-\gamma\):

\[
\max_{o\ne j}g_{j,o}(q)\;\ge\;\gamma\qquad\text{for every }q\in(0,1]
\]

(up to the strict/weak convention of the chosen gap statement). The
endpoints are the known pointwise screens: \(q=1\) is the collider
condition (R4), \(q\to0\) the preemption sign, and the excluded \(q=0\) is
the all-Never profile, whose instability is \(\max_ir_i(\{i\})\ge\gamma\).

*Proof.* At \(\pi_{j,q}\) some player has debt \(\ge\gamma\) (R1); the
owner's debt is \(\max(0,-r_j(\{j\}))<\gamma\); outsider \(o\)'s debt is
\(\max(0,g_{j,o}(q))\) by Lemma 2.1. ∎

**Worked failure (candidate \(B\)).** At owner \(2\):
\(g_{2,0}=g_{2,1}=1-2q\), \(g_{2,3}=4q-3\); the maximum is \(\le0\) exactly
on \([\tfrac12,\tfrac34]\), and each such \(q\) is an exact equilibrium
with payoff \((0,0,1,4)\).

**Remark 2.3 (superseded).** The full-support stationary cap formula and
the resulting semialgebraic screen, formerly only a specification, are
proved in §9 (Theorem 9.1).

## 3. Uniform floors on the minimum fibre

**Lemma 3.1.** Assume R1 and R5. On the **joint** semantic/law carrier let

\[
F=\{(X,\mu)\in\mathcal C : D(X)=D_*\}
\]

be the minimum fibre. Then there is \(\mu_*>0\) with
\(\max_{\varnothing\ne S\subseteq I}\mu(\operatorname{some}S)\ge\mu_*\) for
every \((X,\mu)\in F\).

*Proof.* \(F\) is closed in the compact joint carrier, hence compact;
\((X,\mu)\mapsto\max_S\mu(\operatorname{some}S)\) is a maximum of finitely
many continuous coordinates, hence continuous, and positive on \(F\) by R5
(which speaks of joint minimizing points); a positive continuous function
on a compact set has a positive minimum. ∎

The argument gives a uniform floor for any finite family of positive,
fibre-continuous quantities of the joint point. It does **not** give
uniform floors for label-dependent or chronology-dependent quantities (a
selected reached row, a paid gain): those are attached to realizing
sequences, not to carrier points. That gap is target N1 in §6.

## 4. Recentered kernels

**Definition 4.1.** A *marked chronology* is a pair \((\sigma,\tau)\) of a
profile and a date; its *recentered array* is \(y_{t,i}=x_{\tau+t,i}\) for
\(t\ge-\tau\), extended by \(0\) for \(t<-\tau\), indexed by
\(t\in\mathbb Z\). A *kernel* is a two-sided array with
\(\sum_{t<0}\sum_iy_{t,i}<\infty\).

**Theorem 4.2 (kernel existence with inert past).** Let
\((\sigma_n,\tau_n)\) be marked chronologies with

\[
\mathbb P_{\sigma_n}(\text{alive at }\tau_n)\;\ge\;\lambda\;>\;0 .
\]

Split the marked dates: along a subsequence either \(\tau_n\) is constant
(then the recentered limit is a one-sided object after the finitely many
actual pre-mark rows, and the conclusion is immediate), or
\(\tau_n\to\infty\); assume the latter. Then a further subsequence of the
recentered arrays converges pointwise to a two-sided array \(y\) with

\[
\sum_{t<0}\sum_iy_{t,i}\;\le\;\log(1/\lambda).
\]

*Proof.* Pointwise limits exist by compactness of
\([0,1]^{\mathbb Z\times I}\) and diagonal extraction. For a window
\([-s,0)\) and \(n\) with \(\tau_n\ge s\),

\[
\prod_{t=-s}^{-1}\prod_i\bigl(1-x^n_{\tau_n+t,i}\bigr)
\ \ge\ \prod_{t<\tau_n}\prod_i\bigl(1-x^n_{t,i}\bigr)
\ =\ \mathbb P_{\sigma_n}(\text{alive at }\tau_n)\ \ge\ \lambda,
\]

since dropping factors \(\le1\) increases a product. In the limit every
window product is \(\ge\lambda\); every factor is positive, and
\(u\le\log\frac1{1-u}\) gives
\(\sum_{t=-s}^{-1}\sum_iy_{t,i}\le\log(1/\lambda)\) for every \(s\). ∎

**Lemma 4.3 (boundary semantics; corrected).** Let \(y\) be a kernel,
\(\delta_s=\sum_{t<-s}\sum_iy_{t,i}\downarrow0\), and let
\(\kappa^{(s)}\) be the profile of the game playing the hazards
\((y_t)_{t\ge-s}\) from its first stage. Then:

1. for \(s'\ge s\): \(|U_i(\kappa^{(s')})-U_i(\kappa^{(s)})|\le
   2R\,\delta_s\), and the outcome laws are within \(\delta_s\) in total
   variation;
2. for \(s'>s\):
   \(\bigl|B_i(\kappa^{(s')})-\max\bigl(B_i(\kappa^{(s)}),r_i(\{i\})\bigr)
   \bigr|\le4R\,\delta_s\); and for \(s\ge1\):
   \(B_i(\kappa^{(s)})\ge r_i(\{i\})-2R\,\delta_{s-1}\);
3. consequently \(|B_i(\kappa^{(s')})-B_i(\kappa^{(s)})|\le
   6R\,\delta_{s-1}\) for \(s'>s\ge1\), the limits
   \(u_i(\kappa)=\lim_sU_i(\kappa^{(s)})\),
   \(b_i(\kappa)=\lim_sB_i(\kappa^{(s)})\) exist, satisfy
   \(b_i(\kappa)\ge r_i(\{i\})\) — so all-Continue is exact cap–Nash
   against \(b(\kappa)\) — and \((u(\kappa),b(\kappa))\) lies in the
   compact carrier; under R1, \(\sum_i(b_i-u_i)\ge D_*\).

*Remark (why \(s'=s\) must be excluded in (2)).* With all negative-time
hazards zero, an opponent quitting surely at time \(0\), and
\(r_i(\{i\})=1\) while \(i\) receives \(-1\) both at the opponent's solo
exit and at the simultaneous pair: \(\delta_0=0\) and
\(B_i(\kappa^{(0)})=-1\), while
\(\max(B_i(\kappa^{(0)}),r_i(\{i\}))=1\). The extra strictly earlier
window is what makes the solo value available.

*Proof.* (1) Couple \(\kappa^{(s)}\) and \(\kappa^{(s')}\) on their common
hazards from \(-s\) on; realizations differ only if someone quits during
\([-s',-s)\), probability \(\le\delta_s\); payoffs are bounded by \(R\).

(2) Upper bound: split a deviation of \(\kappa^{(s')}\) by its quit date.
Dates \(\ge-s\): extend the matching \(\kappa^{(s)}\)-deviation by
Continue on the extra window and couple as in (1); error \(\le2R\delta_s\)
uniformly. Dates \(t\in[-s',-s)\): the value differs from \(r_i(\{i\})\)
only if someone quits before \(t\) (probability \(\le\delta_s\)) or an
opponent quits at \(t\) (probability \(\le\sum_{j\ne i}y_{t,j}\le
\delta_s\)); so the value is \(r_i(\{i\})\pm2R\delta_s\). Hence
\(B_i(\kappa^{(s')})\le\max(B_i(\kappa^{(s)}),r_i(\{i\}))+4R\delta_s\),
and the same two families give the matching lower bound. First-row bound:
in \(\kappa^{(s)}\), \(s\ge1\), quitting at the first row \(-s\) meets an
opponent with probability \(\le\sum_{j\ne i}y_{-s,j}\le\delta_{s-1}\) and
nobody has quit before, so
\(B_i(\kappa^{(s)})\ge r_i(\{i\})-2R\delta_{s-1}\).

(3) For \(s'>s\ge1\), combine (2) with
\(0\le\max(B_i(\kappa^{(s)}),r_i(\{i\}))-B_i(\kappa^{(s)})\le
2R\delta_{s-1}\) (the first-row bound): the caps are Cauchy with modulus
\(6R\delta_{s-1}\). The limit dominates \(r_i(\{i\})-2R\delta_{s-1}\) for
every \(s\), so \(b_i\ge r_i(\{i\})\); exactness of all-Continue against
\(b\) is the inequality \(r_i(\{i\})\le b_i\) coordinatewise. Each
\((U(\kappa^{(s)}),B(\kappa^{(s)}))\) is the semantic pair of an actual
profile and the carrier is closed. ∎

**Proposition 4.4 (mark survival).** In Theorem 4.2, if at every
\(\tau_n\) the exact marked coalition event "\(\{j,o\}\) quits at
\(\tau_n\)" has unconditional probability \(\ge\lambda\), then in the
limit: survival to time \(0\) is \(\ge\lambda\), the conditional
marked-coalition probability of the row \(y_0\) is \(\ge\lambda\), and
every truncation \(\kappa^{(s)}\) gives the marked event at recentered
date \(0\) probability \(\ge\lambda^2\).

*Proof.* Survival: the window products are \(\ge\lambda\). Conditional
row event: for each \(n\) it is a fixed continuous function of the single
row \(x^n_{\tau_n}\), equal to (unconditional)/(survival)
\(\ge\lambda/1\); rows converge pointwise to \(y_0\). Multiply. ∎

## 5. What is established

> **Representation theorem (corrected core).** A cofinally reached marked
> chronology admits a two-sided hazard-kernel limit with summable past
> (\(\le\log(1/\lambda)\)), a well-defined carrier semantic boundary at
> \(t\to-\infty\), an all-Continue exact cap root at that boundary, and a
> fixed positive marked event at time zero, all inside one
> extension-compatible truncation family \(\{\kappa^{(s)}\}\).

It preserves one marked port together with its all-Continue boundary. It
does **not** yet: transfer the future tail semantics (T1), place a second
mark in the same ancestry (N2), supply an exact Nash–Bellman chronology,
or consume any Fin4 branch.

## 6. Open producers, in corrected order

**N2 (source-faithful renewal / sewing) — partially resolved, and
re-scoped.** §10 proves an exact graft calculus and a tail-swap theorem:
the semantic half of the sewing problem is solved — a second-round
realizer family *can* be installed inside the first round's ancestry,
preserving the first mark and its paid structure up to \(o(1)\). §11
proves the other half is impossible in the naive form: atlas marks are
purified (conditional probability one), so survival past a mark is zero
and no later mark can carry unconditional mass. The corrected target is
cap-mediated bookkeeping across grafted rounds (§11), which is R11's
trichotomy instantiated on the grafted family.

**T1 (tail transfer).** Pointwise convergence of nonnegative-time hazards
does not identify future terminal semantics (mass can move to later dates
or Never). Needed: an equi-tightness envelope for the retained tails,
derived from the source — not assumed.

**T2 (boundary identification).** Lemma 4.3 makes the kernel boundary a
neutral-port *candidate* (all-Continue exact at the boundary cap).
Identifying it with the strict saturation minimum set — boundary debt
\(=D_H\), root uniqueness — is open; see §7 for what the checked hull
supplies.

**N1 (uniform floors, secondary).** Fibre-continuous floors exist (Lemma
3.1); floors for chronology-attached quantities (reached mass, paid gain)
as functions on the fibre remain open and matter only downstream of N2.

## 7. Source-level interface (recon of the checked frontier)

Recorded here so the next agent can plug the kernel into the exact
structures without re-deriving them; citations by declaration name and
file, statuses as in the repository.

- **Source.** `FinFourMinimumAtomProducer`
  (`Research/Quitting/FinFourProducerAtlas/Source.lean`) stores: the hard
  residual, one minimum joint semantic/law point, \(D_*>0\), and one
  causal suffix atom. Realizing rows are literally
  `prefixedProfile profiles roots rank` — the *base* realizing profile
  prefixed by an exact cap–Nash root stack of length `rank + 1` — with the
  mark at `shiftedStage`. So every rank shares one base chronology and
  carries exactly one mark; the pre-mark part at depth \(s\) is (deep
  stack rows) + (the base's fixed pre-mark rows). Recentering a stream
  therefore has past = limits of deep exact-stack rows.
- **Floors.** Stage mass \(>\mu^2/8\) (`FinFourLowTailRow`), payer defect
  \(\ge D_*/3\), payer gain \(\ge\lambda D_*/3\), canonical form
  \(\ge\mu^2D_*/24\) (`canonical_payerGain_floor`,
  `SourcePreservingForcedPair.lean`). These are per-selected-source, as
  §3 warns.
- **Modes.** `FinFourUniformEscapePacket` / `FinFourMinimumReturnPacket`
  over one stabilized stream with fixed labels
  (`SourcePreservingCompletionAtlas.lean`); the dispatch
  `uniformEscape_or_minimumReturn` is checked Research.
- **Minimum-return consumer.**
  `FinFourMinimumReturnNormalizedThreeRoleOrStrictInert`
  (`SourcePreservingCompletionConsumers.lean`): equality arm = three-role
  regeneration/ascent at the retained hull point; strict arm = whole debt
  \(>D_*\) with all-Continue as the **unique** exact \(0\)-Nash root.
- **Saturation hull** (reviewed export,
  `exports/LAW_TIGHT_CAP_NASH_SATURATION_HULL.md`): the law-tight hull
  \(\widehat{\mathcal H}(z_0)\) with exact scaling
  \(D(P_xz)=q(x)D(X)\), absorption budget
  \(\sum_na(x_n)\le(D(z_0)-D_H)/D_H\) along exact prefix chains —
  consistent with, and sharper on exact stacks than, the
  \(\log(1/\lambda)\) bound of Theorem 4.2 — and the strict trichotomy:
  full debt support / reset-rigid incidence / singleton–Never binding
  cycle whose edges satisfy \(r_j(\{i,j\})-r_j(\{i\})>0\) (the collider
  geometry again). The remaining strict-saturation consumer named there:
  prove \(D_H=D_*\), or turn one strict chamber into an actual profile
  with total debt below \(D_*\) (a contradiction, refuting the chamber).
- **Kernel plug-in point.** Recentering the stabilized stream: the past
  consists of deep exact-stack rows, whose caps converge along a
  subsequence; exactness of cap–Nash roots is closed, so the kernel's far
  past consists of exact cap–Nash roots at the boundary. With Lemma
  4.3(3) the boundary carries an all-Continue exact root; whether its
  debt equals \(D_H\) (which by hull root-uniqueness would make the
  boundary a strict-saturation port and settle T2) is exactly where the
  next proof effort belongs.

## 8. Interface to the program

`DICHOTOMY_ANALYSIS.md` ranked list: item 4 routes through T1, then the
cap-mediated bookkeeping of §11; candidate screening (item 5) now has the
full stationary screen of §9 as a proved tool.

## 9. The full stationary screen

Fix rates \(q\in[0,1]^I\setminus\{0\}\) and the stationary profile
\(\pi_q\). For each \(i\) put
\(\beta_i=\prod_{j\ne i}(1-q_j)\), \(h_{-i}=1-\beta_i\),
\(\pi_{-i}(T)=\prod_{j\in T}q_j\prod_{j\notin T,\,j\ne i}(1-q_j)\) for
\(T\subseteq I\setminus\{i\}\), and

\[
V^Q_i=\sum_{T\subseteq I\setminus\{i\}}\pi_{-i}(T)\,r_i(T\cup\{i\}),
\qquad
V^N_i=\begin{cases}
\dfrac{1}{h_{-i}}\sum_{\varnothing\ne T}\pi_{-i}(T)\,r_i(T), &
h_{-i}>0,\\[1ex]
0, & h_{-i}=0 .
\end{cases}
\]

**Theorem 9.1.** For every \(i\):

1. \(B_i(\pi_q)=\max(V^Q_i,V^N_i)\);
2. \(U_i(\pi_q)=\dfrac{q_iV^Q_i+(1-q_i)h_{-i}V^N_i}
   {q_i+(1-q_i)h_{-i}}\) (the denominator is positive since
   \(q\ne0\));
3. \(\pi_q\) is an exact terminal Nash profile iff for every \(i\):
   if \(q_i\in(0,1)\) and \(h_{-i}>0\) then \(V^Q_i=V^N_i\);
   if \(q_i=0\) then \(V^Q_i\le V^N_i\);
   if \(q_i=1\) then \(V^N_i\le V^Q_i\);
   and if \(h_{-i}=0\) (so \(i\) is the sole quitter) then
   \(0\le V^Q_i=r_i(\{i\})\).

*Proof.* (1) The opponents' environment is memoryless: conditional on
being live, some opponent quits with probability \(h_{-i}\), and the
conditional others-coalition payoff to a passive \(i\) is \(V^N_i\). The
value of "continue to \(t\), quit at \(t\)" is therefore

\[
Q_i(t)=(1-\beta_i^{\,t})V^N_i+\beta_i^{\,t}V^Q_i
\]

(geometric sum; when \(\beta_i=1\) this reads \(Q_i(t)=V^Q_i\), matching
the convention \(V^N_i=0\) since Never then pays \(0\)). The value of
Never is \(V^N_i\) in both cases. A behavioral deviation is a stopping
law \(\nu\), and its value \(\sum_t\nu(t)Q_i(t)+\nu(\infty)V^N_i\) is a
convex combination of numbers lying on the segment between \(V^Q_i\) and
\(V^N_i\); the supremum is attained at \(t=0\) or at Never.

(2) Split the terminal coalition by membership of \(i\): the per-date
absorption probability is \(h=q_i+(1-q_i)h_{-i}\), the \(S\ni i\) part
contributes \(q_iV^Q_i\) and the \(S\not\ni i\) part
\((1-q_i)h_{-i}V^N_i\); conditioning on absorption divides by \(h\). If
\(q_i=0\) and \(q\ne0\) then some \(q_j>0\) gives \(h_{-i}\ge q_j>0\), so
\(h>0\) always.

(3) By (2), \(U_i\) is a convex combination of \(V^Q_i\) and \(V^N_i\)
with weights proportional to \(q_i\) and \((1-q_i)h_{-i}\). The Nash
condition \(\max(V^Q_i,V^N_i)\le U_i\) holds iff: when both weights are
positive, \(V^Q_i=V^N_i\); when the weight of \(V^N_i\) vanishes
(\(q_i=1\), or \(h_{-i}=0\) with \(q_i>0\)), \(V^N_i\le V^Q_i\) — for
\(h_{-i}=0\) this is \(0\le V^Q_i\) and \(V^Q_i=r_i(\{i\})\) since the
others surely continue; when the weight of \(V^Q_i\) vanishes
(\(q_i=0\)), \(V^Q_i\le V^N_i\). ∎

**Corollary 9.2 (stationary covering screen).** A table with terminal
gap \(\gamma\) satisfies, for **every** \(q\in[0,1]^I\setminus\{0\}\),

\[
\max_i\bigl(\max(V^Q_i,V^N_i)-U_i\bigr)\;\ge\;\gamma .
\]

All quantities are rational in \(q\) with denominators \(h\), \(h_{-i}\);
clearing denominators per support pattern turns the screen into finitely
many polynomial conditions — a decidable semialgebraic covering. Lemma
2.1 is the special case \(q=q_je_j\).

## 10. Graft calculus and the tail-swap theorem

For a profile \(\sigma\) with hazards \((x_t)\), a date \(d\ge0\), and a
profile \(T\), let \(\sigma[{<}d]\star T\) play \(x_t\) for \(t<d\) and
\(T\)'s hazards from date \(d\) on. Define, from the pre-\(d\) hazards
only: the survivals
\(\rho_d=\prod_{t<d}\prod_j(1-x_{t,j})\) and
\(\rho^{-i}_d=\prod_{t<d}\prod_{j\ne i}(1-x_{t,j})\); the pre-\(d\)
payoff \(U^{<d}_i\) (absorption before \(d\)); the passive-deviator
collection \(W^{<d}_i\) (others absorb before \(d\) while \(i\)
continues); and \(M^{<d}_i=\max_{t<d}Q^{\sigma}_i(t)\), the best
pre-\(d\) quit value (for \(d=0\): \(M^{<0}_i=-\infty\),
\(U=W=0\), \(\rho=1\)).

**Lemma 10.1 (exact graft identities).** *(The semantic-pair action form is kernel-checked: one-row in-repo as `quittingTerminalSemanticPair_rootThenContinuation`; word-level fold as `fableRootWordProfile_semanticPair` in `lean/FableWordAction.lean`.)* With
\(G=\sigma[{<}d]\star T\):

1. \(\operatorname{law}(G)=\mu^{<d}+\rho_d\cdot
   \operatorname{shift}_d\operatorname{law}(T)\);
2. \(U_i(G)=U^{<d}_i+\rho_d\,U_i(T)\);
3. \(B_i(G)=\max\bigl(M^{<d}_i,\;W^{<d}_i+\rho^{-i}_d\,B_i(T)\bigr)\).

*Proof.* (1), (2): decompose by whether absorption occurs before \(d\).
(3): a deviation of \(i\) is a stopping law \(\nu\); its value is
\(\sum_{t<d}\nu(t)Q^{\sigma}_i(t)+\nu([d,\infty])\bigl(W^{<d}_i+
\rho^{-i}_d\,u\bigr)\), where \(u\) is the value in \(T\) of the
conditional continuation of \(\nu\) — every quantity before \(d\) depends
only on the pre-\(d\) hazards of the others, and quitting before \(d\)
ends the game without seeing the tail. The value is affine in \(\nu\);
taking suprema over the two kinds of extreme behavior gives the maximum
of the best pre-\(d\) quit and \(W^{<d}_i+\rho^{-i}_dB_i(T)\). ∎

**Theorem 10.2 (tail swap).** Let \(T=\sigma[{\ge}d]\) be the literal
tail (so \(\sigma=\sigma[{<}d]\star T\)) and \(T'\) arbitrary,
\(G=\sigma[{<}d]\star T'\). Then coordinatewise

\[
|U_i(G)-U_i(\sigma)|=\rho_d\,|U_i(T')-U_i(T)|,\qquad
|B_i(G)-B_i(\sigma)|\le\rho^{-i}_d\,|B_i(T')-B_i(T)|,
\]

the outcome laws differ by at most
\(\rho_d\,d_{TV}(\operatorname{law}T',\operatorname{law}T)\), and
\(|D(G)-D(\sigma)|\le\sum_i(|\Delta U_i|+|\Delta B_i|)\).

*Proof.* Subtract the identities of Lemma 10.1;
\(|\max(a,w+\rho b)-\max(a,w+\rho b')|\le\rho|b-b'|\). ∎

**Corollary 10.3 (semantic sewing).** Let \(\sigma_n\) be profiles with
\(D(\sigma_n)\to D_*\) whose marked data (rows, roles, stage masses) are
determined by the hazards before dates \(d_n\), and whose literal tails'
semantic pairs converge to \(w\). Let \((T'_k)\) be **any** profiles with
semantic pairs converging to \(w\) — for instance the realizing
chronology of a checked causal atom at the tails' limiting minimizing
point. Then a diagonal \(G_n=\sigma_n[{<}d_n]\star T'_{k(n)}\)
satisfies: \(D(G_n)\to D_*\); the pre-\(d_n\) hazards, hence all marked
row data, are unchanged; and every gain of the form
\(U_p(\text{modified prefix}\star\text{tail})-U_p(\sigma)\) changes by at
most twice the tails' pair distance, hence by \(o(1)\). If the tail laws
also share a limit, the whole laws share theirs.

*Proof.* Theorem 10.2 and a diagonal choice; a paid gain is a difference
of two grafted values sharing the tail, and each side moves by at most
the tails' pair distance by Lemma 10.1(2). ∎

This resolves the **semantic half** of the sewing problem N2: a
second-round realizer family can be installed inside the first round's
ancestry with vanishing perturbation of the first round's mark and paid
structure.

## 11. The purity obstruction and the corrected target

The checked atlas endpoints are **purified**: at the constructed
endpoint profiles, the marked row's coalition quits with conditional
probability one (`pureSingleton_stageMass_eq_liveMass`,
`forcedPair_stageMass_eq_liveMass`; recon §7). Consequences, each
immediate from Lemma 10.1:

1. **Severed pair rows.** After a pure *pair* row, survival is zero and
   moreover \(\rho^{-i}_d=0\) for every player \(i\) — one unilateral
   deviation cannot prevent the other pair member's sure quit. The
   post-row tail influences neither \(U\) nor any cap of the whole
   profile: the profile's semantics is determined at the row. The
   "verbatim tail" is bookkeeping about the tail as a **standalone**
   profile, not a channel into the parent's semantics.
2. **Owner-screened singleton rows.** After a pure *singleton* row, only
   the owner's own deviation reaches the tail
   (\(\rho^{-j}_d>0\) for the owner \(j\), \(\rho^{-i}_d=0\)
   otherwise): the tail disciplines exactly one cap coordinate. This is
   the checked "screen" in its quantitative form.
3. **No multi-mark mass engine.** For purified chronologies a second
   mark after the first has unconditional probability zero — the
   impossibility is structural, not an unproven floor. For the actual
   (impure) realizers no checked floor bounds survival past the mark
   either way. In both cases the iteration engine of the former T3
   cannot be mass-based.

**Corrected target.** Combining §10 and the purity facts: iterated
tail-swap produces one pointwise-limit profile \(\sigma^{\infty}\)
carrying a nested chain of standalone tails
\(T^{(1)}\supset T^{(2)}\supset\cdots\), each with debt \(\to D_*\) and
each holding the next round's marked row; but (a) the semantics of
\(\sigma^{\infty}\) is not determined by the pointwise limit — exactly
T1's tightness gap, which is therefore load-bearing even to *define* the
infinite chronology's semantics; and (b) all influence of round
\(m{+}1\) on round \(m\) flows through the cap channel
\(W+\rho^{-i}B_i(T)\) of Lemma 10.1(3), for the screened coordinates
only. The corrected engine question — the precise successor of N2 — is:

> along the nested chain, does the cap-channel bookkeeping (the leakage
> trichotomy R11 applied at each round through Lemma 10.1(3)) admit a
> monotone quantity, or a consistent assignment realizing every round —
> i.e., is the chain consumable, or constructible?

This question is now posed on one explicit object (the grafted chain)
with exact identities (Lemma 10.1) instead of on unrelated realizing
sequences; T1 is its only remaining foundational prerequisite — and §12
replaces T1 by a decomposition that is proved except for the residue
classification.

## 12. The absorption train

T1 asked for tightness, which the timing bubble (R5) explicitly forbids
in general. The correct replacement is a concentration-compactness
decomposition: absorption cannot escape — it can only ride away in
drifting windows, and every drifting window is a kernel.

For a profile \(\sigma_n\) let \(\alpha_n\) be its absorption measure on
\(\mathbb N\): \(\alpha_n(\{t\})=\mathbb P_{\sigma_n}(\text{absorption at
}t)\), total mass \(\le1\).

**Theorem 12.1 (train extraction).** Every sequence of measures
\(\alpha_n\) on \(\mathbb N\) with \(\alpha_n(\mathbb N)\le1\) admits a
subsequence (not relabeled), an at most countable family of *cars*
\(m=1,2,\dots\) with centers \(c^m_n\), radii \(R^m_n\to\infty\), masses
\(\theta_m>0\) with \(\sum_m\theta_m\le1\), and limit measures
\(\beta^m\) on \(\mathbb Z\) of mass \(\theta_m\), such that:

1. \(\alpha_n(c^m_n+\cdot)\to\beta^m\) pointwise on \(\mathbb Z\), and
   \(\alpha_n([c^m_n-R^m_n,\,c^m_n+R^m_n])\to\theta_m\);
2. the cars separate: \(|c^m_n-c^{m'}_n|\to\infty\) for \(m\ne m'\);
3. the residue vanishes: for every window length \(\tau\) and every
   \(\varepsilon>0\) there is \(K\) with
   \[
   \limsup_n\ \sup\bigl\{\alpha_n([t,t+\tau)):[t,t+\tau)\cap
   \textstyle\bigcup_{m\le K}[c^m_n\pm R^m_n]=\varnothing\bigr\}
   \ \le\ \varepsilon .
   \]

When the underlying object is a probability measure on
\(\mathbb N\cup\{\infty\}\), the extraction is applied to its finite
part; the atom at \(\infty\) is a bounded scalar and converges along the
same subsequence.

*Proof.* Call a nonzero measure \(\beta\) on \(\mathbb Z\) a *cluster* of
a sequence of measures if it is a pointwise limit of recenterings along a
subsequence. If windows \([t_n,t_n+\tau)\) keep mass \(\ge\delta\) along
a subsequence, recentering at \(t_n\) and a diagonal extraction give a
cluster of mass \(\ge\delta\): on the finite window the limit mass is a
limit of finite sums. Let \(\mu^*_1\) be the supremum of cluster masses
of \((\alpha_n)\); if \(\mu^*_1=0\) there are no cars and (3) holds with
\(K=0\). Otherwise pick a cluster \(\beta^1\) of mass
\(\theta_1\ge\mu^*_1/2\) with centers \(c^1_n\); choose radii
\(R^1_n\to\infty\) slowly enough that
\(\alpha_n([c^1_n\pm R^1_n])\to\theta_1\) (possible since for each fixed
\(R\) the window mass converges to \(\beta^1([-R,R])\uparrow\theta_1\);
diagonalize). Define the residual measures by deleting
\([c^1_n\pm R^1_n]\) and iterate: \(\mu^*_{m+1}\) is computed on the
residual, and any cluster of the residual has centers leaving every
neighborhood of the earlier cars, giving (2). Since
\(\theta_m\ge\mu^*_m/2\) and the deleted windows are asymptotically
disjoint, \(\sum_m\theta_m\le\liminf\alpha_n(\mathbb N)\le1\), so
\(\mu^*_m\to0\). Each extraction round refines the previous subsequence;
one final diagonal across the rounds fixes a single subsequence
realizing every car simultaneously. For (3): a sequence of windows of
length \(\tau\) outside the first \(K\) cars keeping mass
\(\ge\varepsilon\) would produce a residual cluster of mass
\(\ge\varepsilon\), so \(\varepsilon\le\mu^*_{K+1}\), which is below any
prescribed level for \(K\) large. ∎

**Corollary 12.2 (actual cars are kernels, after quantile
recentering).** Apply Theorem 12.1 to the absorption measures of
profiles \(\sigma_n\), and fix a car \(m\). Choose an integer \(q_m\)
with \(\beta^m([q_m,\infty))\ge\theta_m/2\) (a median point of
\(\beta^m\)). Window convergence gives, eventually,
\(\alpha_n([c^m_n+q_m,\,c^m_n+R^m_n])\ge\theta_m/3\); absorption at a
date requires being alive at every earlier date, so
\(\mathbb P_{\sigma_n}(\text{alive at }c^m_n+q_m)\ge\theta_m/3\).
Theorem 4.2 therefore applies at the **shifted** centers
\(c^m_n+q_m\) with \(\lambda=\theta_m/3\): the recentered hazards
converge along a further subsequence to a two-sided kernel with past
hazard \(\le\log(3/\theta_m)\), and Lemma 4.3 gives the car a carrier
boundary semantics with the all-Continue inequality. The shift is
necessary: survival to the window *start* dominates the window mass, but
a car may place all of its limit mass strictly before the original
center, so no reach floor holds there; the median shift is what produces
one.

**Typing correction (adopted from review).** Player
\(i\)'s deviation values are governed by the opponents-only survival
\(\rho^{-i}_t\), which can stay large where absorption is negligible
(after \(i\)'s own on-path exit, \(\rho_t\approx0\) while
\(\rho^{-i}_t\approx1\)); so the absorption train alone misses
cap-relevant structure, and the caps need the measures \(\mu^{-i}_n\) —
the others-absorption law of \(\sigma_n[i\leftarrow\text{Never}]\). But
promoting every car of the combined family to one full-profile kernel is
**false**: if \(i\) quits surely at date \(0\) while an opponent quits
surely at date \(n\), then \(\alpha_n\) concentrates at \(0\) and
\(\mu^{-i}_n\) at \(n\); the late car is unreachable in actual play, and
\(i\)'s sure quit sits in its negative past, so full-hazard past
summability fails. The correct object is a **typed train**:

- *actual cars* — Theorem 12.1 applied to \(\alpha_n\); by Corollary
  12.2 (median shift) these carry full kernels with carrier boundary
  semantics;
- *deleted-\(i\) cars*, one train per player — Theorem 12.1 applied to
  \(\mu^{-i}_n\); these carry **opponent-only kernels**: Theorem 4.2
  applies verbatim to the hazard arrays of the players
  \(I\setminus\{i\}\) (its proof uses only products over the displayed
  players), with the reach floor computed from \(\rho^{-i}\) via the
  same median-shift argument, since \(\mu^{-i}\)-absorption at a date
  requires the opponents to be alive there. Deleted-\(i\) cars enter
  only the computation of \(B_i\); they carry no prescribed-payoff
  semantics and are not claimed reachable in actual play.

One further diagonal fixes a common subsequence for all five typed
trains.

**Lemma 12.3 (residue rows are solo-dominated; proved).** *(Kernel-checked as `fable_pureTimeValue_row_estimate` in `lean/FablePureTimeContinuity.lean`.)* For any
profile, any \(i\), any date \(t\):
\(\mu^{-i}(\{t\})=\rho^{-i}_t\,h^{-i}_t\) exactly, where \(h^{-i}_t\) is
the others' quit probability at row \(t\); hence the quit value
\(Q_i(t)=A_i(t)+\rho^{-i}_tV^{\text{row}}_i(t)\) (passive collection
plus weighted immediate row value) satisfies

\[
\bigl|Q_i(t)-\bigl(A_i(t)+\rho^{-i}_t\,r_i(\{i\})\bigr)\bigr|
\;\le\;2R\,\mu^{-i}(\{t\}) ,
\]

because \(|V^{\text{row}}_i(t)-r_i(\{i\})|\le2R\,h^{-i}_t\) (the row
value differs from the solo reward only on the event that an opponent
quits at \(t\)). On residue stretches the right side is uniformly small
by Theorem 12.1(3) applied to the deleted-\(i\) train: residue
deviations are worth at most the *solo envelope*
\(A_i(t)+\rho^{-i}_tr_i(\{i\})\) up to a vanishing error. ∎

**The typed train-assembly problem (open).** Full cap convergence
through the train requires, per the review: control of the
supremum over infinitely many cars and residue stretches; cars whose
enumeration labels drift; the Never endpoint; left and right passive
collections at every deleted-coordinate car; and compatibility of the
four typed cap decompositions with the actual prescribed-payoff limit.
Supremum and subsequence limits do not commute without a uniform tail
estimate, and producing that estimate is the same nonlocality the train
is meant to resolve — this is an open problem, not bookkeeping. §13
sidesteps it for the program's immediate need by proving **one-sided**
(upper) semicontinuity of caps directly, with no train structure at
all.

**What the train replaces and what it leaves.** The decomposition makes
the timing bubble structural: all concentrated absorption and
counterfactual opponent absorption ride in countably many kernels;
between them, deviations see only solo envelopes. The full max-formula
assembly is no longer on the critical path: §13 delivers what the
program needs from limits — an upper bound on limit debt — directly, by
semicontinuity, and extracts a new sign constraint on the bubble.

## 13. Semicontinuity and the social value of the bubble

*(Kernel-checked: `fable_bestResponse_usc`,
`fable_payoff_escape_decomposition`, `fable_bubble_social_sign`,
`fable_bubble_attainment` in `lean/FableBubbleSign.lean`; the checked
Never-chase constant is \(4M\varepsilon\) instead of the
\(3R\varepsilon\) below — immaterial.)*

Throughout, \(\sigma_n\to\sigma^{\infty}\) means pointwise convergence of
the hazard arrays. Write \(\Lambda_n(t,S)\) for the probability that
\(\sigma_n\) absorbs at date \(t\) with coalition \(S\), and
\(Q^{(n)}_i(t)\), \(N^{(n)}_i\) for the quit-at-\(t\) and Never values of
a deviating \(i\) against \(\sigma_n\); recall
\(B_i=\max(\sup_tQ_i(t),N_i)\) (affinity in the stopping law, as in
Theorem 9.1(1)).

**Lemma 13.1 (fixed-horizon continuity).** For each fixed \(t\) and
\(S\), the quantities \(\Lambda_n(t,S)\), \(A^{(n)}_i(t)\) (passive
collection before \(t\)), \(\rho^{-i}_{t}(\sigma_n)\), and
\(Q^{(n)}_i(t)\) converge to those of \(\sigma^{\infty}\).

*Proof.* Each is a finite sum of finite products of hazards at dates
\(\le t\). ∎

**Theorem 13.2 (caps cannot jump up when solos are nonnegative).** If
\(r_i(\{i\})\ge0\), then
\(B_i(\sigma^{\infty})\le\liminf_nB_i(\sigma_n)\).

*Proof.* \(B_i(\sigma^{\infty})=\max(\sup_tQ^{\infty}_i(t),
N^{\infty}_i)\). For each fixed \(t\),
\(Q^{\infty}_i(t)=\lim_nQ^{(n)}_i(t)\le\liminf_nB_i(\sigma_n)\) by Lemma
13.1. For the Never value, fix \(\varepsilon>0\). Since the limit's
opponent-absorption measure \(\mu^{-i,\infty}\) has mass \(\le1\), choose
\(T_0\) with \(\mu^{-i,\infty}((T_0,\infty))\le\varepsilon\), so
\(|A^{\infty}_i(t)-N^{\infty}_i|\le R\varepsilon\) for all \(t\ge T_0\);
and since the row masses \(m^{\infty}_t=\mu^{-i,\infty}(\{t\})\) are
summable, choose \(t\ge T_0\) with \(m^{\infty}_t\le\varepsilon\). Then

\[
Q^{\infty}_i(t)\;\ge\;A^{\infty}_i(t)
-2R\,m^{\infty}_t+\rho^{-i,\infty}_{t+1}\,r_i(\{i\})
\;\ge\;N^{\infty}_i-3R\varepsilon,
\]

using Lemma 12.3's row estimate (constant \(2R\)) and
\(r_i(\{i\})\ge0\). Hence
\(N^{\infty}_i\le\liminf_nB_i(\sigma_n)+3R\varepsilon\) for every
\(\varepsilon\). ∎

Without the solo sign the statement fails in general; the general
version carries a correction term built from the escapes of the
\(\mu^{-i}\) measures and is not needed below.

**Definition 13.3 (escape).** Pass to a subsequence along which every
total outcome mass \(\sum_t\Lambda_n(t,S)\) converges, say to
\(\tau(S)\). By Lemma 13.1 and Fatou,
\(\Lambda^{\infty}(S):=\sum_t\Lambda^{\infty}(t,S)\le\tau(S)\); the
*escape* of \(S\) is
\(\operatorname{esc}(S)=\tau(S)-\Lambda^{\infty}(S)\ge0\) — the
absorption mass on \(S\) that drifts to infinity and becomes Never in
the limit.

**Lemma 13.4 (payoff decomposition).**
\(\lim_nU_i(\sigma_n)=U_i(\sigma^{\infty})
+\sum_S\operatorname{esc}(S)\,r_i(S)\).

*Proof.* For fixed \(T\), \(\sum_{t\le T,S}\Lambda_n(t,S)r_i(S)\)
converges to the corresponding sum for \(\sigma^{\infty}\) (Lemma 13.1).
The tail satisfies
\(\sum_{t>T}\Lambda_n(t,S)=\bigl(\sum_t\Lambda_n(t,S)\bigr)
-\sum_{t\le T}\Lambda_n(t,S)
\to\tau(S)-\sum_{t\le T}\Lambda^{\infty}(t,S)\), which decreases to
\(\operatorname{esc}(S)\) as \(T\to\infty\); payoffs are bounded by
\(R\). ∎

**Theorem 13.5 (the bubble is socially nonnegative).** Let \(r\) satisfy
\(r_i(\{i\})\ge0\) for every \(i\), and let \(\sigma_n\) be any
debt-minimizing sequence: \(D(\sigma_n)\to D_*\). Then along every
subsequence as above,

\[
E\;:=\;\sum_S\operatorname{esc}(S)\,\Bigl(\sum_{i\in I}r_i(S)\Bigr)
\;\ge\;0,
\qquad\text{and}\qquad
D(\sigma^{\infty})\;\le\;D_*+E .
\]

*Proof.* By Theorem 13.2 and Lemma 13.4,

\[
d_i(\sigma^{\infty})
=B_i(\sigma^{\infty})-U_i(\sigma^{\infty})
\le\liminf_nB_i(\sigma_n)-\lim_nU_i(\sigma_n)
+\sum_S\operatorname{esc}(S)r_i(S)
=\liminf_nd_i(\sigma_n)+\sum_S\operatorname{esc}(S)r_i(S).
\]

Summing over \(i\) and using
\(\sum_i\liminf\le\liminf\sum=D_*\) gives
\(D(\sigma^{\infty})\le D_*+E\); since \(\sigma^{\infty}\) is an actual
profile, \(D(\sigma^{\infty})\ge D_*\), so \(E\ge0\). ∎

**Corollary 13.6 (attainment for socially nonpositive quitting).** If in
addition \(\sum_ir_i(S)\le0\) for every nonempty \(S\), then \(E=0\),
every escaping coalition has social value exactly \(0\), and every
pointwise-convergent subsequence of a minimizing sequence has a limit
profile that **attains** the exploitability infimum:
\(D(\sigma^{\infty})=D_*\). Compactness of the hazard arrays supplies
such a subsequence; convergence of the original sequence without
selection is not claimed.

**Remark 13.7 (consequences).**

1. *A sign screen on the bubble.* The timing bubble — the mass that the
   ordinary limit converts to Never — can only carry outcomes of
   nonnegative aggregate social value. Any construction (and any
   hypothetical counterexample dynamics, which must live at nonneg
   solos up to the R4 owner) that parks socially destructive outcomes
   in a remote suffix is now excluded: parking is available only for
   socially break-even-or-better coalitions.
2. *A new candidate-design axis.* For tables with all solos \(\ge0\) and
   all social values \(\le0\), minimizing profiles exist. A
   counterexample in that subclass would carry its minimum on an actual
   profile \(\sigma^*\): R5's atoms sit at literal dates of
   \(\sigma^*\), and the sewing problem of §6/§11 loses its
   sequence-indexed character. Either horn is progress: prove the
   subclass has no counterexample (a new positive chamber), or note
   that any counterexample search should try this subclass first,
   since its dynamics cannot hide in the bubble.
3. *For the grafted chain.* The chain's limit debt is controlled by
   \(D_*+E\) with \(E\) the escaped social value of its rounds; making
   the rounds socially nonpositive forces the chain's limit to be
   minimizing — the first quantitative handle on §11's bookkeeping
   question.

## 14. Window deletion and the screening ledger

The graft identity applied at two cuts prices every window of a profile.
Write \(\sigma=\pi\star V\star T\) for cuts \(a\le b\): the prefix
\(\pi\) (dates \(<a\)), the window \(V\) (dates in \([a,b)\)), the tail
\(T\) (dates \(\ge b\)). Let \(\sigma'=\pi\star C\star T\) replace the
window by all-Continue of the same length \(b-a\ge1\).

**Lemma 14.1 (all-Continue window).** For the block \(C\star T\):
\(M^{C}_i=r_i(\{i\})\) (quitting inside \(C\) is a solo exit),
\(W^{C}_i=0\), \(\rho_C=\rho^{-i}_C=1\); hence
\(B_i(C\star T)=\max(r_i(\{i\}),B_i(T))\) and \(U_i(C\star T)=U_i(T)\).

**Theorem 14.2 (exact deletion identity).** With the Lemma 10.1
quantities of \(\pi\) (at cut \(a\)) and of \(V\) (at cut \(b-a\) inside
\(V\star T\)):

\[
U_i(\sigma')-U_i(\sigma)
=\rho_a\bigl[(1-\rho_V)\,U_i(T)-U^{V}_i\bigr],
\]
\[
B_i(\sigma')-B_i(\sigma)
=\max\bigl(M^{\pi}_i,\;W^{\pi}_i+\rho^{-i}_a
\max(r_i(\{i\}),B_i(T))\bigr)
-\max\bigl(M^{\pi}_i,\;W^{\pi}_i+\rho^{-i}_a
\max(M^{V}_i,\,W^{V}_i+\rho^{-i}_VB_i(T))\bigr).
\]

*Proof.* Lemma 10.1 at cut \(a\), then at cut \(b-a\), for both
profiles, with Lemma 14.1 for the \(C\) window. ∎

**Corollary 14.3 (per-window inequality for minimizing sequences).**
For any profile, \(D(\sigma')\ge D_*\) gives, with
\(\varepsilon=D(\sigma)-D_*\ge0\):

\[
\sum_i\bigl(B_i(\sigma')-B_i(\sigma)\bigr)
\;\ge\;\rho_a\Bigl[(1-\rho_V)\sum_iU_i(T)-\sum_iU^{V}_i\Bigr]
\;-\;\varepsilon .
\]

Every window of a near-minimizing profile must therefore either deliver
at least the social payoff its absorbed mass would have collected in the
tail, or perform *screening service*: its deletion must raise aggregate
caps by the deficit. Cap decreases under deletion are possible (a window
can offer collision gains that the tail does not), and then the
delivered-surplus requirement is strict.

**Remark 14.4 (purified rows are fully explicit).** For a purified pair
row (window of length one where exactly \(\{j,o\}\) quits surely,
others continue): \(\rho_V=0\), \(U^{V}_i=r_i(\{j,o\})\),
\(\rho^{-i}_V=0\) for **every** \(i\), and

\[
M^{V}_i=\begin{cases}
r_i(\{j,o\}) & i\in\{j,o\}\\
r_i(\{i,j,o\}) & i\notin\{j,o\},
\end{cases}
\qquad
W^{V}_i=\begin{cases}
r_j(\{o\}),\,r_o(\{j\}) & i=j,\,o\\
r_i(\{j,o\}) & i\notin\{j,o\}.
\end{cases}
\]

So before deletion the tail cap \(B_i(T)\) appears in **no** player's
cap (the row screens the tail completely, §11), while after deletion the
inner cap becomes \(\max(r_i(\{i\}),B_i(T))\) for every player: deleting
a purified mark row re-opens the tail channel for all four players
simultaneously. Corollary 14.3 then reads: for a near-minimizing profile
carrying a purified pair row,

\[
\sum_i\Delta_i
\;\ge\;\rho_a\Bigl[\sum_iU_i(T)-\sum_ir_i(\{j,o\})\Bigr]-\varepsilon,
\]

with \(\Delta_i\) the explicit outer-max differences of Theorem 14.2.
This is the exact bridge between the atlas's paid-row data and the tail
caps: it constrains, in table entries and the single vector
\((U(T),B(T))\), how a mark row, its collision values, and its tail may
coexist near the minimum. Instantiating it along the grafted chain of
§11 — one inequality per round, sharing successive \((U,B)\) vectors —
is the concrete next computation of the bookkeeping program.

**Outlook (variational front).** §13.6 gives attainment for socially
nonpositive tables: there the minimum is an actual profile
\(\sigma^*\), Corollary 14.3 holds at \(\varepsilon=0\) for **every**
window of \(\sigma^*\), and window perturbations other than deletion
(small hazard insertions at inert dates) give further first-order
conditions. Developing this stationarity system at an attained minimizer
is a front the sequence-based frontier could not open, because its
minima were never attained.

## 15. The screening system (program, with inputs separated)

Theorem 14.2 turns every window of every near-minimizing profile into an
inequality among finitely many reals: table entries, the tail's semantic
pair \((U(T),B(T))\), and prefix aggregates
\((M^{\pi}_i,W^{\pi}_i,\rho_a,\rho^{-i}_a)\). Along a minimum-return
round, the tail pairs converge with total debt \(\to D_*\), so the
inequalities pass to exact constraints on the limit data. The program:
collect, per labeled configuration \((j,o,p)\), the deletion
inequalities of the available windows together with the checked round
facts (collider margin, paid-gain floor, zero forced-owner defect, debts
nonnegative summing to \(D_*\)), and test the resulting finite system
for feasibility. Infeasibility for every labeling is a consumption
theorem for the corresponding branch; a feasible point is a concrete
numerical target for construction. This is a necessary-condition
generator of a new kind: its constraints are priced by screening, not by
sign patterns.

**Secured inputs.**

- **Lemma 15.1 (quantitative outsider screen).** At any row whose
  conditional \(\{j,o\}\)-coalition mass is at least \(c\), every
  \(i\notin\{j,o\}\) has \(\rho^{-i}_{V}\le1-c\): deleting \(i\) leaves
  the pair's quit intact, and the pair event implies absorption. ∎
  So outsider cap channels through such a row are damped by \(1-c\),
  with \(c\ge\lambda\) at atlas marks.
- The deletion identity and inequality (Theorem 14.2, Corollary 14.3)
  for arbitrary — in particular impure — rows of the actual realizers,
  which **are** near-minimizing.
- The explicit pure-row form (Remark 14.4).

**Unsecured input, named.** The atlas does not assert that its purified
endpoint profiles are near-minimizing: their whole-profile debt is not
tracked, only their standalone tail debt. Call **N3** the task of
either (a) bounding the whole-profile debt of the purified endpoints
near \(D_*\), or (b) writing the screening system directly on the
impure realizers via the general Theorem 14.2, using Lemma 15.1 for the
screening coefficients. Route (b) needs no new facts and is the
recommended first computation; route (a) would make Remark 14.4's
explicit form directly usable.

**Order of work.** (1) Write the route-(b) system for one round in the
minimum-return mode; (2) close it with the limit constraints
\(\sum_i(b^T_i-u^T_i)=D_*\), \(b^T\ge\) the checked port inequalities
where they apply; (3) only then chain rounds through the graft calculus
of §10, one system per round with shared tail vectors. Step (1) is
carried out in §16.

## 16. The one-round system, with two guardrails

**Guardrail 1 (deleted-observer typing).** The frontier's uniformly
reached paid suffix carries a `liveMass` floor that is the
opponents-only survival \(\rho^{-i}_t\), not the joint reach
\(\rho_t\): the observer may already have quit on the prescribed path.
Such a row belongs to the deleted-\(i\) train of §12 and feeds only
\(B_i\); Theorem 4.2 cannot promote it to an actual full kernel without
a separate owner-survival field. The typing of §12 is load-bearing, not
an API nicety.

**Guardrail 2 (all-Continue-delay regression).** For any paid block
\(\sigma\) in the minimum-fibre all-Continue tube, set
\(\sigma^{H+1}=\mathbf C\star\sigma^{H}\). Every prefix is exact; the
complete semantic pair, the time-forgetting terminal law, the retained
atom, the paid gain, and the suffix entrance probability (one) are all
unchanged; yet the paid row's calendar date tends to infinity and every
fixed calendar row tends to all-Continue. Recentering recovers
\(\sigma\) but forgets the absolute cut and produces no forward
right-extending chronology. Hence uniform reach, terminal-law
tightness, and the train decomposition **alone** cannot resolve the
full-debt temporal escape: a consumer must retain an
extension-compatible absolute cut or produce a bounded-time
restart/return edge. Accordingly, everything below is a
necessary-condition generator; no chronology theorem is claimed.

**The system (route (b), one minimum-return round).** Fixed data: the
table \(r\), the bound \(R\), the symbols \(D_*>0\), the floors
\(\lambda\) (marked stage mass), \(g\) (paid gain), \(\gamma\)
(collider margin), and the labels \((j,o,p)\). Unknowns: the marked row
\(x\in[0,1]^4\); the limit tail pair \((u,b)\in\mathbb
R^4\times\mathbb R^4\); the prefix aggregates
\(\rho_a,\rho^{-i}_a\in[0,1]\), \(U^{\pi},W^{\pi},M^{\pi}\in\mathbb
R^4\). Derived row quantities (explicit polynomials in \(x\)):
\(\rho_V,\ \rho^{-i}_V,\ U^V_i,\ W^V_i,\ M^V_i\) as in §14 for the
one-row window. Constraints:

- (C1) consistency: \(\rho_a\le\rho^{-i}_a\le1\); \(b_i\ge u_i\);
  \(|u_i|,|b_i|,|M^{\pi}_i|\le R\); \(|U^{\pi}_i|\le R(1-\rho_a)\);
  \(|W^{\pi}_i|\le R(1-\rho^{-i}_a)\).
- (C2) mark floor: \(\rho_a\cdot\pi_x(\{j,o\})\ge\lambda\).
- (C3) tail return: \(\sum_i(b_i-u_i)=D_*\).
- (C4) whole-round minimality, with the exact two-cut decompositions
  \(U_i=U^{\pi}_i+\rho_a(U^V_i+\rho_Vu_i)\) and
  \(B_i=\max\bigl(M^{\pi}_i,\;W^{\pi}_i+\rho^{-i}_a
  \max(M^V_i,\,W^V_i+\rho^{-i}_Vb_i)\bigr)\):
  \(\sum_i(B_i-U_i)=D_*\).
- (C5) row-replacement family: for each chosen comparison row
  \(y\in[0,1]^4\), the same formulas with \(V=y\) satisfy
  \(\sum_i(B_i(y)-U_i(y))\ge D_*\). Any finite selection yields valid
  necessary conditions; the natural first selection is \(y=\mathbf C\)
  (Corollary 14.3), the four pure singleton rows, and the pure
  \(\{j,o\}\) row.
- (C6) zero forced-owner defect: \(o\)'s inner maximum is attained at
  the prescribed branch (the alternative row-action value of \(o\) does
  not exceed it).
- (C7) paid gain: \(p\)'s alternative row-action value exceeds \(p\)'s
  prescribed branch value by at least \(g\).
- (C8) table-side facts: the collider margin
  \(r_o(\{j,o\})\ge r_o(\{j\})+\gamma\) and the applicable
  punishment-normality inequalities.

Every constraint containing a maximum splits into finitely many branch
cases (which argument attains); the system is a finite disjunction of
polynomial systems, each decidable in exact rational arithmetic.

**Justification of (C4)–(C5).** The realizing profiles of the round have
whole-profile debt tending to \(D_*\); the two-cut decompositions are
exact identities (Lemma 10.1 twice) and pass to the limit of the
extracted aggregates by continuity of the max formulas; each
row-replacement produces an actual profile, whose debt is \(\ge D_*\),
and the limit of its decomposition is the displayed expression.

**Transcription caveat.** (C6)–(C7) are stated here at the fidelity of
the fact base; before running the computation their exact forms must be
transcribed from the checked packet fields (the payer-defect floor and
the forced-owner zero-defect equation), so that the branch structure
matches the checked quantifiers.

**Status: computed.** The system is implemented in
`one_round_probe.py` (this folder). The implementation first
machine-validates the calculus: the two-cut assembly and the stationary
formulas agree exactly, in rational arithmetic, with a direct
first-principles computation on an explicit profile (`--selftest`).
The probe then found an **exact rational feasible point**, verified in
Fractions and stored in `one_round_probe_point.json` (repro:
`python3 probe_repair.py`): total tail debt \(D_*\approx0.4221\), mark
floor \(\lambda=214/3285\), a fully mixed marked row, all four tail
debts positive. Conclusion, in the review's framing: the
one-round screening system **at this fidelity is feasible**, so
screening alone cannot consume a minimum-return round; the point is a
concrete local model of one round. What the point does *not*
establish: its prefix aggregates are free (realizability by an actual
prefix is unchecked), C6–C7 are at fact-base fidelity, and only six
comparison rows were imposed. An infeasibility consumer must escalate
at least one of: realizable-aggregate constraints; a richer
row-replacement family (up to the full variational family over
\(y\in[0,1]^4\)); the checked C6–C7 quantifiers; or multi-round
chaining through the graft calculus of §10. That escalation order is
the program's next step.

**Falsified at this information level.** An independent exact
rational example
(`../notes/CODEX_STRENGTHEN__IMPURE_FIN4_SCREENING_MAX_BRANCH_FEASIBILITY.md`)
satisfies the one-round max-branch system together with tail and whole-debt
equalities, full support, singleton moats, pair mass, zero owner defect,
paid gain, and the collider signs — on a table that has pure pair
equilibria. Two consequences, recorded in
`../notes/CODEX_ROOT__FIN4_TWO_CHAMBER_PAUSE_STATUS.md` §7: (i) the
whole-round co-indexing (C4) is not a source theorem — the checked
minimum-return source controls the post-mark **tail** debt, not the whole
debt of the profile carrying the pair event; (ii) even with co-indexing
supplied, closing requires an additional universal-minimality perturbation
family or a bound on the payer overshoot \((Q_p-b_p)_+\). The screening
route is to be revisited only after one of those is added.
