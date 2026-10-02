# Finite completion atlas

Author: `CHATGPT_EXTERNAL`

Status: `MATH_REVIEWED`; ordinary-mathematics classification, not a Fin4 consumer.

Source: supplied as `ephemeral/SOURCE_PRESERVING_ATLAS.md` and moved here without
rewriting the mathematical body.

There is a source-preserving atlas with **three modes and two terminal strongly connected components**. Its decisive change of state language is to store a **cofinal stream of actual source rows**, rather than treating each one-time endpoint refinement as a new atlas source.

The result is the following ordinary-mathematics reduction.

$$
\boxed{
\neg\mathrm{UE}(r)
\Longrightarrow
\mathrm{UniformEscapeRealizable}(r)
\;\lor\;
\mathrm{MinimumReturnRealizable}(r).
}
$$

Both alternatives retain one fixed positive-gap witness, one fixed global minimum semantic/law source, one literal source chronology, cofinally increasing source ranks, fixed player labels after extraction, and exact forced-pair and payer updates. They differ only in whether the post-row debt excess stays uniformly positive or tends to zero.

The construction uses no `RankExit`. Thus it also avoids two gaps in the abstract template:

* a natural rank decreasing only on rank transitions does not prevent infinitely many rank transitions if regular transitions may reset the rank;
* an arbitrary path in a finite directed graph need not eventually enter a terminal SCC—it can remain inside a nonterminal SCC while never taking an available exit.

Here the only nonterminal mode leaves in one regular step, and the only cycles are the two terminal self-shifts.

The existing checked source supplies the hard residual, minimum source, causal atom, exact cap-prefix data, pure screening, forced-pair update, and collision-tail identity. The stream packaging and finite stabilization below are new ordinary-mathematics lemmas; I do not claim that the proposed declarations have yet been Lean-compiled. The source audit below is against current `main` at `64be03405aa605f9317b7aeaece64a7dc307b375`.

---

## 1. Terminal conclusion and certified counterexample

For a reward table \(r\), write

$$
\operatorname{ApproxTerminal}(r)
$$

for the existence of one \(v\in\mathbb R^4\) such that for every \(\varepsilon>0\) there is a behavioral profile \(\sigma_\varepsilon\) satisfying

$$
\max_i\bigl(B_i(\sigma_\varepsilon)-U_i(\sigma_\varepsilon)\bigr)\le \varepsilon,
\qquad
\max_i|U_i(\sigma_\varepsilon)-v_i|\le \varepsilon .
$$

Define `FinFourCompletionTerminal r` as the disjunction of:

1. `ApproxTerminal r`;
2. an actual uniform-equilibrium payoff;
3. an exact positive admissible return accepted by an existing checked uniform-payoff compiler.

Only the first conclusion is needed by the two capstones below.

A certified counterexample is

$$
\operatorname{CertifiedGap}(r)
 :=
 \left\{
 (\gamma,h):
 \gamma>0,\quad
 \forall\sigma\ \exists i,\ 
 B_i(\sigma)-U_i(\sigma)\ge\gamma
 \right\}.
$$

Every nonterminal packet below contains such a witness through its retained hard residual.

---

## 2. The finite mode type

```lean
inductive FinFourCompletionMode
  | cofinalSingleton
  | uniformEscape
  | minimumReturn
```

The mathematical meanings are:

| Mode               | Meaning                                                                                                  |
| ------------------ | -------------------------------------------------------------------------------------------------------- |
| `cofinalSingleton` | One fixed minimum source produces cofinally many actual singleton rows of one fixed positive mass scale. |
| `uniformEscape`    | The corresponding forced-pair collision tails stay above the minimum by one fixed positive amount.       |
| `minimumReturn`    | The corresponding forced-pair collision-tail debts converge back to the global minimum.                  |

The latter two modes will be the terminal components.

---

## 3. Common retained source

Every packet carries a bound \(M\), an exact nonmonodromy entrance residual, and the exact `FinFourMinimumAtomProducer` occurring inside that entrance residual.

Unpacked, the source contains:

* the original reward table \(r\);
* a fixed all-behavior terminal-gap witness;
* a selected joint semantic/law point

  $$
  (z_*,\nu_*)\in K^{\mathrm{law}}(r);
  $$
* the semantic carrier membership of \(z_*\);
* global minimality

  $$
  D(z_*)\le D(z)
  \quad
  \text{for all }z\in K(r);
  $$
* the positive minimum

  $$
  D_*:=D(z_*)=\inf_{\sigma}D(\sigma)>0;
  $$
* one nonempty terminal coalition \(A\);
* its fixed positive law mass

  $$
  \mu:=\nu_*(A)>0;
  $$
* one causal chronology realizing that exact joint point and atom, including actual profiles, cutoffs, marked suffix dates, exact cap–Nash root words of length \(n+1\), convergence to \((z_*,\nu_*)\), convergence of the prefixed debts to \(D_*\), and literal survival of the atom after the exact root word.

These are exactly the fields of `FinFourMinimumAtomProducer`; its construction retains the supplied hard residual literally.

The checked entrance can first be contracted to

```text
FinFourProducerResidualWithoutMonodromy
```

with only the minimum-singleton, purified-singleton, terminal-singleton, and tail-escape constructors. The same-stage monodromy constructors are refuted, not redirected.

Every completion packet stores the entire entrance residual even when only its common source is used later. Thus a purified row, terminal orbit, or tail subsequence is not discarded and then existentially reconstructed.

Set once and for all

$$
\lambda:=\frac{\mu^2}{8}>0.
$$

---

## 4. `cofinalSingleton` packets

A packet in this mode contains the common source and one of the following two exact origins.

### 4.1 Singleton-atom origin

When \(|A|=1\), write \(A=\{j\}\). The packet carries:

* one `FinFourOwnerCompressedSingletonProducer` built from the source’s own causal chronology;
* a sequence of owner-compressed endpoints \(E_n\);
* their source ranks \(k_n\), with

  $$
  k_0<k_1<k_2<\cdots;
  $$
* for each \(n\):

  * the exact source suffix profile;
  * the retained exact cap–Nash root stack;
  * the literal prefixed reference profile \(\sigma_n\);
  * the marked date \(t_n\);
  * the literal one-date owner-compressed target \(\tau_n\);
  * the singleton terminal \(S_n=A=\{j\}\);
  * the mass bound

    $$
    \lambda<
    \Pr_{\tau_n}(S_n\text{ occurs at }t_n);
    $$
  * equality of every complete behavioral strategy away from \(t_n\);
  * equality of every post-\(t_n\) live root and continuation tail with the reference source.

The endpoints are selected recursively with requested depth \(k_n+1\), exactly as in the existing cofinal endpoint construction. The checked theorem already proves strict increase of their actual source ranks.

The owner-compression endpoint itself retains the chronology profiles, cutoffs, roots, root-stack Nash proof, prefix-debt convergence, selected source rank, marked date, and literal one-date target.

### 4.2 Nonsingleton-atom origin

When \(|A|>1\), the packet carries one fixed `SelectedRows` object based on the exact chronology retained by the source. In particular, it retains:

* the same chronology profiles;
* the same exact cap–Nash root words;
* their lengths;
* the same prefixed-debt convergence;
* one marked suffix date at every source rank;
* exact transport of the suffix atom through the root word.

The selected-row structure stores these fields explicitly.

Its eventual mass theorem gives an \(N\) such that, for all \(k\ge N\),

$$
\lambda<
\Pr_{\sigma_k}(A\text{ occurs at its shifted marked date}).
$$

Choose \(k_n=N+n\). At every such row apply the checked pure nonsingleton screening theorem. It gives:

* a complete same-date screening orbit;
* at most three strict profitable preterminal edges;
* exact mover-debt subtraction on every such edge;
* no loss of marked mass;
* a final literal singleton \(S_n\);
* a target profile \(\tau_n\) which is exactly the pure \(S_n\)-root over the original actual profile;
* equality with the original profile at every other date;
* the mass bound

  $$
  \lambda\le
  \Pr_{\tau_n}(S_n\text{ occurs at }t_n).
  $$

The final pair-to-singleton route need not be profitable; profitability is not used by the atlas. The checked endpoint gives the literal singleton and full source attachment unconditionally.

### 4.3 Common packet interface

Both origins expose, for every \(n\):

$$
(k_n,\sigma_n,\tau_n,t_n,S_n,W_n),
$$

where:

1. \(k_n\) is strictly increasing;
2. \(W_n\) is the original exact cap–Nash word and

   $$
   |W_n|=k_n+1;
   $$
3. \(\sigma_n\) and \(\tau_n\) are literal actual profiles;
4. \(|S_n|=1\);
5. \(\tau_n\) differs from \(\sigma_n\) only at \(t_n\);
6. the post-date continuation of \(\tau_n\) is literally the selected source continuation;
7. the complete semantic pairs, unrestricted cap vectors, terminal laws, and player-deleted terminal laws are those computed from these actual profiles;
8. \(\lambda\) is a lower bound for the singleton mass;
9. the source-front debts satisfy

   $$
   D(\sigma_n)\longrightarrow D_*.
   $$

No target-side cap–Nash assertion is inserted.

### Cofinal singleton entrance theorem

$$
\boxed{
\text{Every nonmonodromy Fin4 producer residual produces a }
\texttt{cofinalSingleton}\text{ packet on the same source.}
}
$$

The proof is precisely the cardinality split above. No compact carrier point, law, chronology, or reward table is reselected.

---

## 5. The source-attached forced-pair row

The outgoing theorem for `cofinalSingleton` uses the following local construction on every frame.

Let \(S_n=\{j_n\}\). Pureify the marked row simultaneously to the literal singleton \(S_n\); this does not change the reached live mass or anything after \(t_n\).

The hard residual gives a player \(q_n\ne j_n\) satisfying the full table-gap inequality

$$
r_{q_n}(\{j_n,q_n\})
\ge
r_{q_n}(\{j_n\})+\gamma ,
$$

where \(\gamma>0\) is the fixed terminal-gap witness.

Let \(A_n^q\) be the exact best-endpoint adapter for \(q_n\). At the pure singleton row, the inequality above forces

$$
A_n^q.\mathrm{action}=\mathrm{Quit},
\qquad
A_n^q.\mathrm{routedTerminal}=\{j_n,q_n\}.
$$

The pair keeps the complete marked live mass, and the actual \(q_n\)-gain satisfies

$$
g_n^q\ge \lambda\gamma>0.
$$

At this pure pair, the forced owner \(q_n\) has zero marked coordinate defect. Global minimality and the pure-nonsingleton debt identity give

$$
D_*
\le
\sum_{i\ne q_n}
\delta_i^{(n)} .
$$

There are exactly three summands. Hence one player \(p_n\ne q_n\) satisfies

$$
\delta_{p_n}^{(n)}\ge \frac{D_*}{3}.
$$

Let \(A_n^p\) be the exact best-endpoint adapter for \(p_n\). Store its actual target profile and gain \(g_n^p\). Then

$$
g_n^p
=
L_n\,\delta_{p_n}^{(n)}
\ge
\lambda\frac{D_*}{3}>0,
$$

where \(L_n\ge\lambda\) is the reached live mass, and

$$
d_{p_n}(\text{paid target})
=
d_{p_n}(\text{forced pair})-g_n^p
$$

exactly. Every player strategy away from the one marked date is unchanged, and the full marked mass is routed exactly.

This is the local content already proved by `FinFourWeakCoreForcedPairPacket`: the literal forced pair, zero forced-owner defect, payer floor, positive gain, exact payer-debt subtraction, exact one-date profile equality, and post-date source-tail identity are all checked.

Because the first routed terminal is a genuine pair, the concentrated singleton compiler cannot take its singleton strategic arm. It produces a collision-minimum residual \(C_n\) on that same literal packet. For the constant packet sequence used by the adapter, its cluster is exactly the actual post-date semantic tail:

$$
C_n.\mathrm{cluster}
=
T_n
:=
\operatorname{Sem}
\bigl(
\operatorname{Spine}(\tau_n,t_n+1)
\bigr).
$$

The checked minimum-tail consumer proves both the existence of this residual and this exact identity.

Define its excess

$$
e_n:=D(T_n)-D_*.
$$

Since \(T_n\) belongs to the semantic carrier and \(z_*\) is globally minimal,

$$
e_n\ge0.
$$

The complete forced-pair row stored by the new atlas therefore consists of:

```text
parent source frame
singleton owner jₙ
pure singleton profile
forced outsider qₙ
full table-gap inequality
forced adapter and action = Quit
literal pair {jₙ,qₙ}
forced-owner actual gain
forced-owner zero marked defect
payer pₙ ≠ qₙ
payer adapter and Boolean action
payer defect ≥ D*/3
payer gain ≥ λ D*/3
exact payer-debt subtraction
source, pair, and paid target semantic pairs
complete terminal and deleted laws
collision-minimum residual Cₙ
Cₙ.cluster = the literal post-date source tail Tₙ
nonnegative excess eₙ
```

No cap of another player is asserted to decrease.

---

## 6. Exhaustive stream dispatch

Choose one forced-pair row at every frame. This is countable choice over actual local nonempty types.

First stabilize the finite labels. The color

$$
c_n=(j_n,q_n,p_n,a_n)
\in
(\operatorname{Fin}4)^3\times\{\mathrm{Continue},\mathrm{Quit}\}
$$

takes values in a finite set. Hence there are:

* fixed \(j,q,p,a\);
* a strictly increasing map \(\phi:\mathbb N\to\mathbb N\);

such that all four labels are constant on the reindexed rows.

Replace the stream by this literal subsequence. Its source ranks remain strictly increasing because \(k_n\) and \(\phi\) are strictly increasing.

Now apply the following exhaustive scalar lemma to \(e_n\ge0\).

### Nonnegative stream dichotomy

Exactly one of the following constructions is available.

#### Uniform escape

There exist \(\delta>0\) and a further strict subsequence such that

$$
e_n\ge\delta
\quad\text{for every retained }n.
$$

This happens when \(e_n\ge\delta\) occurs frequently for some \(\delta>0\).

#### Minimum return

Otherwise, for every \(\delta>0\), eventually \(e_n<\delta\). Since \(e_n\ge0\),

$$
e_n\longrightarrow0,
\qquad\text{equivalently}\qquad
D(T_n)\longrightarrow D_* .
$$

No semantic compactification is used in this dichotomy. It is a statement about the actual collision tails already stored in the source stream.

This proves the exhaustive dispatch

$$
\boxed{
\texttt{cofinalSingleton}
\longrightarrow
\texttt{uniformEscape}
\quad\text{or}\quad
\texttt{minimumReturn}.
}
$$

The child packet stores:

* the entire parent packet;
* the exact strict index embedding;
* every selected forced-pair row;
* equalities identifying every child profile, mark, root stack, law, and tail with the corresponding parent object.

Thus the transition cannot substitute an unrelated profile or carrier representative.

---

## 7. Terminal-mode packets and their shifts

### `uniformEscape`

A packet consists of the stabilized forced-pair stream above and a fixed \(\delta>0\) satisfying

$$
D(T_n)\ge D_*+\delta
\quad
\text{for all }n.
$$

### `minimumReturn`

A packet consists of the stabilized forced-pair stream above and

$$
D(T_n)\longrightarrow D_*.
$$

This includes the exact-minimum case \(D(T_n)=D_*\) as well as strictly off-minimum tails whose excess vanishes.

For either terminal mode define `drop P` by

$$
(\operatorname{drop}P).\mathrm{row}(n)=P.\mathrm{row}(n+1).
$$

All common source data, fixed labels, mass floors, cap vectors, laws, exact identities, and convergence or uniform-excess proofs are inherited by restriction. In particular,

```text
drop P.source        = P.source
drop P.row n         = P.row (n + 1)
drop P.sourceRank n  = P.sourceRank (n + 1)
```

definitionally or by displayed equality.

These are the regular self-transitions

$$
\texttt{uniformEscape}\to\texttt{uniformEscape},
\qquad
\texttt{minimumReturn}\to\texttt{minimumReturn}.
$$

The backward compiler for every regular transition is the identity on the reward-level terminal conclusion: the parent and child concern the same reward table.

`RankExit` is the empty type. No real-valued or renewable natural descent is being claimed.

---

## 8. Exhaustive dispatch theorem

In Lean-facing form, the theorem is:

```lean
theorem FinFourCompletionAtlas.dispatch
    {m : FinFourCompletionMode}
    (P : FinFourCompletionPacket m reward) :
    FinFourCompletionTerminal reward
      ∨ FinFourCompletionRankExit P
      ∨ (∃ m' (Q : FinFourCompletionPacket m' reward),
            FinFourCompletionRegularStep P Q)
      ∨ FinFourCompletionCertifiedCounterexample reward
```

with the following actual implementation:

```text
cofinalSingleton:
  RegularSuccessor uniformEscape
  or
  RegularSuccessor minimumReturn

uniformEscape:
  RegularSuccessor (drop P)

minimumReturn:
  RegularSuccessor (drop P)
```

Every emitted regular successor contains the parent packet and literal child-index equations. There is no edge inferred merely from compatible mode names.

Coverage is:

```lean
theorem FinFourCompletionAtlas.coverage :
  FinFourCompletionTerminal reward
    ∨ ∃ m, Nonempty (FinFourCompletionPacket m reward)
```

and under the positive-gap/no-uniform-payoff hypothesis its packet output is initially in `cofinalSingleton`.

The checked repository currently stops earlier: `uniformPayoff_or_nonempty_finFourProducerResidual` explicitly asserts only producer coverage, and the current umbrella explicitly says no uniform-payoff completion or renewable normalized-inert descent is provided.

---

## 9. The regular mode graph

The complete allowed-edge matrix is

$$
\begin{array}{c|ccc}
 & C & E & R\\ \hline
C & 0 & 1 & 1\\
E & 0 & 1 & 0\\
R & 0 & 0 & 1
\end{array}
$$

where

$$
C=\texttt{cofinalSingleton},\qquad
E=\texttt{uniformEscape},\qquad
R=\texttt{minimumReturn}.
$$

Equivalently,

```text
C ───▶ E ↻
│
└────▶ R ↻
```

There are no other regular edges.

A useful mode height is

$$
h(C)=1,\qquad h(E)=h(R)=0.
$$

Every regular transition outside a terminal component strictly lowers this height. Therefore the graph does not require a fairness assumption.

Its SCCs are:

$$
\{C\},\qquad \{E\},\qquad \{R\}.
$$

The terminal SCCs are exactly

$$
\boxed{\{E\},\ \{R\}.}
$$

The condensation graph is the finite acyclic graph

$$
\{C\}\longrightarrow\{E\},
\qquad
\{C\}\longrightarrow\{R\}.
$$

---

## 10. Exact terminal-component realization

For \(X\in\{E,R\}\), define

$$
\operatorname{Realizable}_X(r)
$$

to mean that there exist a bound, an \(X\)-packet \(P\), and a sequence of packets \(P^{(n)}\) such that

$$
P^{(0)}=P,
\qquad
P^{(n+1)}=\operatorname{drop}P^{(n)},
$$

and every displayed equality in the regular-step constructor holds.

The canonical realization is

$$
P^{(n)}=\operatorname{drop}^n(P).
$$

It is source coherent in the strong literal sense:

* the reward table is unchanged;
* the positive-gap witness is unchanged;
* \(z_*,\nu_*,D_*,A,\mu,\lambda\) are unchanged;
* the source chronology is unchanged;
* the \(n\)-th child row is an explicitly indexed row of the parent stream;
* all profiles, cap vectors, laws, marks, and collision clusters are inherited, not reselected.

### Terminal-component reduction theorem

$$
\boxed{
\neg\exists v\,
  \operatorname{IsUniformEquilibriumPayoff}(r,v)
\ \Longrightarrow\
\operatorname{Realizable}_E(r)
\ \lor\
\operatorname{Realizable}_R(r).
}
$$

**Proof.**

1. Apply the checked nonmonodromy coverage theorem.
2. The uniform-payoff arm contradicts the hypothesis.
3. Retain the exact source inside the returned residual.
4. If its atom is a singleton, construct the cofinal owner-clock stream.
5. If its atom is nonsingleton, apply pure screening cofinally on one fixed selected-row family.
6. This gives a `cofinalSingleton` packet.
7. Apply the forced-pair construction at every row.
8. Stabilize the finite labels.
9. Apply the nonnegative stream dichotomy.
10. Obtain an \(E\)-packet or an \(R\)-packet.
11. Iterate `drop`.

Every object is on the original reward table and descends from the original source chronology. ∎

Because there are no rank transitions and \(C\) exits in one step, this proves the requested result for arbitrary infinite paths without relying on the invalid generic rank-reset or terminal-SCC assertions.

---

## 11. The two capstone questions

### Capstone E: uniform tail-escape return

> **UniformEscapeCapstone.**
> For every Fin4 reward table and every source-attached `uniformEscape` packet, produce `FinFourCompletionTerminal reward`.

Expanded, the hypothesis gives:

* one positive all-behavior gap witness;
* one global positive minimum \(D_*\);
* one cofinal literal source chronology;
* fixed players \(j,q,p\);
* a fixed singleton-to-pair table gap;
* a fixed mass floor \(\lambda>0\);
* forced pair rows and exact paid payer endpoints;
* exact payer-debt subtraction by at least \(\lambda D_*/3\);
* collision tails \(T_n\) with

  $$
  D(T_n)\ge D_*+\delta
  $$

  for one fixed \(\delta>0\);
* literal post-date source provenance.

The mathematical task is to charge the repeated fixed-size off-minimum excursion to an exact source-matched return, or directly compile terminal approximate Nash profiles.

A negative answer must exhibit a concrete \(r\) and such a packet. Its retained hard-residual witness already proves a fixed positive exploitability gap against every behavioral profile.

### Capstone R: minimum-return cap leakage

> **MinimumReturnCapstone.**
> For every Fin4 reward table and every source-attached `minimumReturn` packet, produce `FinFourCompletionTerminal reward`.

Its hypothesis gives all the fixed forced-pair and payer data above, but now

$$
D(T_n)\longrightarrow D_*.
$$

This is the exact renewable formulation of the cross-coordinate cap-leakage problem: one player loses at least \(\lambda D_*/3\) debt at every paid row, while the other unrestricted caps may absorb the loss, and the actual continuation tails return to the minimum region.

Again, a negative answer is a concrete all-behavior positive-gap table because the packet contains the witness itself.

### Global implication

If both capstones are resolved positively and some Fin4 table \(r\) had no uniform-equilibrium payoff, the terminal-component reduction would produce an \(E\)- or \(R\)-realization. The corresponding capstone would produce a terminal conclusion, contradicting the fixed positive gap. Hence:

$$
\boxed{
\text{UniformEscapeCapstone}
\ \land\
\text{MinimumReturnCapstone}
\quad\Longrightarrow\quad
\text{Fin4 uniform-equilibrium conjecture}.
}
$$

A valid concrete negative answer to either capstone refutes the conjecture.

---

## 12. Where the current downstream nodes went

They are not omitted. They become internal certificates of the two recurrent stream components.

### Concentrated collision packet

Every forced-pair row in both \(E\) and \(R\) contains the actual `QuittingConcentratedCollisionMinimumResidual`, together with the exact equality between its cluster and the literal post-date tail. It is therefore represented row by row, with cofinal renewal.

### Forced pair and unique-all-Continue inert point

The forced pair is the common structural core of both terminal components. The normalized unique-all-Continue inert minimizer is a compact refinement of the \(R\)-component, after selecting a convergent decorated subsequence.

The checked normalized-return theorem produces either an actual three-role endpoint-law branch or a strict inert minimizer, but explicitly does not produce a recursive completion.

### Three-role endpoint law

This remains an internal \(R\)-certificate. When its target debt equals \(D_*\), the checked theorem causalizes the endpoint’s own routed law atom and constructs a new `FinFourMinimumAtomProducer` at that exact target point, retaining the same hard residual. There is no rank orientation, so this is a recurrent regeneration mechanism rather than a rank exit.

The stream-level atlas does not need to pretend that this regeneration is a descent: the parent \(R\)-stream remains available throughout.

### One-time support handoff

The current support-rank handoff is explicitly one-time and does not reconstruct a renewable canonical-pair source.

It is therefore not a regular atlas edge. It is a certificate attached to an \(R\)-packet. Any future consumer may use it while retaining the complete parent stream. No source reconstruction is needed merely to keep the atlas closed.

### Tent toll and fixed-cap barrier

The exact gain-to-mass identity and single-density tent inequality are predicates on the normalized minimizer derived from an \(R\)-packet. The checked file itself says that it does not consume the strict arm or construct terminal approximations.

They are invariants inside the minimum-return capstone, not successor modes.

### Strict-ray positive roots, cardinality three, and full binding

The maximal-prefix ray and strict-ray packages are also refinements of the \(R\)-component. The maximal-ray strict arm presently has no downstream completion.

The binding-cardinality result is conditional on a parity certificate that the present source does not construct; its honest output is a positive-absorption exact limiting root, full binding, or binding cardinality three.

All three remain inside the same retained \(R\)-stream. They are not counted as eliminated and are not used as unproved source transitions.

### Monodromy

It is absent from the mode type. The checked impossibility theorem is used only to justify the contracted entrance and the pure-screening endpoint; it is not a live SCC.

---

## 13. Lean-facing interface

A direct formal interface is:

```lean
inductive FinFourCompletionMode
  | cofinalSingleton
  | uniformEscape
  | minimumReturn

FinFourCofinalSingletonOrigin
FinFourCofinalSingletonPacket
FinFourForcedPairStreamRow
FinFourStabilizedForcedPairStream
FinFourUniformEscapePacket
FinFourMinimumReturnPacket

FinFourCompletionPacket
FinFourCompletionTerminal
FinFourCompletionCertifiedCounterexample

-- No constructors.
FinFourCompletionRankExit

FinFourCompletionRegularStep.classifyUniformEscape
FinFourCompletionRegularStep.classifyMinimumReturn
FinFourCompletionRegularStep.dropUniformEscape
FinFourCompletionRegularStep.dropMinimumReturn

FinFourCompletionAtlas.coverage
FinFourCompletionAtlas.dispatch
FinFourCompletionAtlas.modeGraph
FinFourCompletionAtlas.terminalComponents
FinFourCompletionAtlas.counterexample_enters_terminalComponent

FinFourUniformEscapeCapstone
FinFourMinimumReturnCapstone
FinFourCompletionAtlas.all_capstones_imply_finFour
```

The genuinely new formal lemmas are limited to:

1. cofinal application of pure nonsingleton screening on one fixed retained `SelectedRows`;
2. the origin-independent singleton-frame version of the forced-pair proof;
3. finite-label stabilization followed by the nonnegative excess dichotomy;
4. stream restriction and the three-vertex SCC computation.

The game-theoretic inequalities and source identities used by those lemmas are already present in the checked declarations cited above. No repository changes were made, and I am not labeling the proposed interface as compiled or axiom-clean without the validation required by the project runbook. 
