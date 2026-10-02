# Never deletion and the summable-port boundary

Author: `CHATGPT_EXTERNAL`

Status: `PROOF_DRAFT`; conditional lemma and audit, not an exhaustive producer.

Source: supplied as `ephemeral/NEVER_DELETION.md` and moved here without
rewriting the mathematical body.

## Verdict

Three points survive the audit.

1. **The conditional Never-deletion lemma is correct**, and one of its five hypotheses is unnecessary:

   $$
   U_w(x_2)\ge \chi_w
   $$

   is not needed to prove that \(y_w\) is a minimum-fiber support descent. It is needed only if the entire interpolation from \(x_2\) to \(y_w\) must remain punishment-floor admissible.

2. **Failure of the displayed \(g,\kappa,q\) tests cannot be used contrapositively.** They are one-sided lower and upper bounds obtained from different extrema. A failed bound need not correspond to any actual payoff loss, cap increase, complementary pair, or common behavioral deviation.

3. **The exhaustive producer theorem is not closed by the cited declarations.** After replacing all five coarse failures by exact same-profile quantities, every non-descent endpoint can be put on one literal, quantitatively paid, exact punishment-floor cap orbit. But the positive-minimum debt budget forces that orbit into the **summable all-Continue port** arm, whose restart or rank consumer is still open. The repository itself records that restarting or otherwise consuming this paid port remains unresolved.

Thus I obtain a sharper conditional theorem and an exact reduction to one residual, but not one of the three complete deliverables requested. I also do not obtain a realizable counterexample: under the full hypotheses, such a construction would itself be a finite quitting game without a uniform-equilibrium payoff.

---

# 1. Exact verification of the Never-deletion lemma

Write

$$
z_k=\operatorname{Sem}(x_k),\qquad
d_i^k=B_i(x_k)-U_i(x_k),
$$

and fix \(w\in W\). Let

$$
y=y_w=x_2[w\leftarrow\mathrm{Never}].
$$

Define the **actual** changes

$$
G_i^w:=U_i(y)-U_i(x_2),
\qquad
K_i^w:=B_i(y)-B_i(x_2).
\tag{1}
$$

Then the exact debt identity is

$$
d_i(y)=d_i^2+K_i^w-G_i^w.
\tag{2}
$$

The point of \(g_i^w\) and \(\kappa_i^w\) is that they bound the two exact terms in (2).

## 1.1 Actual payoff gain

Realize the five behavioral strategies of \(x_2\) by independent complete stopping times

$$
Q_i\in\mathbb N\cup\{\infty\}.
$$

Couple \(x_2\) and \(y\) by retaining \(Q_i\) for \(i\ne w\) and replacing \(Q_w\) by \(\infty\).

There are four samplewise cases.

* If an opponent coalition stops strictly before \(w\), the terminal coalition is unchanged.
* If \(w\) ties at the first stopping date with a nonempty
  \(T\subseteq I\setminus\{w\}\), the outcome changes from \(T\cup\{w\}\) to \(T\).
* If \(w\) is the unique first quitter, the outcome changes from \(\{w\}\) to some later
  \(T\subseteq I\setminus\{w\}\), including \(T=\varnothing\) if everybody else plays Never.
* If everybody plays Never, nothing changes.

Consequently, for every player \(i\),

$$
G_i^w
\ge
\sum_{\varnothing\ne T\subseteq I\setminus\{w\}}
\mu_2(T\cup\{w\})
  \bigl(r_i(T)-r_i(T\cup\{w\})\bigr)
+\mu_2(\{w\})m_i^w
=
g_i^w(x_2).
\tag{3}
$$

This uses the actual terminal law of the literal \(x_2\); no semantically equivalent realization is substituted.

## 1.2 Unrestricted cap exposure

Fix \(i\ne w\) and an arbitrary behavioral deviation \(\tau_i\). Couple

$$
y[i\leftarrow\tau_i]
\quad\text{and}\quad
x_2[i\leftarrow\tau_i]
$$

by the same stopping times, changing only \(Q_w\) to \(\infty\).

The samplewise payoff increase of player \(i\) is at most \(\kappa_i^w\). Indeed, the only changed outcomes are exactly

$$
T\cup\{w\}\longmapsto T
$$

and

$$
\{w\}\longmapsto T,\qquad
T\subseteq I\setminus\{w\},
$$

and both classes occur in the definition of \(\kappa_i^w\). Therefore

$$
U_i\bigl(y[i\leftarrow\tau_i]\bigr)
\le
U_i\bigl(x_2[i\leftarrow\tau_i]\bigr)+\kappa_i^w.
$$

Taking the supremum over **all** behavioral \(\tau_i\) gives

$$
K_i^w\le\kappa_i^w,\qquad i\ne w.
\tag{4}
$$

This includes Never, arbitrarily late deterministic stopping, randomized stopping times, and every history-dependent hazard sequence available in a quitting game.

For \(w\), the opponents are literally unchanged:

$$
\operatorname{Function.update}(y,w,\tau_w)
=
\operatorname{Function.update}(x_2,w,\tau_w).
$$

Hence

$$
K_w^w=0.
\tag{5}
$$

## 1.3 Closing \(w\)'s debt

Because \(y\) itself is a unilateral deviation by \(w\) from \(x_2\),

$$
G_w^w\le B_w(x_2)-U_w(x_2)=d_w^2.
\tag{6}
$$

If

$$
g_w^w(x_2)\ge d_w^2,
$$

then (3) and (6) give

$$
d_w^2
\le g_w^w(x_2)
\le G_w^w
\le d_w^2.
$$

Thus all terms are equal and

$$
d_w(y)
=d_w^2-G_w^w
=0.
\tag{7}
$$

For \(i\ne w\), equations (2)–(4) give

$$
d_i(y)
\le d_i^2+\kappa_i^w-g_i^w(x_2)
\le q_i^w.
\tag{8}
$$

## 1.4 Global minimality and support descent

Assume

$$
\sum_{i\ne w}q_i^w\le D_0.
$$

Using (7) and (8),

$$
D(\operatorname{Sem}(y))
\le
\sum_{i\ne w}q_i^w
\le D_0.
\tag{9}
$$

But \(y\) is an actual profile for the same reward table, so its semantic pair lies in the terminal-semantic carrier. Global minimality of \(z_0\) gives

$$
D_0\le D(\operatorname{Sem}(y)).
\tag{10}
$$

Therefore

$$
D(\operatorname{Sem}(y))=D_0.
\tag{11}
$$

Let

$$
A_0:=\operatorname{supp}^{+}d(z_0).
$$

If

$$
q_j^w=0\qquad(j\notin A_0),
$$

then nonnegativity of terminal semantic debt and (8) imply

$$
d_j(y)=0
\qquad(j\notin A_0).
\tag{12}
$$

Together with \(d_w(y)=0\) and \(w\in A_0\),

$$
\operatorname{supp}^{+}d(\operatorname{Sem}(y))
\subseteq A_0\setminus\{w\},
$$

so

$$
\left|\operatorname{supp}^{+}d(\operatorname{Sem}(y))\right|
<
|A_0|.
\tag{13}
$$

This proves the requested conditional endpoint result.

## 1.5 The punishment-floor hypothesis is not used

Notice that

$$
U_w(x_2)\ge\chi_w
$$

appeared nowhere in (3)–(13). Hence the sharper statement is:

$$
\boxed{
\begin{aligned}
&w\in A_0,\quad
g_w^w(x_2)\ge d_w^2,\quad
\sum_{i\ne w}q_i^w\le D_0,\\
&\forall j\notin A_0,\ q_j^w=0
\end{aligned}
}
\Longrightarrow
\text{minimum-fiber strict support descent.}
\tag{14}
$$

The floor condition becomes relevant only for the full whole-stopping-law homotopy

$$
x_2^\theta
=
x_2\!\left[
w\leftarrow
(1-\theta)(x_2)_w+\theta\,\mathrm{Never}
\right].
$$

For \(w\), the cap remains constant and the prescribed payoff is affine, so under (7),

$$
d_w(x_2^\theta)=(1-\theta)d_w^2,
\qquad
U_w(x_2^\theta)=U_w(x_2)+\theta d_w^2.
$$

Thus \(U_w(x_2)\ge\chi_w\) implies floor safety for every \(\theta\). For every other player, the prescribed payoff is affine and the unrestricted cap is convex under whole-stopping-law mixing. This is again control against arbitrary behavioral deviations, not merely stationary ones.

The cancellation is appended after \(x_2\). Therefore neither literal reset

$$
x_0\longrightarrow x_1,
\qquad
x_1\longrightarrow x_2
$$

is changed, and the second reset retains its literal source \(x_1\). The quarter-retention statement remains true at \(x_2\); no retention after the final Never replacement is needed for the support-drop proof. The checked two-reset theorem itself exports literal profiles and retention but explicitly does not perform a cardinal reduction.

---

# 2. The exact semantic endpoint alternative

The coarse quantities should be separated from the exact endpoint behavior.

From (1)–(2),

$$
d_w(y)=d_w^2-G_w^w,
\tag{15}
$$

and, for \(i\ne w\),

$$
d_i(y)=d_i^2+K_i^w-G_i^w.
\tag{16}
$$

The exact alternative is:

$$
\boxed{
\begin{aligned}
&\operatorname{Sem}(y_w)
\text{ is a global minimum with strict support drop}\\
&\quad\lor\\
&\Bigl[
w\notin A_0
\ \lor\
d_w(y_w)>0
\ \lor\
D(\operatorname{Sem}(y_w))>D_0\\
&\hspace{42mm}
\lor\
\exists j\notin A_0,\ d_j(y_w)>0
\Bigr].
\end{aligned}
}
\tag{17}
$$

Indeed, if the second bracket is false, then:

* \(w\in A_0\);
* \(d_w(y_w)=0\);
* global minimality and \(D(y_w)\le D_0\) give \(D(y_w)=D_0\);
* no source-inactive coordinate is activated.

Therefore the support is contained strictly in \(A_0\setminus\{w\}\).

Unlike the \(g,\kappa,q\) tests, (17) is an exact statement about one literal endpoint. It neither recombines incompatible cap witnesses nor substitutes an unreachable coalition.

---

# 3. What happens to the five advertised failures

## 3.1 \(U_w(x_2)<\chi_w\)

This is **not an endpoint obstruction**. If the other four finite conditions hold, (14) still gives strict support descent, which qualifies as Outcome 4 even though the original five-field `SpareCancel` predicate fails.

If one needs a floor-admissible interpolation rather than merely the endpoint, then the inequality does matter. It implies

$$
0<\chi_w-U_w(x_2)\le B_w(x_2)-U_w(x_2)=d_w^2,
$$

so \(w\) has a positive unrestricted stopping-time deviation. That supplies a paid first-disagreement row, but not by itself an exact positive-charge return.

## 3.2 \(g_w^w(x_2)<d_w^2\)

This only says that a **lower bound** on \(G_w^w\) is too small.

There are two exact subcases:

$$
G_w^w=d_w^2.
$$

Then \(d_w(y_w)=0\), and support descent may still occur despite failure of the \(g\)-test.

Or

$$
G_w^w<d_w^2.
$$

Then

$$
d_w(y_w)=d_w^2-G_w^w>0.
\tag{18}
$$

Since \(w\) plays Never in \(y_w\), some finite stopping-time deviation beats Never. This gives an especially well-oriented paid row: source witness Never, receiving witness finite.

The checked first-disagreement decoder turns a positive difference between two pure stopping times—including Never—into a literal live-mass-weighted paid row.  Its temporal orientation can produce further legal endpoint deviations, but that module explicitly does not re-enter the resulting row into a reset chronology.

## 3.3 \(\sum_{i\ne w}q_i^w>D_0\)

Once \(w\)'s debt has been closed,

$$
D_0
\le D(y_w)
\le \sum_{i\ne w}q_i^w.
\tag{19}
$$

The strict inequality on the right does not distinguish between:

* actual excess \(D(y_w)>D_0\); and
* slack in the separate \(g_i^w\) and \(\kappa_i^w\) bounds while \(D(y_w)=D_0\).

The maxima defining the various \(\kappa_i^w\) may occur at different coalitions and under different deviating stopping laws. The minima defining the \(m_i^w\) may concern coalitions never reached after the unique-\(w\) event. Therefore

$$
\sum_i q_i^w-D_0
$$

is not a common-profile charge, a Bellman absorption mass, or an executable complementary-pair certificate.

The correct split is to evaluate the actual \(D(y_w)\):

* if \(D(y_w)=D_0\) and no inactive coordinate enters, use Outcome 4;
* if \(D(y_w)>D_0\), one has an actual off-minimum paid endpoint, but no established well-founded descent back to the minimum fiber.

## 3.4 \(\exists j\notin A_0,\ q_j^w>0\)

Again, \(q_j^w\) is only an upper bound.

If

$$
d_j(y_w)=0,
$$

the positive \(q_j^w\) is harmless slack.

If

$$
d_j(y_w)>0,
\tag{20}
$$

then there is an actual zero-to-positive debt-support entry. This is a semantic object, but its conversion into an executable chronology is itself a live frontier edge. The support-rank machinery isolates precisely such entries; it does not supply the missing source-matched path consumer. The repository’s paid-near-return capstone likewise treats support entry as a separately assumed chronological consumer.

## 3.5 \(w\notin A_0\)

The finite omission theorem cannot replace \(w\) by another spare automatically. If \(a,b,c,\ell\) are distinct, \(W\) is a singleton. The omitted-label theorem is only finite role counting; it supplies no debt sign, floor, cap, or reward comparison for that label.

An inactive \(w\) does not prevent \(y_w\) from dropping some other active coordinate, so the exact endpoint must still be inspected. But if \(y_w\) remains on the same minimum fiber with the same positive support, omission alone gives no rank decrease.

This is especially unavoidable in the one-active regime: if \(a\) is the unique source debtor, then every omitted \(w\ne a\) is source-inactive.

---

# 4. Why the one-active files do not consume the residual

`OneActiveAlignedRankCollapse.lean` proves a strong but differently quantified statement:

* one positive minimum semantic pair;
* one exact Nash root against its prescribed payoff;
* a positive singleton clock at that root;
* a positive debt owner at that same pair.

Under those simultaneous hypotheses, the debt owner equals the clock owner, and the exceptional \(3+2\) role pattern collapses. The file explicitly states that it does **not** prove the required alignment; putting the atom and transfer edge on the same minimum pair and exact root is the remaining task.

Its same-profile quantitative replacement is also insufficient here. For a singleton atom at an actual stage, distinct clock/debt owners are charged by

$$
\text{live mass}\times\text{tail excess}
+
D(\operatorname{Sem}(\text{whole profile})).
\tag{21}
$$

At \(x_2\), the second term is at least \(D_0>0\); it is not an error tending to zero.

The literal two-reset theorem supplies:

* actual \(x_0,x_1,x_2\);
* transfer inequalities;
* retention of actual terminal atoms.

It does not supply an exact Nash root at the retained atom, nor identify the retained stage with the minimum semantic pair. Consequently the one-active collapse cannot be applied merely because the five labels fit its graph.

`OneActiveTransferDefectGraph.lean` is correspondingly a finite graph classification. It does not construct the required profile, root, or Bellman chronology.

---

# 5. The strongest surviving exhaustive producer

There is a clean two-arm theorem.

## Theorem: literal Never drop or a same-source paid summable port

For every \(w\in W\), either

$$
\operatorname{Sem}(y_w)
$$

is an actual global minimizer with strict positive-debt-support drop, or there exist an observer \(i\) and a fixed \(\gamma>0\) such that the literal profile \(y_w\) carries a

$$
\operatorname{QuittingPaidFirstDisagreementRow}(r,y_w,i,\gamma),
$$

and therefore a

$$
\operatorname{QuittingPaidCapLiftedSource.SummablePort}
$$

whose positive minimum is \(z_0\).

Moreover, if the terminal witness has gap \(\eta\), one may take any fixed

$$
0<\gamma<\eta,
$$

for example \(\gamma=\eta/2\).

### Proof

If \(y_w\) gives support descent, take the first arm.

Otherwise \(D(y_w)\ge D_0>0\), so some player has positive terminal semantic debt. More directly, the terminal witness supplies a player and a behavioral deviation improving its payoff by at least \(\eta\).

For fixed opponents, a quitting-game behavioral strategy is a probability law on

$$
\mathbb N\cup\{\infty\}.
$$

Payoff is affine in that law. Decomposing both the profitable deviation and the prescribed strategy into pure stopping times shows that two pure times have payoff difference greater than \(\eta/2\). The paid first-disagreement decoder constructs the literal row.

Use:

* minimum \(z_0\);
* its global lower-bound proof;
* \(D_0>0\);
* literal profile \(y_w\);
* the selected observer;
* gain \(\eta/2\);
* the paid row.

These fields form a `QuittingPaidCapLiftedSource`. Its cap-lift construction prefixes exact cap-Nash roots, keeps all cap coordinates above their behavioral punishment floors, preserves the paid suffix with a positive reach ratio, and proves that total absorption is summable.

So all five failed-test cases can be collapsed to one actual semantic residual:

$$
\boxed{
\text{literal, uniformly paid, exact punishment-floor,
summable all-Continue port}.
}
\tag{22}
$$

This is substantially smaller than the five finite failures. It is not, however, one of Outcomes 1–4.

The obstruction is exact: the limiting port is a terminal-semantic carrier point, not a behavioral profile that reaches the original paid suffix after infinitely many exact prefixes. Summable absorption and convergence do not imply a positive-charge payoff return. For example, abstractly,

$$
q_t=2^{-t},
\qquad
v_{t+1}-v_t=q_t e
$$

has summable charge and convergent values, while the normalized motion remains the nonzero vector \(e\). Thus the newly added normalized-motion producer does not apply without an additional theorem producing arbitrarily small normalized motion.

The paid-row near-return file is explicit about the missing direction: it supplies consumers for a positive exact payoff return or payoff closure, but does not construct either from a paid row.

---

# 6. Consequences for the requested theorem

Under the terminal exploitability witness:

* Outcome 3 is impossible. A terminal \(\varepsilon\)-Nash profile satisfies

  $$
  d_i\le\varepsilon
  $$

  for all five players and hence

  $$
  D\le5\varepsilon.
  $$

  Taking \(\varepsilon<D_0/5\) contradicts global minimality. The checked debt-sum bound appears in the one-active module.

* Outcome 2 is impossible because a positive cumulative admissible payoff near-return family compiles to a uniform-equilibrium payoff. The toolkit distinguishes this checked consumer from the still-missing producer.

Therefore a complete producer theorem would have to turn the summable-port residual (22) into an actual rank descent. The exact missing implication is of the form

$$
\boxed{
\begin{aligned}
&\text{literal FIN5 four-role packet}
+\text{literal paid cap-lifted summable port}\\
&\qquad\Longrightarrow
\text{minimum-fiber support drop}
\ \lor\
\text{positive exact payoff return}.
\end{aligned}
}
\tag{23}
$$

Neither `OneActiveAlignedRankCollapse` nor the two-reset retention theorem proves (23). The general four-role reduction module likewise leaves the game-facing consumption of every local dispatch as an explicit premise rather than a theorem.

A realizable negative answer would require an actual `QuittingTerminalExploitabilityWitness`, which the repository treats as equivalent to nonexistence of a uniform-equilibrium payoff. Local cap regressions or compatible debt vectors do not meet that requirement.

## Final status

The verified mathematical advancement is:

$$
\boxed{
\text{remove the floor hypothesis from endpoint deletion}
}
$$

and

$$
\boxed{
\text{collapse all genuine failed deletions to one
same-source paid summable-port residual}.
}
$$

The unconditional FIN5 four-role discharge remains unproved and unrefuted. Claiming Outcomes 1–4 exhaustively would require precisely the paid-port restart or support-entry chronology theorem that is still absent.

This audit used current `main` at commit
`e274d8c8d1bb9635aef2fba0e21b6b13b9919db8`.  No new Lean declaration was compiled or published; the project runbook requires keeping a mathematical source audit distinct from a checked Lean result. 


## Verdict

The literal-Never deletion argument is sound, and it admits a useful strengthening:

* the punishment-floor hypothesis is unnecessary for the **endpoint** rank descent;
* the omitted player need not itself belong to the original positive-debt support;
* \(g_w^w(x_2)\ge d_w(x_2)\) need not hold if the residual debt of \(w\) can be absorbed in a smaller finite cover;
* an inactive coordinate may acquire a positive upper bound \(q_j^w\), provided the total possible target cover is still smaller.

What does **not** follow from the available declarations is the requested unconditional producer theorem. The precise obstruction is not the five listed certificate failures individually: \(g\) is only a payoff-gain lower bound and \(\kappa\) only a cap-lift upper bound, so their failures need not correspond to any actual semantic failure. After replacing those tests by exact endpoint data, the unresolved arms are:

1. a literal Never endpoint strictly above the global minimum, followed only by a real-valued cap-port debt descent which has no checked well-founded re-entry; or
2. a literal minimum-fiber endpoint with no support-rank drop whose paid cap lift is the lossless all-Continue inert stall.

I did not obtain a realizable counterexample satisfying the terminal-exploitability hypothesis. Such an example would itself be a five-player quitting game without a uniform-equilibrium payoff, not merely a counterexample to an auxiliary estimate.

The uploaded submission’s assessment—valid conditional branch, no exhaustive producer—is therefore correct, but its hypotheses can be weakened substantially. 

# 1. Independent verification of the literal-Never lemma

Put

$$
z_k=\operatorname{Sem}(x_k),\qquad d_i^k=d_i(z_k),
\qquad
y=y_w=x_2[w\leftarrow\mathrm{Never}].
$$

It is useful to separate prescribed-payoff change from cap change:

$$
\Delta_i^w:=U_i(y)-U_i(x_2),
\qquad
\alpha_i^w:=B_i(y)-B_i(x_2).
\tag{1}
$$

Then, identically,

$$
d_i(\operatorname{Sem}(y))
   =d_i^2+\alpha_i^w-\Delta_i^w.
\tag{2}
$$

## 1.1 Prescribed-payoff comparison

Represent every behavioral strategy by its complete stopping time

$$
Q_i\in\mathbb N\cup\{\infty\}.
$$

Couple \(x_2\) and \(y\) by retaining all \(Q_i\), \(i\ne w\), and replacing \(Q_w\) by \(\infty\).

There are only four cases.

* An opponent stops strictly before \(w\): the outcome is unchanged.
* \(w\) ties a nonempty first coalition \(T\): the outcome changes from
  \(T\cup\{w\}\) to \(T\).
* \(w\) is uniquely first: after deleting \(w\), the eventual opponent coalition is some
  \(T\subseteq I\setminus\{w\}\), including \(T=\varnothing\) if nobody ever stops.
* Everyone chooses Never: the outcome remains the nonabsorbing outcome.

Hence

$$
\Delta_i^w\ge g_i^w(x_2)
\tag{3}
$$

for every \(i\).

This is a genuine whole-stopping-law comparison. It includes finite stopping, Never, arbitrarily late stopping, and random stopping times.

## 1.2 Unrestricted cap comparison

Fix \(i\ne w\) and an arbitrary behavioral deviation \(\tau_i\). Couple

$$
y[i\leftarrow\tau_i]
\quad\text{and}\quad
x_2[i\leftarrow\tau_i]
$$

in the same way. Pathwise, the payoff increase caused by removing \(w\) is at most
\(\kappa_i^w\). Therefore

$$
U_i\bigl(y[i\leftarrow\tau_i]\bigr)
\le
U_i\bigl(x_2[i\leftarrow\tau_i]\bigr)+\kappa_i^w .
$$

Taking the supremum over **all** behavioral deviations gives

$$
\alpha_i^w\le \kappa_i^w
\qquad(i\ne w).
\tag{4}
$$

For \(w\), the opponents have not changed, so its entire deviation problem is unchanged:

$$
\alpha_w^w=0,
\qquad
B_w(y)=B_w(x_2).
\tag{5}
$$

Thus

$$
d_w(y)=d_w^2-\Delta_w^w.
\tag{6}
$$

Since debt is nonnegative,

$$
\Delta_w^w\le d_w^2.
\tag{7}
$$

If

$$
g_w^w(x_2)\ge d_w^2,
$$

then (3) and (7) force

$$
\Delta_w^w=d_w^2,
\qquad
d_w(y)=0.
\tag{8}
$$

For \(i\ne w\), (2)–(4) give

$$
d_i(y)
\le d_i^2+\kappa_i^w-g_i^w(x_2)
\le q_i^w.
\tag{9}
$$

Consequently,

$$
D(\operatorname{Sem}(y))
\le\sum_{i\ne w}q_i^w.
\tag{10}
$$

Under the stated aggregate hypothesis,

$$
D(\operatorname{Sem}(y))\le D_0.
$$

Since \(y\) is an actual profile for the same reward table and \(z_0\) is globally minimizing,

$$
D_0\le D(\operatorname{Sem}(y)).
$$

Therefore

$$
D(\operatorname{Sem}(y))=D_0.
\tag{11}
$$

If \(j\notin A_0:=\operatorname{supp}^{+}d(z_0)\), then \(q_j^w=0\) and (9) imply
\(d_j(y)=0\). Together with (8),

$$
\operatorname{supp}^{+}d(\operatorname{Sem}(y))
\subseteq A_0\setminus\{w\}.
\tag{12}
$$

If \(w\in A_0\), the support cardinality decreases strictly.

This verifies the original conditional lemma.

# 2. The floor hypothesis is not part of the endpoint proof

The inequality

$$
U_w(x_2)\ge\chi_w
\tag{13}
$$

was not used in (1)–(12).

Indeed, when \(w\)'s debt closes,

$$
U_w(y)=B_w(x_2)\ge\chi_w
\tag{14}
$$

by the definition of the punishment value. Thus the **final** Never endpoint is automatically floor-safe.

The extra hypothesis (13) is needed only if one wants the entire homotopy

$$
x_2^\theta
=
x_2\!\left[
w\leftarrow
(1-\theta)(x_2)_w+\theta\,\mathrm{Never}
\right],
\qquad 0\le\theta\le1,
\tag{15}
$$

to remain floor-safe. Whole-stopping-law affinity gives

$$
U_w(x_2^\theta)
  =(1-\theta)U_w(x_2)+\theta U_w(y),
$$

while the opponents, and hence \(B_w\), remain fixed. Under debt closure,

$$
d_w(x_2^\theta)=(1-\theta)d_w^2.
\tag{16}
$$

For \(i\ne w\), payoff affinity and cap convexity give

$$
d_i(x_2^\theta)
\le
(1-\theta)d_i^2+\theta d_i(y).
\tag{17}
$$

Thus every intermediate cap estimate also covers unrestricted behavioral deviations.

The first two reset profiles are unaffected: the cancellation is appended after \(x_2\). Therefore the literal reset identities

$$
x_0\longrightarrow x_1\longrightarrow x_2
$$

and the quarter-retention inequalities are unchanged. This is stronger than a perturbative preservation argument.

# 3. Stronger finite-cover Never theorem

Define

$$
\widehat q_i^w :=
\begin{cases}
\max\{0,d_w^2-g_w^w(x_2)\},&i=w,\\[1mm]
\max\{0,d_i^2+\kappa_i^w-g_i^w(x_2)\},&i\ne w,
\end{cases}
\tag{18}
$$

and the finite prospective cover

$$
C_w:=\{i:\widehat q_i^w>0\}.
\tag{19}
$$

The previous coupling proves, without any additional hypothesis,

$$
d_i(\operatorname{Sem}(y_w))\le \widehat q_i^w
\qquad(i\in I).
\tag{20}
$$

Indeed, for \(i=w\), use (3), (6), and nonnegativity; for \(i\ne w\), use (9).

## Finite-cover literal-Never descent theorem

If, for some \(w\in W\),

$$
\sum_i\widehat q_i^w\le D_0
\tag{21}
$$

and

$$
|C_w|<|A_0|,
\tag{22}
$$

then

$$
D(\operatorname{Sem}(y_w))=D_0
\tag{23}
$$

and

$$
\left|
\operatorname{supp}^{+}d(\operatorname{Sem}(y_w))
\right|
<
|A_0|.
\tag{24}
$$

### Proof

By (20),

$$
D(\operatorname{Sem}(y_w))
\le\sum_i\widehat q_i^w\le D_0.
$$

Global minimality gives the reverse inequality, proving (23). Also (20) gives

$$
\operatorname{supp}^{+}d(\operatorname{Sem}(y_w))
\subseteq C_w.
$$

Taking cardinalities and using (22) proves (24). ∎

This theorem is strictly stronger than the five original tests. Those tests imply

$$
\widehat q_w^w=0,
\qquad
C_w\subseteq A_0\setminus\{w\},
$$

and hence imply (21)–(22), but the converse fails.

In particular:

* \(w\) need not lie in \(A_0\);
* \(w\)'s debt need not be completely closed;
* a previously inactive coordinate may receive some debt;
* the target support need not be a subset of \(A_0\);
* only total cover size and aggregate debt matter.

This is an ordinary-mathematics theorem; it has not been added to Lean.

# 4. Why the five individual failures are not semantic branches

The main logical problem with the requested producer is that the five tests are one-sided certificates. Their negations do not describe actual endpoint behavior.

| Failed test                       | What the failure really says                                                                                                                          |
| --------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------- |
| \(w\notin A_0\)                   | Only that deleting \(w\) cannot lower support by removing \(w\) itself. It may still cancel another debtor.                                           |
| \(U_w(x_2)<\chi_w\)               | Only that the beginning of the deletion homotopy is below the floor. It says nothing adverse about the final endpoint when Never closes \(w\)'s debt. |
| \(g_w^w(x_2)<d_w^2\)              | Only that a terminal-law lower bound is too weak. The actual gain \(\Delta_w^w\) may still equal \(d_w^2\).                                           |
| \(\sum_{i\ne w}q_i^w>D_0\)        | Only that the sum of separate worst-case cap bounds is too large. Actual cap maximizers need not realize those worst cases simultaneously.            |
| \(q_j^w>0\) for an inactive \(j\) | Only that the coarse upper bound does not prove \(d_j(y_w)=0\). It does not imply that \(j\) actually acquires positive debt.                         |

For example,

$$
g_w^w(x_2)<d_w^2
$$

is compatible with

$$
\Delta_w^w=d_w^2
$$

because \(g_w^w\) replaces the actual post-\(\{w\}\) continuation payoff by the minimum over all possible later coalitions. Likewise,

$$
q_j^w>0
$$

is compatible with \(d_j(y_w)=0\), because \(\kappa_j^w\) is a maximum over all coalition comparisons, whereas the actual cap may use none of the maximizing coalitions.

Therefore a theorem cannot validly send the **failure of one of these bounds** directly to a paid path, an exact return, or a rank decrease. One first has to replace the bound failure by an exact semantic event such as

$$
d_w(y_w)>0,\qquad
D(\operatorname{Sem}(y_w))>D_0,
\qquad\text{or}\qquad
d_j(y_w)>0.
\tag{25}
$$

# 5. What the two one-active modules actually provide

The checked four-role reset theorem supplies literal \(x_1,x_2\), positive transfer recipients, nonnegative first excess, and quarter-retention of every original stage atom. Its own scope expressly stops before a cardinal reduction: the omitted player may still affect the payoff and cap table.  The underlying two-reset theorem similarly uses the first target only as an excess-near-minimum source for the second reset; it does not assert that \(x_1\) or \(x_2\) is another global minimizer.

`OneActiveTransferDefectGraph.lean` proves the finite alternative

$$
\text{four-role window}
\quad\lor\quad
\text{period-three transfer cycle disjoint from a fixed two-edge defect}.
$$

It explicitly remains a structural reduction: it does not construct a compatible game chronology carrying the same defect atom, and it does not consume an omitted player.

`OneActiveAlignedRankCollapse.lean` proves something more precise but under stronger alignment:

* one literal minimum semantic pair;
* one exact Nash root at that pair;
* one positive singleton clock;
* one positive transfer-owner debt at the same pair.

Under those hypotheses the clock owner and every positive debt owner coincide, so the five displayed roles collapse to four. The file explicitly does not prove the required alignment. Its same-profile quantitative alternative charges owner mismatch by

$$
\text{tail excess}+\text{initial total debt},
$$

and the latter equals \(D_0>0\) in the counterexample regime, so it is not itself a contradiction.

There is also an important incompatibility with the original Never condition. In the exactly aligned one-active case, if a singleton clock is positive then every positive debt coordinate has that same owner. Since total debt is positive,

$$
A_0=\{\text{clock owner}\}.
\tag{26}
$$

An omitted fifth player \(w\) is then normally **outside** \(A_0\). Thus

$$
w\notin A_0
$$

is not an exceptional failure that the aligned theorem eliminates; it is the canonical aligned configuration.

Moreover, when \(|A_0|=1\) and \(D_0>0\), no minimum-fiber positive-support descent is possible at all: every pair with total debt \(D_0>0\) has nonempty positive support. In that stratum, a successful producer must yield a uniform-payoff/return contradiction or a different maintained rank—not deletion of \(w\) from \(A_0\).

# 6. The exact semantic residual after trying every omitted player

Using exact endpoint data rather than \(g,\kappa,q\), failure of all literal-Never support descents is precisely

$$
\forall w\in W,\qquad
D(\operatorname{Sem}(y_w))>D_0
\quad\lor\quad
\left[
D(\operatorname{Sem}(y_w))=D_0
\ \land\
\bigl|\operatorname{supp}^{+}d(\operatorname{Sem}(y_w))\bigr|
\ge |A_0|
\right].
\tag{27}
$$

This is strictly smaller than the five-test failure list:

* it removes every false obstruction caused by slack in \(g\) or \(\kappa\);
* it removes the punishment-floor test from endpoint descent;
* it allows cancellation of a player other than \(w\);
* it measures the actual unrestricted caps at the literal endpoint.

Call (27) the **exact Fin5 four-role spare residual**.

No theorem in either one-active module consumes (27). The reason is exact: neither disjunct produces the same-pair exact Nash root, singleton clock, and transfer owner required by the aligned rank-collapse theorem.

# 7. What a terminal exploitability gap adds

Suppose the terminal witness has gap \(\gamma>0\). At every actual profile \(p\), some player \(i\) has

$$
d_i(\operatorname{Sem}(p))\ge\gamma.
\tag{28}
$$

For that player, let \(V_i(t)\) be the terminal payoff obtained by the pure stopping time

$$
t\in\mathbb N\cup\{\infty\}.
$$

The prescribed behavioral strategy induces a probability law \(\nu_i\) on these pure stopping times, and

$$
U_i(p)=\mathbb E_{\nu_i}[V_i(t)].
\tag{29}
$$

Meanwhile,

$$
B_i(p)=\sup_t V_i(t).
\tag{30}
$$

Choose \(t^+\) with

$$
V_i(t^+)\ge B_i(p)-\gamma/4.
$$

Because (29) is an expectation, some \(t^-\) satisfies

$$
V_i(t^-)\le U_i(p).
$$

Hence

$$
V_i(t^+)-V_i(t^-)\ge 3\gamma/4.
\tag{31}
$$

The checked pure-time decoder turns such a difference into a literal first-disagreement row retaining finite times, Never, reached survival mass, and the exact Quit-versus-wait comparison.   Thus every residual endpoint \(y_w\) supplies an attained paid row with any fixed gain below \(3\gamma/4\), for example \(\gamma/2\).

This still does not produce an admissible payoff near-return. A paid first disagreement is a payoff difference between two deviations at one literal profile; it is not automatically an exact punishment-floor Nash–Bellman edge.

# 8. The latest paid-cap trichotomy and the remaining two arms

At current `main`, the source declaration `QuittingPaidCapLiftedSource.exactTrichotomy` divides an attained paid cap-lift into:

1. positive cumulative absorption and zero cap displacement, yielding a `QuittingPositiveCumulativeAdmissiblePayoffNearReturnFamily`;
2. positive cap displacement, yielding a quantitative total-debt decrease

   $$
   D_*\,\frac{\rho}{2M};
   $$
3. zero total absorption, in which every selected cap root is literally all Continue, every finite prefix has the same whole semantic pair, and the paid row shifts without loss.

The project status correctly records two limitations:

* the quantitative descent has no regenerated source or well-founded recursive consumer;
* the zero-absorption inert branch remains open.

These limitations matter here.

### Minimum-fiber endpoint

If

$$
D(\operatorname{Sem}(y_w))=D_0,
$$

then the positive-displacement branch would give a semantic carrier point with debt below \(D_0\), contradicting global minimality. The charged-return branch contradicts the terminal witness. Therefore the paid cap lift of a hard same-fiber endpoint must be the inert all-Continue branch.

So the exact unresolved same-fiber case is

$$
\boxed{
D(\operatorname{Sem}(y_w))=D_0,\quad
|\operatorname{supp}^{+}d(\operatorname{Sem}(y_w))|\ge|A_0|,
\quad
\text{lossless all-Continue paid stall}.
}
\tag{32}
$$

### Off-minimum endpoint

If

$$
D(\operatorname{Sem}(y_w))>D_0,
$$

positive cap displacement may lower its debt without crossing below \(D_0\). This is a real decrease, but it is not the requested Outcome 4:

* total debt is real-valued and can descend infinitely;
* the new port need not be an actual minimum-fiber source;
* there is no checked re-extraction which recreates a smaller four-role packet;
* the cap displacement can tend to zero;
* the alternative can instead become the inert stall.

Thus the exact unresolved off-minimum case is

$$
\boxed{
D(\operatorname{Sem}(y_w))>D_0,
\quad
\text{followed by either a non-regenerated cap descent or an inert stall}.
}
\tag{33}
$$

The paid-row near-return consumer itself explicitly does not construct a near-return from a paid row; it only consumes one after an exact floor-admissible producer has supplied it.

# 9. Outcomes 2 and 3 really are contradiction branches

If \(p_\varepsilon\) is terminal \(\varepsilon\)-Nash, then each debt coordinate is at most \(\varepsilon\), so on five players

$$
D(\operatorname{Sem}(p_\varepsilon))\le5\varepsilon.
$$

Global minimality gives

$$
D_0\le5\varepsilon.
$$

Taking

$$
0<\varepsilon<D_0/5
$$

is impossible. This estimate is recorded in `OneActiveAlignedRankCollapse.lean`.

Likewise, a positive cumulative admissible payoff near-return family has the checked uniform-payoff consumer, contradicting the terminal exploitability witness.

Hence the requested producer would indeed amount to unconditional rank descent or contradiction throughout the non-excess four-role arm.

# 10. Strongest surviving exhaustive statement

The strongest statement justified by the actual source data is:

$$
\boxed{
\begin{aligned}
&\exists w\in W:
   \sum_i\widehat q_i^w\le D_0
   \ \land\
   |\{i:\widehat q_i^w>0\}|<|A_0|
\\
&\qquad\Longrightarrow
\text{literal same-table minimum-fiber support descent};
\end{aligned}}
\tag{34}
$$

otherwise, after replacing the one-sided tests by exact endpoint semantics and using the terminal gap to extract a paid row, every \(w\in W\) lies in one of:

$$
\boxed{
\begin{array}{ll}
\textbf{S:}&
D(y_w)=D_0,\ 
|\operatorname{supp}^{+}d(y_w)|\ge|A_0|,\ 
\text{lossless all-Continue paid stall};\\[1mm]
\textbf{O:}&
D(y_w)>D_0,\ 
\text{non-regenerated quantitative cap descent or inert stall}.
\end{array}}
\tag{35}
$$

This is substantially smaller than the five original failure cases, but neither \(\mathbf S\) nor \(\mathbf O\) presently has the named checked consumer required by the question.

A draft `SparePlayerCancellation.lean` branch contains a useful exact-cap/all-behavior conditional trichotomy—terminal Nash, strict debt decrease, or finite cover-rank drop—but it assumes the source cover, spare-floor, coordinate collision repayment, and aggregate balance. It does not derive those facts from the four-role output.

## Formal status

I refreshed repository state as required by the supplied runbook.  Current `main` is
`a277602ce02e1e0b9094b40756aa22cc5e766c36`.  Its current CI run failed in the Python unit-test step, so trust scanning, Lean compilation, and `lake build` were skipped; accordingly I have treated the newly added paid-cap trichotomy as a source declaration with a mathematical proof body, not as current-head CI-validated evidence.

The definite conclusion is therefore:

$$
\boxed{
\text{The conditional Never deletion is valid and strengthens to (34), but
the exhaustive FIN5 producer is not established.}
}
$$

The exact missing implication is the consumption of the semantic residuals (32)–(33): either turn a lossless all-Continue paid stall into an exact admissible payoff return, or turn cap displacement into a regenerated, genuinely well-founded minimum-fiber rank decrease.
