# Finite cap children are sibling prefixes; stationarity gives only weak barrier monotonicity

Author: CODEX_SPINOZA

## Status

**Exact ordinary mathematics; barrier-ancestry lemma and strictness no-go,
not Lean-checked.** A unilateral deterministic finite-clock child and its
actual parent are universal-prefix siblings over one literal shifted tail.
If the parent is stationary, the shifted tail is the parent again, so the
cap child is a universal-prefix descendant and the greatest target-free
Bellman barrier \(Q\) cannot decrease across that one horizontal update.

This does not renew along the Fin4 reset construction: its later actual
sources are nonstationary, so the next cap child and its parent are merely
siblings. Even in the stationary case, a positive attained cap gain need not
give any strict increase in \(Q\). Thus the barrier ledger still lacks a
charge modulus.

## Question

The universal-hull no-go isolates the comparison

\[
 Q(\text{cap child})\stackrel{?}{\ge}Q(\text{actual parent}).
 \tag{1}
\]

Does literal pure-time ancestry prove (1) for the shifted finite cap used in
the renewed owner construction?

## 1. Full semantic common-tail factorization

Let \(\sigma\) be an actual behavioral profile in a finite quitting game.
Because the only live public history is all Continue, write its prescribed
root sequence as

\[
 x^0,x^1,x^2,\ldots\in[0,1]^I.
\]

Fix a player \(k\) and a finite date \(T\). Let \(\tau\) be obtained from
\(\sigma\) by replacing only player \(k\)'s stopping law by deterministic
Quit at date \(T\). Thus \(k\) Continues at dates \(0,\ldots,T-1\) and Quits
surely at date \(T\), while every opponent retains its literal strategy.

Let \(\theta^{T+1}\sigma\) be the actual shifted tail after \(T+1\) joint
Continue outcomes and put

\[
 z_{\mathrm{tail}}=\operatorname{Sem}(\theta^{T+1}\sigma).
\]

Define two root words of length \(T+1\):

- the parent word \(v=(x^0,\ldots,x^T)\);
- the cap-child word \(w=(y^0,\ldots,y^T)\), where
  \(y^t_{-k}=x^t_{-k}\) for every \(t\),
  \(y^t_k=0\) for \(t<T\), and \(y^T_k=1\).

### Proposition 1.1 (literal sibling-prefix identity)

For the complete terminal semantic pair, including every unrestricted
behavioral cap,

\[
 \boxed{
 \operatorname{Sem}(\sigma)=T_vz_{\mathrm{tail}},
 \qquad
 \operatorname{Sem}(\tau)=T_wz_{\mathrm{tail}}.}
 \tag{2}
\]

#### Proof

The first equality is the iterated terminal-semantic prefix identity applied
to the actual first \(T+1\) roots of \(\sigma\).

For the second equality, the prescribed root sequence of \(\tau\) through
date \(T\) is exactly \(w\). At date \(T\), prescribed play absorbs surely
because \(k\) Quits. If an outsider \(i\ne k\) deviates, player \(k\)'s sure
Quit remains, so the play still cannot reach the tail after date \(T\). If
player \(k\) deviates and every opponent Continues at date \(T\), the
continuation cap depends only on the opponents' literal strategies after
that date, which are exactly those of \(\theta^{T+1}\sigma\). The prescribed
post-\(T\) strategy of \(k\) is irrelevant to \(k\)'s own cap. Hence the
iterated prefix formula computes every prescribed-payoff and cap coordinate
of \(\tau\), proving the second equality. QED

No best-response or cap-attainment hypothesis is needed for (2). If the
finite clock \(T\) happens to attain \(k\)'s complete cap at \(\sigma\), then
(2) applies to the horizontal cap-child seam used in the shifted-clock arm.

## 2. Exact barrier consequences

Let

\[
 Q(z)=\inf_a d(T_az)
\]

be the greatest target-free Bellman barrier, where \(a\) ranges over finite
arbitrary product-root words. Bellman monotonicity and (2) give only

\[
 Q(z_{\mathrm{tail}})
 \le Q(\operatorname{Sem}(\sigma)),
 \qquad
 Q(z_{\mathrm{tail}})
 \le Q(\operatorname{Sem}(\tau)).
 \tag{3}
\]

These are two lower bounds from a common ancestor. They do not compare the
two sibling values in (1).

### Corollary 2.1 (stationary finite-cap monotonicity)

If \(\sigma\) is stationary, then

\[
 \operatorname{Sem}(\theta^{T+1}\sigma)
 =\operatorname{Sem}(\sigma).
\]

Consequently (2) makes \(\operatorname{Sem}(\tau)\) a finite universal-prefix
descendant of \(\operatorname{Sem}(\sigma)\), and

\[
 \boxed{
 Q(\operatorname{Sem}(\sigma))
 \le Q(\operatorname{Sem}(\tau)).}
 \tag{4}
\]

This applies to a deterministic finite cap installed at an actual stationary
source. It does not require the source to minimize debt.

For a nonstationary source, stationarity is exactly the missing ancestry
equality. The reset children in the renewable cap-clock theorem are explicitly
nonstationary: they retain an older counterfactual tail behind a finite
prefix. Proposition 1.1 types their cap child as another prefix of a shifted
tail, but does not identify that tail semantic point with the actual parent.
Thus (4) cannot simply be iterated through renewed phases.

## 3. Positive cap gain does not charge \(Q\)

Even under stationarity, (4) is only weak. Consider the Fin4 reward table
with

\[
 r_0(\{0\})=1
\]

and every other reward coordinate equal to zero. Let \(\sigma\) be all Never.
It is stationary, player \(0\)'s unrestricted cap is attained by Quit0, and
the cap gain is one. Let

\[
 \tau=\sigma[0\leftarrow\operatorname{Quit0}].
\]

The profile \(\tau\) is terminal Nash: player \(0\) receives one and cannot
improve, while every other payoff and cap is zero. Therefore

\[
 Q(\operatorname{Sem}(\tau))=0.
\]

Since \(\tau\) is a one-root prefix of \(\sigma\), it is an admissible word
in the definition of \(Q(\operatorname{Sem}(\sigma))\), so

\[
 Q(\operatorname{Sem}(\sigma))=0.
\]

Thus a stationary cap response of gain one can satisfy equality in (4):

\[
 Q(\operatorname{Sem}(\tau))
 -Q(\operatorname{Sem}(\sigma))=0.
 \tag{5}
\]

The example has global minimum zero. It is not a regression under the
hypothetical Fin4 positive-minimum branch. It proves the narrower universal
claim needed here: no strict increase depending only on cap gain can follow
from stationarity and cap attainment.

## 4. Consequence for the \(D_*>0\) renewal route

Under a positive global terminal gap, every carrier point has
\(Q\ge\eta>0\). This supplies a common floor, not an ordering between the
siblings in (3). The first deterministic cap child of an actually stationary
tropical source obeys (4), but after that update the literal child is not
stationary. The next renewed cap update therefore returns to (3).

Accordingly the barrier program still lacks one of:

1. an additional source identity making each shifted tail equal to its
   renewed parent;
2. a quitting-specific comparison between \(Q(T_vz)\) and \(Q(T_wz)\) for
   the two source-linked sibling words;
3. a strict positive-minimum barrier-charge theorem using more than cap gain;
   or
4. a terminal consumer after the single stationary monotone step.

The current ancestry data supply none of these. In particular, replacing
“stationary” by “has one finite sure opponent” is invalid: a sure opponent
screens many deviations but does not identify the semantic state of the
shifted tail.

## Sources inspected

- formalized/QUITTING_CONTROLLER_TESTER_VALUE_AND_BARRIER_DUALITY.md;
- notes/CODEX_SPINOZA__RENEWABLE_CAP_ORBIT_GLOBAL_BARRIER_NO_GO.md,
  frozen after review at SHA-256
  cd8d489e2390ebfde21e5d061226dcec3a3d1e9c266e6096b36547d8cce46d2b;
- notes/CODEX_HAHN__LATE_RESET_RENEWS_ESCAPING_CAP_CLOCK_SOURCE.md,
  especially its explicit warning that a cap child is not stationary;
- notes/CODEX_SPINOZA__UNIQUE_SURE_ACTUAL_CHILD_TO_LITERAL_SHIFTED_CAP_RAY.md;
- notes/CODEX_NEGATIVE_CERTIFICATE__FINITE_PREFIX_OWNER_CAP_BYPASS.md; and
- the iterated form of continuous_quittingTerminalSemanticPrefix and
  quittingTerminalSemanticPrefix_mem_carrier in
  UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean.

## Boundary and nonclaims

- The proof covers a deterministic finite clock. Never has no finite terminal
  cut and is not included.
- The full semantic identity includes unrestricted behavioral deviations; it
  is not only a prescribed-payoff identity.
- Sibling ancestry is not prefix comparability.
- Weak \(Q\)-monotonicity at one stationary source is not a charged
  Nash--Bellman edge and does not yield a uniform equilibrium.
- The zero-minimum example refutes only a strict gain-to-\(Q\) modulus. It
  does not refute a theorem using the full positive-minimum Fin4 packet.

## Next exact question

For the particular two sibling words produced at a renewed \(D_*>0\) reset,
does exact root Nash on the parent word and cap attainment on the child word
force

\[
 Q(T_wz_{\mathrm{tail}})
 \ge Q(T_vz_{\mathrm{tail}}),
\]

or can their \(Q\)-ordering reverse? Any proof must use the linked
root-Nash/cap structure; common-tail ancestry alone gives only (3).
