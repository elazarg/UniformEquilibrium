# An exact word forces the cap-band receiver past its unique-sure mark

Author: CODEX_SPINOZA

## Status

**Exact ordinary mathematics; source-attached temporal strengthening, not
Lean-checked and not yet a Nash--Bellman return.** For the unique-sure
persistent word, exact Nash--Bellman ancestry rules out every profitable
pure stopping clock inside the exact word. Since the host's complete cap is
a fixed amount above its prescribed payoff, every sufficiently near-cap
receiver is therefore at the original tail boundary, later, or Never.

Redirecting the cap-band bad mass to such a late receiver preserves a fixed
amount of actual joint reach through the unique-sure inner row and into the
original tail. In fact, every source clock inside the exact word is outside
the cap band, so the target owner Continues surely through the whole word and
the target's joint tail reach is exactly the source's owner-deleted reach.
Thus the early-receiver branch in the generic cap-band split does not occur
here. The resulting paid target still changes the host's actions inside the
word and is not asserted to retain the word's exact-root property.

## 1. Exact finite-word stopping screen

Let a finite literal root word of length \(m\) be placed over an arbitrary
actual behavioral tail \(X\):

\[
 \Sigma=W\triangleright X.
\tag{1}
\]

For \(0\le t<m\), let \(q_t\) be the prescribed product root at date \(t\)
and \(u_t\) the prescribed payoff of the actual suffix beginning at that
date. Assume

\[
 u_t=F(q_t,u_{t+1})
\tag{2}
\]

and \(q_t\) is an exact product Nash equilibrium of the one-stage quitting
game with continuation payoff \(u_{t+1}\).

### Lemma 1.1: no profitable stopping clock inside the word

For every player \(i\) and every finite \(r<m\),

\[
 U_i\bigl(\Sigma[i\leftarrow Q_r]\bigr)\le U_i(\Sigma).
\tag{3}
\]

Here \(Q_r\) means Continue surely before the absolute date \(r\) and Quit
surely at \(r\).

### Proof

At date \(r\), the pure Quit endpoint payoff is at most \(u_{r,i}\), because
the prescribed mixed action \(q_{r,i}\) is a best response at the exact
one-stage Nash root and its expected payoff is \(u_{r,i}\). Work backwards.
If the continuation value of the deviating plan from date \(t+1\) is at most
\(u_{t+1,i}\), then choosing pure Continue at date \(t\) and following that
plan has value at most the pure Continue endpoint evaluated at
\(u_{t+1,i}\). Exact Nash optimality bounds that endpoint by \(u_{t,i}\).
Induction to date zero proves (3). This is the finite-word instance of
`quittingRootSequencePureTimeTerminalValue_le_of_bellmanSupersolution`. QED

## 2. Unique-sure persistent input

Use the actual profiles and notation from
`CODEX_SPINOZA__UNIQUE_SURE_PERSISTENT_WORD_HOST_PAYER_CAP_BAND`:

\[
 \Sigma_n=W_n\triangleright X_n,
 \qquad m_n=|W_n|.
\tag{4}
\]

The innermost roots satisfy \(q_{n,0}\to q\), where \(q_k=1\) and
\(q_i<1\) for \(i\ne k\). There are constants \(\eta>0\) and, eventually,

\[
 \beta_{n,k}:=\Pr_{\Sigma_n}(\text{opponents of }k
       \text{ survive through }m_n)\ge\eta,
 \qquad d_k(\Sigma_n)\ge D_*/2.
\tag{5}
\]

Let \(C_n\) be player \(k\)'s complete unrestricted behavioral cap at
\(\Sigma_n\), and let

\[
 f_n(a)=U_k\bigl(\Sigma_n[k\leftarrow Q_a]\bigr),
 \qquad a\in\mathbb N\cup\{\mathrm{Never}\}.
\tag{6}
\]

Behavioral pure-time extremality gives \(C_n=\sup_a f_n(a)\). Fix

\[
 e=D_*/4,
\tag{7}
\]

where all reward coordinates have absolute value at most \(R>0\).

Write \(\mu_n\) for player \(k\)'s complete source stopping law. Since its
word law contains the inner factor \(1-q_{n,0,k}\to0\),

\[
 \mu_n(\{m_n,m_n+1,\ldots,\mathrm{Never}\})
 =\Pr_{\Sigma_n}(T_k\ge m_n)\longrightarrow0.
\tag{8}
\]

## 3. Every near-cap receiver is late

### Theorem 3.1

For all sufficiently large \(n\), every receiver \(a_n\) satisfying

\[
 C_n-e/2<f_n(a_n)
\tag{9}
\]

lies in

\[
 \{m_n,m_n+1,\ldots\}\cup\{\mathrm{Never}\}.
\tag{10}
\]

### Proof

If \(a_n=r<m_n\), Lemma 1.1 gives
\(f_n(r)\le U_k(\Sigma_n)=C_n-d_k(\Sigma_n)\). On the other hand, (5),
(7), and (9) give

\[
 f_n(r)>C_n-e/2
 \ge U_k(\Sigma_n)+D_*/2-D_*/8
 =U_k(\Sigma_n)+3D_*/8,
\tag{11}
\]

a contradiction. QED

Near-cap receivers exist even when the cap is not attained: apply the
defining supremum property to the positive tolerance \(e/2\). The theorem
includes Never on the late side.

## 4. A paid target with positive actual tail reach

### Theorem 4.1

For all sufficiently large \(n\), choose any receiver satisfying (9) and
apply the cap-band pushforward of width \(e\) to the source law \(\mu_n\).
Let \(\widehat\Sigma_n\) be the resulting actual unilateral target. Then

\[
 U_k(\widehat\Sigma_n)-U_k(\Sigma_n)\ge D_*/4,
 \qquad d_k(\widehat\Sigma_n)\le D_*/4.
\tag{12}
\]

Moreover, after a finite shift,

\[
 \Pr_{\widehat\Sigma_n}(\text{jointly survive through }m_n)
 =\beta_{n,k}\ge\eta>0,
 \qquad
 \Pr_{\widehat\Sigma_n}(T_k\ge m_n)=1.
\tag{13}
\]

The cap-band cut \(c_n\) can be chosen with \(c_n<m_n\), and every
prescribed live root at a date strictly before \(c_n\) is unchanged.

### Proof

The checked cap-band debt and gain bounds give (12). Lemma 1.1 gives the
stronger pointwise statement that, for every finite \(r<m_n\),

\[
 C_n-f_n(r)\ge C_n-U_k(\Sigma_n)
 =d_k(\Sigma_n)\ge D_*/2>e.
\tag{14}
\]

Thus every source clock strictly before \(m_n\) is outside the width-\(e\)
band. The receiver is late by Theorem 3.1, so the pushforward sends all such
clocks to a clock at or after \(m_n\). Clocks already at or after \(m_n\)
either stay there or are sent to the same late receiver. Hence the target
owner has no stopping mass before \(m_n\), proving its sure survival in
(13). The opponents are unchanged, so independence makes target joint
survival through the word exactly their source survival \(\beta_{n,k}\).

By (8), the source mass before \(m_n\) tends to one. The standard
least-bad-clock construction therefore has positive early bad mass. Its
first positive bad clock is strictly before \(m_n\), while its receiver is
at or after \(m_n\). Hence the selected cut is that first bad clock and is
strictly before \(m_n\). The checked cap-band prefix identity gives the last
assertion. QED

## 5. Exact advance and remaining seam

The generic receiver-location alternative has collapsed to its useful side:
an exact Nash--Bellman word cannot contain a near-cap finite receiver before
its tail. The same actual cap-band target therefore combines:

- fixed gain \(D_*/4\);
- target owner debt at most \(D_*/4\);
- owner survival through the old word equal to one and joint tail reach at
  least \(\eta\);
- unchanged opponents and hence the original host-deleted clock; and
- literal source/root ancestry before a uniformly reached cut.

This does not make \(\widehat\Sigma_n\) an exact root word. At and after the
first bad clock, the host's hazard changes. The old roots were Nash against
the old successor payoffs, so (13) alone does not restore their exact
Nash--Bellman status. Nor does positive reach to date \(m_n\) identify the
conditional target suffix there with the old tail \(X_n\): it carries the
residual stopping law induced by the cap-band pushforward.

The remaining source-attached problem is consequently narrower than a
generic paid-port return: consume an actual fixed-gain sibling that reaches
the original tail boundary with fixed probability and differs from the
exact source only in the unique host's law after one pre-tail cut.

### Exact one-root regression: outsider Nash can fail

The strengthened reach does not preserve outsider root optimality. Take four
players \(k,j,a,b\), and make every reward coordinate zero except

\[
 r_k(\{k,j\})=1,
 \qquad r_j(\{j\})=1.
\tag{15}
\]

Let the tail have player \(j\) Quit surely and everyone else Continue. Put
over it one source root at which \(k\) Quits surely and all other players
Continue. This root is exact. Player \(k\)'s Quit payoff and prescribed
Continue payoff are both zero; player \(j\)'s Quit and Continue payoffs in
the presence of sure \(k\) are both zero; and both dummy comparisons are
zero.

The source pays \(k\) zero, while the late pure clock at the tail date makes
\(k\) join \(j\) and pays one. The cap-band replacement therefore forces
\(k\) to Continue through the one-row word and reaches the tail with
probability one. At the target, however, player \(j\)'s prescribed payoff is
zero from the tie \(\{k,j\}\), while Quitting at the old root produces
\(\{j\}\) and pays one. Thus the target's old root has outsider Nash defect
one.

The simultaneous \(\{k,j\}\) profile is a terminal equilibrium, so this
table has global minimum zero. It is not a counterexample under the hard
positive-minimum hypothesis. It does show that the new target fields alone
cannot revalidate the old roots; a further consumer must use the global
minimum/no-uniform-payoff structure.

## Sources inspected

- `notes/CODEX_SPINOZA__UNIQUE_SURE_PERSISTENT_WORD_HOST_PAYER_CAP_BAND.md`;
- `notes/CODEX_BLINDSPOT__FIXED_LEDGER_PAYER_PREMARK_CAP_BAND_WITNESS.md`;
- `UniformEquilibrium/Quitting/Bellman/Finite/BellmanCapPureTimeStop.lean`;
- `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/CapBandRedistribution.lean`;
- `MathUE/Probability/StoppingLawCapBandRedistribution.lean`; and
- `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`.

## Boundary and nonclaims

- The stopping screen uses the exact one-stage Nash inequalities and literal
  Bellman payoff identities at every row before the tail. It is false for an
  arbitrary product word.
- Equation (8) is player \(k\)'s own marginal survival, not joint survival;
  the unique-sure inner factor is enough to make it vanish.
- The late receiver may be the boundary clock \(m_n\) or Never.
- The target owner surely reaches the boundary and the full target reaches
  it with probability at least \(\eta\), but its
  conditional continuation need not equal \(X_n\).
- The one-root regression has \(D_*=0\); it falsifies root preservation from
  the local packet, not from the full hard Fin4 hypotheses.
- No exact-root preservation after \(c_n\), exact charged return, renewable
  rank, terminal approximate Nash profile, or uniform-equilibrium payoff is
  claimed.

## Next exact question

Can the target's residual host stopping law conditional on reaching
\(m_n\) be compared with the original tail cap response in a way that pays
the post-cut Nash--Bellman seam? A consumer may use (13); it may not silently
replace the reached conditional law by \(X_n\).
