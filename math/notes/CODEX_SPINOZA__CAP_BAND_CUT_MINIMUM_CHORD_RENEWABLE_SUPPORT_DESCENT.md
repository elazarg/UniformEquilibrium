# The live cap-band cut gives an off-minimum port or a renewable minimum support descent

Author: CODEX_SPINOZA

## Status

**Exact ordinary mathematics; global source-renewal reduction, not
Lean-checked and not a terminal consumer.**  Normalize the unique-sure live
cap-band source and target at their literal first disagreement.  The source
reaches that cut with a fixed probability, so the normalized pair is an
actual one-player response edge with a fixed conditional gain.  The source
endpoint retains a fixed mover debt, while the target endpoint has vanishing
mover debt.

After joint semantic/law compactification, either one endpoint is uniformly
off the global minimum fibre, giving the already known source-attached
off-minimum paid port, or both endpoints are minimum.  In the latter case,
mixing the mover's two complete stopping laws produces an entire executable
minimum chord.  Every proper chord point has positive-debt support strictly
containing the target support.  The chord point and target admit checked
same-point minimum-source regeneration.  Using a one-use origin state, the
target enters the checked renewable tangent trace with support at most three;
the literal chord-to-target replacement is retained as ancestry but is not
asserted to be a full-replacement cluster of that re-extracted tangent family.

This is the first use of the cap-band edge that yields a finite rank rather
than another local root inequality.  It does not consume the off-minimum arm.

## 1. Source-normalized response pair

Let \(I=\operatorname{Fin}4\), let rewards have absolute value at most \(R\),
and work in the no-uniform-payoff hard branch with global minimum total debt
\(D_*>0\).

For each \(n\), let

\[
 Y_n=\Sigma_n[k\leftarrow \widehat s_{n,k}]
\tag{1}
\]

be the vanishing-width live cap-band target of the unique-sure persistent
word.  Let \(c_n\) be its literal first cap-band cut and \(e_n\downarrow0\)
its band width.  The checked cap-band fields and exact-word late-receiver
screen give, after a finite shift,

\[
 g_n:=U_k(Y_n)-U_k(\Sigma_n)\ge D_*/2-e_n\ge D_*/4,
 \qquad d_k(Y_n)\le e_n,
\tag{2}
\]

and

\[
 r_n:=\Pr_{\Sigma_n}(T_I\ge c_n)\ge\kappa>0.
\tag{3}
\]

The profiles agree literally at every date strictly before \(c_n\).  Let
\(A_n\) and \(B_n\) be their actual suffix profiles beginning at \(c_n\):

\[
 A_n=\operatorname{Shift}_{c_n}(\Sigma_n),
 \qquad
 B_n=\operatorname{Shift}_{c_n}(Y_n).
\tag{4}
\]

Then \(B_n=A_n[k\leftarrow b_{n,k}]\) is a literal complete one-player
replacement.  Define its conditional gain

\[
 G_n=U_k(B_n)-U_k(A_n).
\tag{5}
\]

### Lemma 1.1: fixed source debt and vanishing target debt

For every retained \(n\),

\[
 g_n=r_nG_n,
 \qquad G_n\ge D_*/4,
 \qquad d_k(A_n)\ge G_n,
\tag{6}
\]

and

\[
 d_k(B_n)\le {e_n\over r_n}
 \le {e_n\over\kappa}\longrightarrow0.
\tag{7}
\]

Moreover own-cap invariance gives the exact identity

\[
 d_k(A_n)-d_k(B_n)=G_n.
\tag{8}
\]

### Proof

The common-prefix payoff identity gives \(g_n=r_nG_n\).  Since \(r_n\le1\),
(2) proves the gain floor.  The complete cap at \(A_n\) dominates the actual
replacement \(B_n\), so \(d_k(A_n)\ge G_n\).

Any complete deviation by \(k\) at \(B_n\) can be lifted behind the unchanged
prefix of \(Y_n\).  Its full gain is \(r_n\) times its suffix gain.  Taking
suprema gives

\[
 r_nd_k(B_n)\le d_k(Y_n),
\]

which proves (7).  Finally \(A_n,B_n\) have identical opponents, so player
\(k\)'s unrestricted cap is identical at the two profiles.  Subtract their
prescribed payoffs to obtain (8).  QED

No Nash property of the target word is used here.  Fixed full reach at the
actual first disagreement is the essential new source field.

## 2. Compact endpoint split

Pass to one subsequence on which the two terminal semantic/law points
converge:

\[
 (\operatorname{Sem}(A_n),\operatorname{Law}(A_n))\to (A,\mu_A),
 \qquad
 (\operatorname{Sem}(B_n),\operatorname{Law}(B_n))\to (B,\mu_B),
\tag{9}
\]

and \(G_n\to G\).  Compactness and (6)--(8) give

\[
 G\ge D_*/4,
 \qquad d_k(A)\ge D_*/4,
 \qquad d_k(B)=0,
 \qquad d_k(A)=G.
\tag{10}
\]

Both semantic endpoints lie in the terminal-semantic carrier, so

\[
 D(A),D(B)\ge D_*.
\tag{11}
\]

There is an exhaustive closed/open split.

1. If \(D(A)>D_*\) or \(D(B)>D_*\), the corresponding actual suffix sequence
   is eventually a fixed distance off the minimum fibre.  It remains attached
   to the literal paid response pair (4)--(6).  This is the established
   off-minimum source/full-replacement port, not a newly claimed consumer.
2. Otherwise

   \[
   D(A)=D(B)=D_*.
   \tag{12}
   \]

The rest of the note treats the second case.

## 3. The executable minimum chord

Fix once and for all \(0<\theta<1\).  Mix only player \(k\)'s complete
stopping laws in the actual suffix profiles:

\[
 H_{n,\theta}=(1-\theta)A_n+_k\theta B_n.
\tag{13}
\]

This is private one-player randomization encoded as the corresponding
behavioral stopping-law mixture, not a public correlated coin.  It satisfies

\[
 B_n=H_{n,\theta}[k\leftarrow b_{n,k}]
\tag{14}
\]

literally, and payoff/law affinity gives

\[
 U_k(B_n)-U_k(H_{n,\theta})=(1-\theta)G_n,
\tag{15}
\]

\[
 \operatorname{Law}(H_{n,\theta})
 =(1-\theta)\operatorname{Law}(A_n)
   +\theta\operatorname{Law}(B_n).
\tag{16}
\]

Pass to a further joint cluster

\[
 (\operatorname{Sem}(H_{n,\theta}),
   \operatorname{Law}(H_{n,\theta}))\to(H_\theta,\mu_\theta).
\tag{17}
\]

### Theorem 3.1: minimum-chord support descent

Under (12),

\[
 D(H_\theta)=D_*,
 \qquad
 d_i(H_\theta)=(1-\theta)d_i(A)+\theta d_i(B)
 \quad(i\in I),
\tag{18}
\]

and

\[
 \operatorname{supp}^+d(B)
 \subsetneq
 \operatorname{supp}^+d(H_\theta).
\tag{19}
\]

The literal full replacements (14) have limiting mover gain

\[
 (1-\theta)G\ge(1-\theta)D_*/4>0,
\tag{20}
\]

and their target cluster kills the mover debt exactly:

\[
 d_k(B)=0<d_k(H_\theta)=(1-\theta)d_k(A).
\tag{21}
\]

### Proof

Terminal payoff and outcome law are affine under a one-player stopping-law
mixture, while each unrestricted cap and hence each debt coordinate is
convex.  Thus

\[
 D(H_\theta)
 \le(1-\theta)D(A)+\theta D(B)=D_*.
\tag{22}
\]

Carrier minimality gives the reverse inequality.  Equality of the sums of
the four coordinatewise convexity inequalities forces equality in each
coordinate, proving (18).  This is the checked
`quittingTerminalSemanticDebt_stoppingLawMixture_eq_of_minimum_sameDebtSum`
mechanism.

If \(d_i(B)>0\), (18) gives
\(d_i(H_\theta)\ge\theta d_i(B)>0\), so the inclusion in (19) holds.  It is
strict because (10), (18) give \(k\in\operatorname{supp}^+d(H_\theta)\),
whereas \(k\notin\operatorname{supp}^+d(B)\).  Equations (15) and (10) prove
(20)--(21).  QED

## 4. Literal source regeneration and finite rank

The hard residual is unchanged because all objects use the original reward
table.  The joint points \((H_\theta,\mu_\theta)\) and \((B,\mu_B)\) are
minimum joint semantic/law carrier points.  The checked Fin4 finite-atom
theorem gives a positive finite terminal atom at each such minimum point, and
same-point causalization packages each as a complete
`FinFourMinimumAtomProducer`.

The endpoint source may be regenerated at the exact joint point
\((B,\mu_B)\).  Equations (19)--(21) retain the literal paid ancestry

\[
 (H_\theta,\mu_\theta)
 \longrightarrow
 (B,\mu_B)
\tag{23}
\]

and imply \(|\operatorname{supp}^+d(B)|\le3\).  Attach an independently
re-extracted positive-minimum tangent family whose base is exactly \(B\), as
provided by `exists_positiveMinimumDebtTangentFamily_of_pair`.  With one
nonrecurrent origin phase, define

\[
 \rho(\mathsf{terminal})=0,\qquad
 \rho(\mathsf{tangent}(X))=1+|\operatorname{supp}^+d(X)|,\qquad
 \rho(\mathsf{origin})=5.
\tag{24}
\]

The origin-to-tangent entry strictly decreases this rank because the target
support has cardinality at most three.  Every later recursive minimum-fibre
child in the checked canonical system strictly lowers support; the other
tangent outputs are its named residual exits.  The incoming entry also
retains the literal fixed-gain full-replacement sequence (14); it is not
inferred merely from the two limiting debt vectors.  The generic tangent
family re-extracted at \(B\) need not use that incoming replacement as one of
its own columns, and no such identification is claimed.

## 5. Conjecture-facing reduction

The structured unique-sure cap-band edge now has the global exhaustive output

\[
 \boxed{
 \text{source-attached off-minimum paid port}
 \quad\text{or}\quad
 \text{one-use entry into the renewable minimum-source support trace}.}
\tag{25}
\]

The second arm is a genuine finite-rank entry.  The minimum chord proves that
the cap-repaired endpoint has support at most three while preserving a
literal paid edge into that endpoint.  A one-use origin phase then enters the
generic checked tangent trace based at the regenerated endpoint.  This does
not identify the incoming paid edge with a column of the re-extracted tangent
family.

The first arm is the same off-minimum paid-port/source-reentry waist already
present elsewhere.  Nothing here charges or returns that arm.

## Sources inspected

- `notes/CODEX_SPINOZA__UNIQUE_SURE_PERSISTENT_WORD_HOST_PAYER_CAP_BAND.md`;
- `notes/CODEX_SPINOZA__EXACT_WORD_FORCES_LATE_CAP_BAND_RECEIVER_AND_LIVE_TARGET.md`;
- `notes/CODEX_SPINOZA__LIVE_CAP_TARGET_POSTTAIL_DISTINCT_DEBTOR.md`;
- `notes/CODEX_MINER__ACTUAL_PAID_FIRST_DISAGREEMENT_SUFFIX_COMPACTIFICATION.md`;
- `formalized/FIN4_MINIMUM_RESPONSE_CHORD_ATOM_AND_SOURCE_REGENERATION.md`;
- `formalized/CANONICAL_FIN4_RENEWABLE_MINIMUM_SOURCE_SUPPORT_DESCENT.md`;
- `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/CapBandRedistribution.lean`;
- `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawMinimumFiberAffine.lean`;
- `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumLawFiniteAtom.lean`; and
- `Research/Quitting/SourceFaithfulMinimumLawCausalization.lean`.

## Boundary and nonclaims

- The reach floor at the literal first disagreement is indispensable for
  (7).  Deleted-player reach alone would not kill the target suffix debt.
- The off-minimum alternative means strict excess at a compact limit and
  hence an eventual uniform excess after subselection.  It is not called a
  terminal consumer.
- The chord uses one-player stopping-law mixtures.  No semantic coordinatewise
  interpolation is postulated.
- The regenerated child source has the same joint semantic/law point as the
  endpoint, but need not reuse the original calendar or cap-band cut.
- Rank descent is asserted only for the one-use origin entry and the checked
  downstream tangent trace.  It does not prove that arbitrary
  better-response iteration decreases support.
- No exact Nash--Bellman return, terminal approximate Nash profile, or
  uniform-equilibrium payoff is proved.

## Next exact question

Can the source-attached off-minimum arm in (25) be charged to a return to the
new minimum chord source, or does it again admit the known all-Continue cap
stall?  The minimum-fibre arm no longer needs a cap-to-prescribed root bridge;
its finite rank is already literal and renewable.
