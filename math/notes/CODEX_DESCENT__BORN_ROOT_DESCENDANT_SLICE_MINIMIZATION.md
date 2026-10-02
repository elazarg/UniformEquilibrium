# Born-root descent closes at a normalized descendant-slice minimizer

Identity: `CODEX_DESCENT`  
Date: 2026-08-31  
Status: **ordinary-mathematics audit and reduction.**  The finite
re-exactification identities in
`CODEX_ROOT__OFF_MINIMUM_BORN_ROOT_REEXACTIFIED_DESCENT.md` are valid with
the ancestry qualification in Section 2 below.  Infinite strict descents do
not need to be oriented by a real-valued rank: compact minimization of the
closed normalized descendant slice gives either a minimum-fibre cluster or
an off-minimum endpoint whose exact root correspondence is uniquely
all-Continue.  This is the same mathematical mechanism already checked for
marked-pair decorations in `Research/Quitting/NormalizedPassportMinimizer.lean`.
The four-profile response/source adapter described here is not one checked
declaration.  Its minimizer has closed-descendant provenance, not one
recovered literal prehistory.

## 1. Question

Start with a two-level off-minimum response packet.  Its low-debt endpoint
has semantic/law limit \(z\),

\[
 D(z)=L>D_*,\qquad d_j(z)=0,
\]

and a same-response sibling gives a fixed positive signed atom.  Separately,
the original tangent source and its full mover replacement give a fixed
positive actual payoff gain along the same selected ranks.  A second,
reset-face semantic point already has all-Continue as its unique exact cap
root.  If \(B(z)\) has a positive-absorption exact root, the
born-root/re-exactification operation makes another source packet with
strictly smaller limiting debt and the same normalized passport.

Can infinitely many such steps be forced to reach \(D_*\), accumulate a
positive usable charge, or stabilize at double all-Continue?

The answer supported by the present data is:

* finite arrival at \(D_*\) is not forced;
* a positive tail charge on one extension-compatible chronology is not
  forced; but
* after closing and minimizing the normalized descendant class, one obtains
  either a cluster at \(D_*\) or the double-all-Continue residual.

## 2. Audit of the one-step composition

Let \(R_n\to z\), let \(q\) be exact cap--Nash against \(B(z)\), and put
\(c=\Pr_q(\mathbf C)\in(0,1)\).  If \(e_{n,i}\) is the coordinate cap defect
of \(q\) against \(B(R_n)\), the checked identity
`quittingTerminalSemanticDebt_prefix_eq_capDefect_add_continueMass_mul`
gives

\[
 d_i(q::R_n)=e_{n,i}+c\,d_i(R_n).
\]

Continuity gives \(e_{n,i}\to0\).  Hence

\[
 D(q::R_n)\longrightarrow cL<L,
 \qquad d_j(q::R_n)\longrightarrow0.
\]

Choose an exact root \(r_n\) against the actual cap of \(q::R_n\), with
survival \(s_n\), and prefix it.  The checked exact-root scaling gives

\[
 D(r_n::q::R_n)=s_nD(q::R_n),
 \qquad
 s_n\ge {D_*\over D(q::R_n)}.
\]

After subselection,

\[
 L'=scL,\qquad D_*\le L'\le cL<L.
\]

Prefix the same roots also to the original source/full-replacement pair.
The response/sibling signed atom and the source/replacement actual payoff
gain both scale by the same joint survival.  Thus, at the limiting level,

\[
 {A'\over L'}={A\over L},
 \qquad
 {G'\over L'}={G\over L}.
\tag{2.1}
\]

These calculations are sound.

There are two scope qualifications.

1. The inner root \(q\) is not made exact at the old actual cap by placing
   the fresh exact root \(r_n\) before it.  Thus the two-row word is not an
   exact Nash--Bellman stack row by row.  What is restored is an actual
   source with one exact outer root, from which a fresh exact ray may be
   started.  Any consumer requiring exactness of every displayed inner row
   needs a separate error account.
2. Iteration requires the response/sibling packet and its dependent source
   fields to be reconstructed after the state change.  The scalar identities
   alone do not supply that reconstruction.  The closure argument below must
   therefore be formulated on a closed literal-descendant orbit, not on
   semantic pairs alone.

Neither qualification invalidates the endpointwise strict-debt operation.
They do rule out reading it immediately as a positive exact chronology.

## 3. A scalar/product regression

The debt and passport ledgers alone cannot force finite termination or a
positive tail charge.  Fix

\[
 D_*<\ell<L_0,\qquad
 L_k=\ell+2^{-k}(L_0-\ell),\qquad
 \alpha_k={L_{k+1}\over L_k}.
\]

Take born-root survival \(c_k=\alpha_k\) and fresh-root survival \(s_k=1\).
Every \(c_k\) is the survival of a product root (one player can Quit with
probability \(1-c_k\)).  Put

\[
 A_k=\theta L_k,\qquad G_k=\psi L_k
\]

for fixed positive densities.  Then all scalar identities of the descent
hold exactly:

\[
 L_{k+1}=s_kc_kL_k,\qquad
 {A_{k+1}\over L_{k+1}}={A_k\over L_k},\qquad
 {G_{k+1}\over L_{k+1}}={G_k\over L_k}.
\]

But no finite level equals \(D_*\), and

\[
 \prod_{k<N}\alpha_k={L_N\over L_0}\longrightarrow{\ell\over L_0}>0,
\]

so

\[
 \sum_{k\ge N}(1-\alpha_k)
 \le \log {L_N\over\ell}\longrightarrow0.
\tag{3.1}
\]

Thus every sufficiently late block has vanishing cumulative absorption.  The
same example with \(\ell=D_*\) approaches the minimum without ever attaining
it at a finite step.

This is an exact scalar/product-probability regression, not a fixed-table
quitting-game realization.  Its role is precise: no argument using only debt
monotonicity, survival multiplication, and invariant passport ratios can
prove finite landing or a fixed positive recurrent charge.

## 4. Exact accounting for any infinite chain

The same obstruction is intrinsic to every chain satisfying the advertised
exact limiting ledgers.  Write

\[
 \alpha_k={L_{k+1}\over L_k}=c_ks_k\in(0,1).
\]

Then, for every \(N<M\),

\[
 \prod_{k=N}^{M-1}\alpha_k={L_M\over L_N},
\qquad
 \sum_{k=N}^{M-1}(1-\alpha_k)
 \le \log {L_N\over L_M}.
\tag{4.1}
\]

If \(L_k\downarrow\ell\ge D_*>0\), the total absorption of the combined
prefix block from levels \(N\) through \(M-1\) is

\[
 1-\prod_{k=N}^{M-1}\alpha_k
 =1-{L_M\over L_N}.
\tag{4.2}
\]

It tends to zero when first \(M\to\infty\) and then \(N\to\infty\).  Hence
compact recurrence among sufficiently late levels cannot by itself carry a
fixed positive absorption charge.  A block starting at the original level
can have positive total absorption, but its endpoint has a different debt
level and is not a near-return.

In contrast, (2.1) gives

\[
 G_k=\psi L_k\ge\psi D_*>0
\]

for the retained horizontal paid fork.  Thus the data separate cleanly:
the paid fork remains macroscopic while every recurrent tail of the exact
prefix descent has vanishing absorption.  Turning the former into a temporal
edge requires a cross-track identification between the sibling and response
states; neither the scalar ledger nor compact recurrence supplies it.

## 5. The closed descendant slice

The correct replacement for iterating a real rank is compact minimization.
The required decoration is explicit.  At rectangle rank \(n\), write

* \(S_n\) for the original tangent source;
* \(E_n\) for its full mover-replacement endpoint;
* \(R_n\) for \(E_n\) after installing the observer's selected pure-time
  response; and
* \(Q_n\) for \(S_n\) after installing the same observer response.

Thus \(R_n,Q_n\) are the pair in the rectangle atom, whereas \(E_n,S_n\)
are a separate actual payoff-gain pair.  Let \(J(P)\) denote the complete
semantic/law point of an actual profile \(P\), and define the raw decoration

\[
 \mathcal D_n=(J(R_n),J(Q_n),J(E_n),J(S_n)).
\tag{5.1}
\]

The two passport functions on this fourfold compact product are

\[
 A(\mathcal D)
   =K\bigl(\mu^R(T)-\mu^Q(T)\bigr)r_j(T),
\qquad
 G(\mathcal D)=U_p(E)-U_p(S).
\tag{5.2}
\]

They are continuous functions of the actual coordinates, not free scalar
annotations.  The rectangle packet gives \(A(\mathcal D_n)\ge\gamma>0\).
The checked theorem
`fullReplacementPrescribedGain_tendsto_baseDebt` gives

\[
 G(\mathcal D_n)\longrightarrow d_p(z_*)>0
\tag{5.3}
\]

along the same strict rectangle subsequence, because \(p\) belongs to the
positive-debt support.  After deleting finitely many ranks, both passport
coordinates therefore have fixed positive floors.

For a finite product-root word \(W\), prefix **the same word** to all four
profiles and shift every retained date by \(|W|\).  Define

\[
 \mathcal O
 =\{\mathcal D(W\triangleright R_n,W\triangleright Q_n,
                    W\triangleright E_n,W\triangleright S_n):
       n\in\mathbb N,\ W\text{ a finite product-root word}\},
\tag{5.4}
\]

and let \(\mathcal K=\overline{\mathcal O}\) inside the fourfold product of
the compact semantic/law carrier.  This is a literal raw arbitrary-common-
prefix orbit, not an unspecified collection of profiles of the same type.
Prefixing by any fixed product root is a continuous self-map of
\(\mathcal K\).

A common prefix contributes identical fresh root law and prescribed payoff
to the two members of each pair.  Therefore, if its joint survival is \(c\),

\[
 A(\Phi_W\mathcal D)=cA(\mathcal D),
\qquad
 G(\Phi_W\mathcal D)=cG(\mathcal D).
\tag{5.5}
\]

This is the four-profile analogue of
`QuittingMarkedPairDecoratedFamily.prefixOrbitCarrier` and
`prefixMap_mem_carrier` in
`Research/Quitting/NormalizedPassportPrefixOrbit.lean`.

Fix positive densities \(\theta,\psi\) strictly below the initial limiting
ratios, and intersect the closed orbit with

\[
 d_j(R)=0,\qquad
 A\ge\theta D(R),\qquad
 G\ge\psi D(R).
\tag{5.6}
\]

Call the resulting set \(\mathcal K_{\theta,\psi}^0\).  No post-mark tail
coordinate is claimed here.  If a later consumer needs one, it must be added
as a fifth compact semantic/law coordinate on which the prefix action is the
identity, and its required closed equality must be stated separately.

It is compact and nonempty.  The equality \(d_j=0\) is important: it is the
response coordinate needed for the minimum-fibre reset adapter.  Although an
arbitrary prefix need not preserve this equality, an exact cap--Nash prefix
does preserve it, because every debt coordinate scales by joint survival.
The signed atom and paid gain also scale by the same survival.  Therefore an
exact cap--Nash prefix maps a point of
\(\mathcal K_{\theta,\psi}^0\) back into
\(\mathcal K_{\theta,\psi}^0\).

The only source subtlety is that a root exact at a limit point need not be
exact at its raw actualizers.  This does not invalidate closed-orbit
membership: the raw orbit was enlarged using all finite literal product-root
prefixes, so continuity places the fixed-root prefix of the limit in its
closure.  If one insists on a source with a fresh exact outer root, the
one-step re-exactification of Section 2 supplies it and preserves (5.6) in
the limit.

This is exactly the distinction already implemented for marked-pair data in
`NormalizedPassportMinimizer.lean`: finite approximate prefixes need not
preserve a saturated density inequality, while the closed limiting slice is
invariant under an exact root at the displayed limiting cap.

## 6. Minimization theorem

Minimize the response debt \(D(R)\) on
\(\mathcal K_{\theta,\psi}^0\), and let \(P_{\min}\) be a minimizer with
response semantic point \(z_{\min}\) and debt

\[
 \ell=D(z_{\min})\ge D_*.
\]

Suppose \(q\) is an exact cap--Nash root at \(B(z_{\min})\), with survival
\(c<1\).  Exact prefix scaling gives a point in the same closed slice with

\[
 d_j'=0,\qquad D'=c\ell<\ell,\qquad
 A'=cA\ge\theta c\ell,\qquad
 G'=cG\ge\psi c\ell.
\]

This contradicts minimality.  Hence every exact root at \(B(z_{\min})\) has
survival one and is literally all-Continue.  Finite root-game Nash existence
then gives

\[
 \boxed{
   \operatorname{Nash}(B(z_{\min}))=\{\mathbf C\}.
 }
\tag{6.1}
\]

There are two cases.

### Minimum-fibre case

If \(\ell=D_*\), raw closed-descendant actualizers converge to a
global-minimum law
point with \(d_j=0\) and nonvanishing signed/gain densities.  In the Fin4
hard residual, the finite-atom plus singleton/Never cap-tightness argument
from `CODEX_GATE__VANISHING_RESPONSE_MAXROOT_RESET_TRICHOTOMY.md` makes
opponent incidence automatic.  The point therefore enters reset-rigid.
Finite equality need not have occurred at any descendant.

### Strict case

If \(\ell>D_*\), equation (6.1) is the unique-all-Continue response endpoint.
The reset-face selector \(m\) carried by the original two-level residual is
already unique all-Continue.  Keeping that certificate as an external
same-origin conjunction gives the sharpened double-all-Continue cell while
retaining

\[
 A\ge\theta D_* >0,\qquad G\ge\psi D_*>0.
\tag{6.2}
\]

No assertion is made that \(m\) is a descendant of, law-matched to, or
chronologically composable with \(z_{\min}\).  No infinite iterative choice
and no transfinite argument are needed.

## 7. Relation to the checked normalized-passport theorem

The mathematical engine of Section 5 is already kernel-checked for the
marked-pair decoration:

* `normalizedPassportSlice_isCompact`;
* `exists_minimum_normalizedPassportSlice`;
* `prefixMap_mem_normalizedPassportSlice_of_isZeroNash`;
* `minimum_normalizedPassportSlice_exactRoot_eq_allContinue`; and
* `exists_minimum_normalizedPassportSlice_eq_or_strict_inert`

in `Research/Quitting/NormalizedPassportMinimizer.lean`.

That checked theorem does not literally mention the present paired response
endpoint, the signed response/sibling atom, or the closed condition
\(d_j=0\).  The proof above is the direct decorated-carrier extension.  If
the current response packet can instead be adapted to the existing
`QuittingMarkedPairDecoratedFamily` with its positive marked mass and actual
gain fields, then no new minimization theorem is needed at all; only that
adapter and the closed zero-debt refinement are missing.

## 8. What remains

The descent question is therefore not a remaining dynamical trichotomy.
Normalized descendant-slice minimization settles it as

\[
 \boxed{
   \text{minimum-fibre reset-rigid cluster}
   \quad\lor\quad
   \text{closed-descendant double-all-Continue minimizer}.
 }
\]

It does not consume either output.  In particular, the invariant positive
gain belongs to the distinct original-source/full-replacement pair, while
the signed atom belongs to the response/sibling pair.  Neither is a temporal
exit from the response minimizer, whose exact cap roots are uniquely
all-Continue.  The
remaining mathematics is the consumer of that double-all-Continue port, not
termination of born-root descent.

## 9. Sources inspected

* `notes/CODEX_ROOT__OFF_MINIMUM_BORN_ROOT_REEXACTIFIED_DESCENT.md`;
* `notes/CODEX_GATE__VANISHING_RESPONSE_MAXROOT_RESET_TRICHOTOMY.md`;
* `notes/FORCED_PAIR_REVIEW__SUPPORT_ENTRY_CARRIER_RESTART_AND_NONLIFTABILITY.md`;
* `notes/FORCED_PAIR_REVIEW__APPROXIMATE_SUPPORT_ENTRY_REEXACTIFICATION.md`;
* `notes/PAIR_WALL_REVIEW__NORMALIZED_PASSPORT_INFIMUM_CLOSURE.md`;
* `notes/FORCED_PAIR_REVIEW__NORMALIZED_PASSPORT_MINIMIZER_ELIMINATES_SUPPORT_ENTRY.md`;
* `Research/Quitting/NormalizedPassportPrefixOrbit.lean`;
* `Research/Quitting/NormalizedPassportMinimizer.lean`;
* `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticOwnStrategyTransport.lean`;
* `UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashEndpointTransport.lean`;
* `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PositiveTotalSlopeFullReplacement.lean`;
* `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/ContinuePrefixAtomAccess.lean`; and
* `UniformEquilibrium/Quitting/Root/NashExistence.lean`.

## 10. Next question

At the off-minimum minimizer in (6.1)--(6.2), can the positive horizontal
signed response passport and the distinct positive source/replacement gain
be turned into a source-faithful finite chronology even
though both displayed exact-root correspondences are uniquely
all-Continue?  Any successful argument must alter a cap or use a nonlocal
stopping-law splice before asking for an absorbing exact root.
