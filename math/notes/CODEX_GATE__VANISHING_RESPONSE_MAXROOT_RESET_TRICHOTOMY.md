# Vanishing-response maximal roots: charged rebase, reset-rigid return, or a typed two-level inert residual

Identity: `CODEX_GATE`  
Date: 2026-08-31  
Status: **ordinary mathematics composed with named checked declarations; the
source-level trichotomy and quantitative ledgers below are proved.  In the
actual Fin4 hard residual, every minimum-fibre response cluster automatically
has positive observer incidence and enters reset-rigid; this uses a finite
atom at every global-minimum law plus singleton/Never cap tightness, not the
rectangle atom's sign.  The signed rectangle atom itself orients incidence to
the low-debt endpoint only in the positive-reward, genuine-opponent cell.  An
exact Fin4 endpoint regression proves that this narrower orientation is false
in general.  No branch here is a complete chronological consumer or a
uniform-equilibrium proof.**

This note continues
[`CODEX_GATE__MAXIMAL_TARGET_CAP_REROOT_TRICHOTOMY.md`](CODEX_GATE__MAXIMAL_TARGET_CAP_REROOT_TRICHOTOMY.md),
especially its Section 10 question.  It uses the joint compactification and
reset-face selector in
`RectangleResetFaceMinimizer.lean`.  The exhaustive static sign classification
itself was already obtained in
[`CODEX_MINER__SIGNED_CAUSAL_RECTANGLE_ORIENTATION_COMPILER_BOUNDARY.md`](CODEX_MINER__SIGNED_CAUSAL_RECTANGLE_ORIENTATION_COMPILER_BOUNDARY.md);
the new content here is its composition with **literal endpointwise maximal
exact roots**, the exact charge ledger, and the resulting reset/two-level
inert split.

## 1. Exact question and data

Let the player type be `Fin 4`, fix `M>0`, and let the terminal reward table
be bounded by

\[
  |r_i(S)|\leq M,
\]

and suppose that a `QuittingPositiveMinimumDebtTangentFamily` and a
`QuittingStoppingLawVanishingDebtRectangleSequence` have been supplied.  Thus

\[
 D_*:=D(\texttt{frontier.base})>0
\]

is the global minimum of total unrestricted terminal semantic debt.  Write
`j` for the fixed observer, `T` for the fixed nonempty terminal coalition,
and `c>0` for `packet.charge`.

Apply, in order,

- `QuittingStoppingLawVanishingDebtRectangleSequence.nonempty_resetFaceDispatch`,
  and
- `QuittingStoppingLawRectangleResetFaceDispatch.nonempty_jointAtomLimit`

from
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/RectangleResetFaceMinimizer.lean`.
After composing their two strict subsequences, let

\[
 R_n=\text{literal low-debt double endpoint},\qquad
 Q_n=\text{literal same-response sibling}.                 \tag{1.1}
\]

Their complete semantic/law points converge to

\[
 z=((U^z,B^z),\mu^z),\qquad
 q=((U^q,B^q),\mu^q).                                     \tag{1.2}
\]

Put

\[
 D_n=D(\operatorname{Sem}(R_n)),\quad D_z=D(z),\quad
 K=|\mathsf{TerminalOutcome}(\operatorname{Fin}4)|=16,
 \quad \gamma=c/4.                                       \tag{1.3}
\]

The checked compactification gives

\[
 z,q\in\mathcal C_{\rm sem,law},\qquad
 d_j(z)=0,\qquad D_n\longrightarrow D_z,                 \tag{1.4}
\]

and the exact limiting signed atom

\[
 \boxed{\gamma\leq
 K\bigl(\mu^z(T)-\mu^q(T)\bigr)r_j(T).}                  \tag{1.5}
\]

In particular `r_j(T)` is nonzero.  The dispatch also supplies a separate
reset-face minimizer `m` satisfying

\[
 d_j(m)=0,\qquad D_*\leq D(m)\leq D_z,                   \tag{1.6}
\]

such that all Continue is the unique exact cap--Nash root at `m`.  The law of
`m` need not equal `mu^z`; this loss of law provenance is an explicit field of
the checked interface, not an omission below.

When a reset-rigid output is invoked, also fix the terminal exploitability
witness available in the no-uniform-payoff regime.  For the strengthened
minimum-fibre conclusion in Section 3, fix the actual
`FinFourQuantitativeFullSupportHardResidual`; it supplies both that witness
and punishment-normality.  The rectangle packet by itself contains neither
of these fields.

## 2. Literal maximal exact roots and their ledgers

For every `n`, let `N_n` be the nonempty compact set of exact product roots
which are Nash against the actual cap `B(R_n)`.  Nonemptiness is
`exists_isZeroQuittingRootNash`; closedness is immediate from the finite root
inequalities.  The continuous absorption function therefore attains its
maximum.  Choose a maximizer `p_n` and write

\[
 a_n=1-\prod_i p_{n,i}(\mathsf{Continue}),\qquad
 s_n=1-a_n.                                             \tag{2.1}
\]

Prefix the **same** root to both literal endpoints:

\[
 \widehat R_n=p_n\mathbin{::}R_n,\qquad
 \widehat Q_n=p_n\mathbin{::}Q_n.                       \tag{2.2}
\]

Only the first prefix in (2.2) is asserted to be Nash--Bellman: `p_n` was
selected against the cap of `R_n`, not the cap of `Q_n`.  The second profile
is used solely to retain the exact signed-law comparison.

### Proposition 2.1 (exact root charge and retained atom)

Define

\[
 \kappa_n=a_nD_n.                                       \tag{2.3}
\]

Then, for every `n`,

\[
 d_i(\widehat R_n)=s_nd_i(R_n),\qquad
 D(\widehat R_n)=s_nD_n,                                \tag{2.4}
\]

\[
 \boxed{\kappa_n=D_n-D(\widehat R_n)\leq D_n-D_*},     \tag{2.5}
\]

and

\[
 \boxed{s_n\geq {D_*\over D_n}\geq {D_*\over8M}>0.}   \tag{2.6}
\]

Moreover the common prefix cancels from the fresh absorbing part of the law,
so its old-suffix atom scales exactly:

\[
 \operatorname{Atom}(\widehat R_n,\widehat Q_n;j,T)
   =s_n\operatorname{Atom}(R_n,Q_n;j,T).                \tag{2.7}
\]

Consequently

\[
 \boxed{
 {cD_*\over32M}
 \leq K\operatorname{Atom}(\widehat R_n,
                             \widehat Q_n;j,T).}         \tag{2.8}
\]

Finally `d_j(\widehat R_n)\to0`.

#### Proof

Equation (2.4) is
`quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash`.
The prefixed point remains in the terminal semantic/law carrier, so global
minimality gives `D_* <= s_n D_n`, proving (2.5) and the first inequality in
(2.6).  A terminal payoff and its unrestricted cap both lie in `[-M,M]`.
Every debt is therefore at most `2M`, and four players give `D_n<=8M`.

Equation (2.7) is the one-root case of
`quittingTerminalPayoffDifferenceAtom_literalRootStack`.  Multiply the
literal packet inequality `c/4 <= K Atom(R_n,Q_n;j,T)` by `s_n`, then use
(2.6), to get (2.8).  The final assertion follows by multiplying the checked
convergence `d_j(R_n) -> 0` by `s_n in [0,1]`.  `QED`

The point of (2.8) is that re-rooting cannot screen the old rectangle atom,
even when the fresh absorption itself tends to zero.

## 3. Exhaustive source-level trichotomy

The trichotomy must be stated on the roots `p_n` at the **literal caps**.
Choosing an absorbing root only at the compact limit `B^z` is not enough:
the exact Nash-root correspondence is closed/upper hemicontinuous, but exact
roots can be born at a limiting cap and need not be approximable by exact
roots at the preceding caps.

Exactly one of the following ordered alternatives holds.

### Alternative C: uniformly charged fresh roots

There are `eta>0` and a strict subsequence such that

\[
 a_n\geq\eta,\qquad
 \boxed{\kappa_n\geq\eta D_*>0}                      \tag{3.1}
\]

at every selected index.  Each row is a literal exact cap-root prefix of the
actual low-debt endpoint, and (2.8) retains a fixed positive fraction of the
same source-provenant signed atom behind it.

This is a genuine quantitative charged rebase.  It is not by itself a return
to the old frontier source, nor an extension-compatible renewable edge.

### Alternative R: minimum-fibre reset-rigid entry

If Alternative C fails, then `a_n->0`.  Suppose additionally that

\[
 D_z=D_*                                                    \tag{3.2}
\]

and

\[
 0<\operatorname{Inc}^{\rm opp}_j(\mu^z).                  \tag{3.3}
\]

Then `z` is a positive global-minimum law point with `d_j(z)=0` and positive
opponent incidence.  It therefore enters a genuine
`QuittingLawTightResetRigidChamber`.

To see the exact checked adapter, take `origin=minimum=point=z`.  The origin
belongs to its law-tight saturation hull.  Every hull point belongs to the
ambient carrier, and (3.2) plus global minimality of `frontier.base` proves
that `z` minimizes this hull.  Thus `z` lies in its own minimum face.  Apply
`exists_quittingLawTightResetRigidChamber` with source `frontier.base`, reset
owner `j`, and (3.3).  This retains the law, a positive incidence coordinate,
the fixed-law reset dispatch, the returned minimum-face point, and its exact
all-Continue fixed arm.

At a positive global minimum, `z` itself also has all Continue as its unique
exact cap root: any absorbing exact prefix would scale `D_*` strictly below
`D_*`.  This agrees with
`quittingLawTightCapNashSaturationMinimumFace_rootNash_iff_allContinue`.

#### Proposition 3.2 (the hard residual makes target incidence automatic)

Assume the actual `FinFourQuantitativeFullSupportHardResidual` for this reward
table.  If `D_z=D_*`, then

\[
 \boxed{0<\operatorname{Inc}^{\rm opp}_j(\mu^z).}        \tag{3.4}
\]

Consequently every minimum-fibre rectangle response cluster enters
Alternative R, regardless of the sign or terminal label of the rectangle
atom.

#### Proof

Since `z` belongs to the joint carrier and `D_z=D_*`, its semantic coordinate
is a global minimizer.  Also (2.5) gives

\[
 0\leq a_nD_n\leq D_n-D_*\longrightarrow0.
\]

Since `D_n->D_*>0`, this already forces `a_n->0`, so Alternative C is
impossible.  Apply
`exists_positive_finiteLawAtom_of_finFourHardResidual_minimum` to obtain a
finite terminal `S` with

\[
 0<\mu^z(S).                                            \tag{3.5}
\]

Suppose instead that the total opponent incidence of `j` were zero.  The
simplex property and
`terminal_eq_singleton_of_totalOpponentIncidence_eq_zero_of_mass_pos` imply
that **every** finite terminal of positive mass equals `{j}`.  In particular,
the terminal `S` from (3.5) is `{j}`, so, for

\[
 p=\mu^z(\{j\})>0,
\]

we have `p>0`.  For any finite terminal `A`, if `A={j}` its mass is `p`; if
`A != {j}`, then its nonnegative mass cannot be positive, since the same
terminal-support lemma would force `A={j}`.  Hence that mass is zero.  The
simplex identity now reads

\[
 \mu^z(\mathsf{Never})+p=1.
\]

Thus the complete law is supported on `{j}` and Never, with the exact
coordinates

\[
 \mu^z(A)=\mathbf 1_{A=\{j\}}p,
 \qquad \mu^z(\mathsf{Never})=1-p.                    \tag{3.6}
\]

The checked chronology/topology theorem
`terminalSemanticLaw_singletonNever_zeroDebt_cap_eq_singletonReward`, applied
with `d_j(z)=0`, then gives

\[
 B^z_j=r_j(\{j\}).                                     \tag{3.7}
\]

On the other hand, the positive global-minimum singleton margin
`minimumTerminalSemantic_singletonMargin` gives

\[
 0<D_*\leq B^z_j-r_j(\{j\})=0,                        \tag{3.8}
\]

a contradiction.  This proves (3.4).  Applying
`exists_quittingLawTightResetRigidChamber` as above, now with
`residual.witness`, proves the final assertion.  `QED`

This argument is stronger than trying to orient the rectangle atom.  The
finite atom used in (3.5) can be a completely different terminal coordinate;
zero total incidence would force it, and every other positive finite
coordinate, onto `{j}` before cap tightness contradicts the moat.  The cap
tightness theorem is essential: singleton/Never support and the singleton
margin alone do not yield the contradiction until (3.7) identifies the cap
with the singleton reward.

### Alternative I: typed two-level inert residual

If neither Alternative C nor Alternative R holds, then all of the following
data remain simultaneously:

\[
 a_n\longrightarrow0,\qquad \kappa_n\longrightarrow0,    \tag{3.9}
\]

\[
 d_j(z)=d_j(m)=0,\qquad D_*\leq D(m)\leq D_z,              \tag{3.10}
\]

\[
 \text{all Continue is the unique exact cap root at }m,   \tag{3.11}
\]

the exact positive signed atom (1.5), and the exhaustive failure tag

\[
 \boxed{D_*<D_z\quad\text{or}\quad
        \operatorname{Inc}^{\rm opp}_j(\mu^z)=0.}         \tag{3.12}
\]

Under the maintained Fin4 hard residual, Proposition 3.2 eliminates the
second disjunct whenever `D_z=D_*`.  Hence the actual residual sharpens to

\[
 \boxed{D_*<D_z.}                                        \tag{3.13}
\]

The fresh prefix does not wash out the endpoint: absorption going to zero
implies `p_n->allContinue`; the terminal laws differ from their suffix laws
by at most `2a_n` in `l1`.  Hence the prefixed low-debt endpoints still
converge to `z`, while (2.8) keeps their signed suffix atom uniformly
positive.  Thus (3.9) is an actual source-stream inertness statement, and
(3.11) is an exact semantic reset-selector inertness statement.  These are the
two levels meant by “two-level inert.”  It is not a claim that every
law-preserving selector is inert.

There is one further exact subtyping at the endpoint cap `B^z`.  Let `a_z`
be maximum exact-root absorption there.

- If `a_z=0`, all Continue is also the unique exact root at the atom-carrying
  endpoint `z`.  This is the strong double-all-Continue cell.
- If `a_z>0`, the absorbing root is **born at the compact limit**: no sequence
  of exact roots against the literal caps `B(R_n)` can approach it, because
  every such root has absorption at most `a_n->0`.  It is a carrier-level
  charge, not a literal source-level rebase.  Treating it as a chronological
  edge would reverse the closed-graph implication for the Nash
  correspondence.

If `D_*<D_z` and the endpoint law happens independently to have positive
opponent incidence, the existing fixed-law reset dispatcher is still
available.  Its absorbing-descent/all-Continue alternative and, in the
positive-reward cell, the checked aligned-or-law-premium bridge must be
retained.  They do not collapse (3.12), because their minimizing semantic
point need not preserve the literal endpoint chronology.

#### Exhaustiveness proof

If the nonnegative bounded sequence `a_n` does not tend to zero, some
`eta>0` occurs infinitely often; select those indices and use (2.5) to get
Alternative C.  Otherwise `a_n->0`.  The checked field
`cluster_fiber_or_separated` says exactly `D_z=D_*` or `D_*<D_z`.  Total
opponent incidence is nonnegative.  If the first equality and strict positive
incidence both hold, Alternative R applies.  Otherwise (3.12) holds and the
reset-face dispatch supplies (3.10)--(3.11), giving Alternative I.  Under
the hard residual, Proposition 3.2 shows that equality `D_z=D_*` is always
the reset-rigid case, leaving only (3.13) in Alternative I.  `QED`

## 4. Exactly when the signed atom is on the low-debt target

The atom (1.5) has a complete quantitative polarity.  Let

\[
 \ell={c/4\over KM}>0.                                  \tag{4.1}
\]

### Proposition 4.1 (target-versus-sibling orientation)

1. If `r_j(T)>0`, then

   \[
   \mu^z(T)-\mu^q(T)\geq {c/4\over K r_j(T)}\geq\ell,
   \qquad \mu^z(T)\geq\ell.                             \tag{4.2}
   \]

   If `T` contains some `other != j`, then the **low-debt target** has

   \[
   \operatorname{Inc}_{j,other}(\mu^z)\geq\ell>0.        \tag{4.3}
   \]

   This is exactly the hypothesis of
   `QuittingStoppingLawRectangleJointAtomLimit.endpoint_opponentIncidence_pos`
   and its fixed-law reset consumer.

2. If `r_j(T)<0`, then

   \[
   \mu^q(T)-\mu^z(T)\geq {c/4\over K|r_j(T)|}\geq\ell,
   \qquad \mu^q(T)\geq\ell.                             \tag{4.4}
   \]

   The quantitative mass is on the **sibling**.  There is no positive lower
   bound at all for `mu^z(T)` from the signed atom.

3. If `T={j}` and the reward is positive, (4.2) gives target singleton mass
   but not opponent incidence.  This cell belongs to the checked singleton
   static dispatcher, not to the incidence-reset adapter.

#### Proof

Divide (1.5) by the positive constants and use the sign of `r_j(T)`.  In the
positive case, nonnegativity of `mu^q(T)` gives the second inequality in
(4.2); in the negative case, nonnegativity of `mu^z(T)` gives (4.4).  The
reward bound replaces `|r_j(T)|` by `M`.  If `other` lies in `T` and differs
from `j`, the corresponding incidence sum contains the nonnegative summand
`mu^z(T)`.  `QED`

Thus the answer to the requested orientation question is **no in general**.
It is **yes, quantitatively**, precisely in the positive-reward cell whose
terminal contains a genuine opponent.  The checked
`negativeTarget_sourceMassLower` theorem in
`StoppingLaw/NegativeTargetAtomicDispatch.lean` records the opposite
orientation on literal source endpoints; the distinction is already part of
the maintained API.

An important consequence for Alternative I is:

\[
 D_z=D_*\text{ and }\operatorname{Inc}^{\rm opp}_j(\mu^z)=0
 \quad\Longrightarrow\quad
 r_j(T)<0\text{ or }T=\{j\}.                           \tag{4.5}
\]

Indeed, any nonempty terminal other than `{j}` contains some player distinct
from `j`; positive reward would then contradict (4.3).

Equation (4.5) is only the rectangle atom's local sign classification.  In
the actual hard residual, Proposition 3.2 rules out its minimum-fibre
zero-incidence premise altogether, using a possibly different positive
finite atom.  Therefore no sign choice for the rectangle atom is needed to
enter reset-rigid after an exact minimum return.

## 5. Exact Fin4 regression for the failed orientation

The following deterministic table realizes the narrow endpoint obstruction,
including a full-debt source, a positive observer debt rise, an exact
zero-debt response endpoint, a negative signed atom carried entirely by its
sibling, and a unique all-Continue target cap root.

Let the players be `m,j,a,b`.  For every nonempty coalition `S`, define

\[
 r_m(S)=\begin{cases}-1&m\in S,\\0&m\notin S,\end{cases} \tag{5.1}
\]

\[
 r_j(S)=
 \begin{cases}
 -2,&j\in S,\\
 -1,&j\notin S\text{ and }m\in S,\\
 0,&j\notin S\text{ and }m\notin S,
 \end{cases}                                           \tag{5.2}
\]

and, for `x in {a,b}`,

\[
 r_x(S)=
 \begin{cases}
 1,&x,m,j\in S,\\
 -1,&x\in S\text{ but not both }m,j\in S,\\
 0,&x\notin S.
 \end{cases}                                           \tag{5.3}
\]

The bound is `M=2`.  At date zero everybody Continues.  At date one define:

- `X`: `m` and `j` Quit surely; `a,b` Never;
- `Y`: replace only `m` by Never, leaving `j`'s Quit at date one;
- `R`: from `Y`, replace the observer `j` by Never;
- `Q`: from `X`, replace the observer `j` by Never.

Thus `R` is all Never and `Q` has only `m` Quit at date one.  The fork
`X -> Y` has a literal common prefix of reach one through date zero.

### Proposition 5.1 (negative atom with zero target incidence)

The unrestricted semantic pairs are

\[
 U(X)=(-1,-2,0,0),\qquad B(X)=(0,-1,1,1),
 \qquad d(X)=(1,1,1,1),                               \tag{5.4}
\]

\[
 U(Y)=(0,-2,0,0),\qquad B(Y)=(0,0,0,0),
 \qquad d(Y)=(0,2,0,0),                               \tag{5.5}
\]

\[
 U(R)=B(R)=(0,0,0,0),\qquad d(R)=0.                  \tag{5.6}
\]

In particular the mover gains one, while the observer debt rises by one:

\[
 U_m(Y)-U_m(X)=1,\qquad d_j(Y)-d_j(X)=1.             \tag{5.7}
\]

The observer's common response `Never` is exact at `R`, with zero debt.  For
the terminal `T={m}`,

\[
 \mu^R(T)=0,\qquad \mu^Q(T)=1,\qquad r_j(T)=-1,    \tag{5.8}
\]

so the target-first rectangle atom is

\[
 (\mu^R(T)-\mu^Q(T))r_j(T)=(0-1)(-1)=1.             \tag{5.9}
\]

Nevertheless the low-debt target has zero finite incidence for `j`.
Against the cap `B(R)=0`, all Continue is the unique exact product root.

#### Proof

At `X`, players `m` and `j` can respectively improve from `-1` to `0` and
from `-2` to `-1` by Never.  Each of `a,b` can join the date-one `{m,j}`
coalition and obtain one instead of zero.  No behavioral mixture exceeds
these deterministic extrema, proving (5.4).  At `Y`, `j` improves from `-2`
to zero by Never; all other players obtain zero and any coalition they can
join without both `m` and `j` pays them at most zero.  This proves (5.5).
At all Never, every unilateral finite Quit gives a negative singleton payoff,
so (5.6) follows.

For the root claim, `j` strictly prefers Continue to Quit against every
opponent product law: Continue pays between `-1` and `0`, while Quit pays
`-2`.  Player `m` also strictly prefers Continue, with payoff zero versus
`-1`.  Once `m` Continues surely, each of `a,b` receives zero by Continue and
`-1` by Quit, since its positive reward requires both `m` and `j` in the same
coalition.  Hence every exact root is all Continue.  Equations (5.8)--(5.9)
are immediate from the deterministic stopping laws.  `QED`

This table is deliberately not a positive-minimum counterexample: `R` is an
exact zero-debt terminal profile, so its global minimum is zero and there is
no positive terminal exploitability witness.  Its exact scope is narrower
and sufficient:

```text
full-debt source
+ literal common-prefix mover fork and positive observer debt rise
+ exact zero-debt common response endpoint
+ positive signed rectangle atom
+ unique all-Continue target cap root
does not imply any positive incidence in the low-debt target law.
```

The global singleton moat does not repair the sign algebra by itself.  It
controls `B_j-r_j({j})`; the selected negative atom here is at the different
terminal `{m}`.  A maintained positive-minimum proof may rule out the whole
table by other global data, but it still needs such a datum explicitly.  It
cannot silently reorient the negative atom from `Q` to `R`.

## 6. What this does and does not consume

The result genuinely improves the endpoint bookkeeping:

- the fresh-root alternative is literal and uniformly charged, not a root
  selected only after compactification;
- the minimum-fibre positive-incidence branch enters the checked
  reset-rigid chamber with the correct retained law, and in the actual hard
  residual positive incidence is automatic rather than sign-selected;
- failure leaves a precise pair of inert selectors, the exact signed atom,
  and the disjunction `off minimum or zero target incidence`;
- a root born only at the limiting cap is distinguished from a root usable
  at the actual source endpoints; and
- the atom's target/sibling orientation and constants are explicit.

It does **not** prove that Alternative C is renewable, that a reset-rigid
return has a decreasing finite rank, or that the semantic minimizer in
Alternative I retains the atom law.  The sign-specific strategic consumers
in the existing orientation compiler also remain available and should not be
discarded: in particular, the negative-reward branch has persistent sibling
mass and its source-row atomic dispatch, while the observer-singleton branch
has its static toggle/deletion dispatch.

## 7. Source and duplicate audit

Declarations inspected narrowly:

- `QuittingStoppingLawVanishingDebtRectangleSequence` in
  `StoppingLaw/OffDiagonal/AtomRectangleSequenceAlternative.lean`;
- `QuittingStoppingLawRectangleResetFaceDispatch`,
  `QuittingStoppingLawRectangleJointAtomLimit`,
  `nonempty_resetFaceDispatch`, `nonempty_jointAtomLimit`,
  `endpoint_opponentIncidence_pos`, `exists_fixedLawResetDispatch`, and
  `nonempty_minimizerBridge` in
  `StoppingLaw/Endpoint/RectangleResetFaceMinimizer.lean`;
- `positive_quittingTerminalPayoffDifferenceAtom_iff_signedMassPolarity` in
  `StoppingLaw/StaticStrategicOrientation.lean`;
- `negativeTarget_sourceMassLower` and the source-row negative atomic
  dispatcher in `StoppingLaw/NegativeTargetAtomicDispatch.lean`;
- `exists_positive_finiteLawAtom_of_finFourHardResidual_minimum` in
  `TerminalSemanticFinFourMinimumLawFiniteAtom.lean`;
- `terminal_eq_singleton_of_totalOpponentIncidence_eq_zero_of_mass_pos` in
  `LawTightCapNashStrictMinimum.lean`;
- `terminalSemanticLaw_singletonNever_zeroDebt_cap_eq_singletonReward` in
  `TerminalSemanticSingletonNeverCapTightness.lean`;
- `minimumTerminalSemantic_singletonMargin` in
  `TerminalSemanticAuxiliaryNashBudget.lean`;
- `quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash` and
  the law-carrier prefix closure through the law-tight saturation imports;
- `quittingTerminalPayoffDifferenceAtom_literalRootStack` in
  `StoppingLaw/ContinuePrefixAtomAccess.lean`;
- `IsQuittingLawTightCapNashSaturationMinimum` and
  `quittingLawTightCapNashSaturationMinimumFace_rootNash_iff_allContinue` in
  `LawTightCapNashMinimumFace.lean`; and
- `QuittingLawTightResetRigidChamber` and
  `exists_quittingLawTightResetRigidChamber` in
  `LawTightCapNashStrictMinimum.lean`.

The static six-cell orientation table is not new; it is already synthesized
in `CODEX_MINER__SIGNED_CAUSAL_RECTANGLE_ORIENTATION_COMPILER_BOUNDARY.md`.
The earlier local double-inert cap/law regression in
[`CODEX_RAMSEY__FIN4_DOUBLE_INERT_LAW_BRIDGE_PLATEAU_SEPARATION.md`](CODEX_RAMSEY__FIN4_DOUBLE_INERT_LAW_BRIDGE_PLATEAU_SEPARATION.md)
concerns a different singleton repair producer and a retained owner-leave
toggle.  Proposition 5.1 here isolates the specific **negative rectangle
orientation at a vanishing-debt response endpoint**.

No Lean, fable, feedback, question, or export file was edited.

## 8. One next question

The remaining source-level question is now exact:

> In Alternative I with `D_*<D_z`, can the hard-residual provenance convert
> either the fixed-law premium or the negative sibling-mass passport into an
> exact root/block at the literal caps `B(R_n)` with absorption bounded away
> from zero, or into a same-law minimum-fibre return?  Equivalently, what
> additional retained field excludes the coexistence of `a_n->0`, a positive
> signed suffix atom, and loss of the atom law at the reset-face minimizer?

Lower semicontinuity of the exact Nash-root correspondence cannot be assumed;
the born-at-limit subcase above is the precise topological reason.
