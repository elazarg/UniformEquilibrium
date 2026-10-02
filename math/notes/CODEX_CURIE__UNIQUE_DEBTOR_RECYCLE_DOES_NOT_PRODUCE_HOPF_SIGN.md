# Unique-debtor recycling does not produce the induced-owner HOPF sign

## Status

This is an internal source audit, not a new consumer and not a Lean claim.
The reviewed unique-debtor recursion reaches a sharp conditional chamber, but
does not manufacture the scalar sign needed by the checked induced-owner HOPF
compiler.  The missing sign is an average over an induced Nash law; the
forced-pair and one-debtor fields control neither that law nor the other terms
in the average.

The exact local failure is independently exhibited in
[`CODEX_RIEMANN__FORCED_PAIR_TO_INDUCED_OWNER_HOPF_ADAPTER.md`](CODEX_RIEMANN__FORCED_PAIR_TO_INDUCED_OWNER_HOPF_ADAPTER.md).
Its regression has global minimum zero, so it is an interface fence rather
than a refutation of a genuinely positive-minimum adapter.

## 1. Input and reviewed recursion

The input is the codimension-one carrier produced in Section 10 of
[`CODEX_EULER__FIN4_CODIMENSION_ONE_PASSPORT_PAIRBASE_ALIGNMENT.md`](CODEX_EULER__FIN4_CODIMENSION_ONE_PASSPORT_PAIRBASE_ALIGNMENT.md):
one player (e) is the only possible debtor, its debt is bounded below, and
its prescribed payoff initially lies strictly below its singleton reward.

The reviewed recursion in
[`CODEX_RAMSEY__UNIQUE_DEBTOR_FLOOR_ENTRANCE_AND_SOLO_RECYCLE.md`](CODEX_RAMSEY__UNIQUE_DEBTOR_FLOOR_ENTRANCE_AND_SOLO_RECYCLE.md)
does two things.

1. While (U_e<\chi_e), exact roots have a quantitative opponent-absorption
   floor.  Prefixing contracts the unique debt until the punishment floor is
   entered, unless the orbit approaches the tight boundary

   \[
   U_e=\chi_e=r_e(\{e\}).
   \tag{1}
   \]

2. From a floor-safe unique-debtor carrier it gives a floor-preserving strict
   debt descent, a uniform-equilibrium payoff, or a positive-debt
   all-Continue stall.  In the nonterminal infinite solo-root arm, either
   absorption charge is nonsummable and the punishment-floor compiler gives a
   uniform payoff, or the roots converge to all Continue at a carrier still
   satisfying (1).

Thus the recursion's honest terminal obstruction is a floor-safe
all-Continue carrier with one positive debtor.  It does not select an induced
Nash distribution on the other three players.

## 2. Exact HOPF gate at the stall

Fix a prospective owner (h), and take the maximal free set

\[
F=I\setminus\{h\}.
\]

The outsider condition in `QuittingInducedOwnerNeverChamber` is then
vacuous.  Let \(\pi\) be a mixed Nash point of the finite induced game in
which (h) is held at Quit, and let \(\mu_\pi\) be its product law on
subsets of (F).  Put

\[
g_h(\varnothing)=r_h(\{h\}),
\qquad
g_h(T)=r_h(T\cup\{h\})-r_h(T)quad(T\ne\varnothing).
\]

Direct expansion gives the exact owner sign

\[
\boxed{
Q_h(\pi)-C_h(\pi)
=\sum_{T\subseteq F}\mu_\pi(T)g_h(T).}
\tag{2}
\]

Together with (r_h(\{h\})\le0), the existence of one induced Nash point
with nonnegative right-hand side is sufficient for the checked HOPF
all-behavior terminal-Nash compiler.

The unique-debtor recursion supplies neither part:

* tightness (1) compares the singleton reward with the punishment value and
  the carrier prescribed payoff; it does not determine the absolute sign of
  (r_e(\{e\}));
* exact roots selected during the recursion are roots against a carrier
  continuation vector, not Nash points of the induced finite game with the
  owner held at Quit; and
* opponent-absorption and summability estimates do not determine the product
  law \(\mu_\pi\) or the weighted sum (2).

Accordingly the recursion gives no source-produced implication

\[
\text{unique-debtor all-Continue stall}
\Longrightarrow
\exists\pi\in\operatorname{Nash}(\Gamma_h),\quad Q_h(\pi)\ge C_h(\pi).
\tag{3}
\]

## 3. Why the forced pair does not fill the gap

For the natural forced-pair owner (h) and singleton owner (j), the hard
source supplies one positive membership term

\[
g_h(\{j\})>0.
\tag{4}
\]

Equation (2), however, averages all eight backgrounds in
(F=\operatorname{Fin}4\setminus\{h\}).  The packet gives no lower bound on
(\mu_\pi(\{j\})), no signs on the other seven (g_h(T)), and no transport
identity from the minimum joint law to an induced Nash law.  Thus (4) is one
positive summand, not the HOPF sign.

Riemann's complete rational regression makes this logical separation exact:
it has a literal forced pair, a distinct paid player, a positive common
response square, (r_h(\{h\})<0), and yet the unique induced Nash point is
all Continue with

\[
Q_h-C_h<0.
\]

The same table has all Never as an exact equilibrium, hence (D_*=0).  It
does not refute (3) with the full positive-minimum premise; it proves that a
proof of (3) must use that premise through an additional global relation, not
through the current one-debtor or forced-pair fields.

## 4. Disposition

The one-debtor/HOPF lane has reached the following sharp status:

\[
\boxed{
\begin{array}{c}
\text{strict floor deficit}\Rightarrow
\text{quantitative contraction},\\
\text{nonsummable solo recycling}\Rightarrow\text{uniform payoff},\\
\text{otherwise}\Rightarrow
\text{floor-tight all-Continue stall};
\end{array}}
\]

but the last stall yields only the conditional HOPF chamber

\[
r_h(\{h\})\le0
\quad\text{and}\quad
\exists\pi\in\operatorname{Nash}(\Gamma_h),\ Q_h(\pi)\ge C_h(\pi).
\tag{5}
\]

Neither inequality in (5) is produced.  A further attack on this lane must
derive an incidence relation between the positive-minimum source law and an
induced Nash law, or prove that the uniform owner-unsafe margin over the whole
induced Nash correspondence is incompatible with positive global minimum.
Another exact-root contraction estimate or another singleton join label
cannot decide (2).

## Sources inspected

* `notes/CODEX_RAMSEY__UNIQUE_DEBTOR_FLOOR_ENTRANCE_AND_SOLO_RECYCLE.md`;
* `notes/CODEX_EULER__FIN4_CODIMENSION_ONE_PASSPORT_PAIRBASE_ALIGNMENT.md`;
* `notes/CODEX_RIEMANN__FORCED_PAIR_TO_INDUCED_OWNER_HOPF_ADAPTER.md`;
* `Research/Quitting/HopfCompletionSafeChambers.lean`;
* `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourSoloWallDispatch.lean`.

