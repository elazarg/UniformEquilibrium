# Independent review of `FIN4_MINIMAL_PASSPORT_DOUBLE_INERT_LAW_BRIDGE`

**Reviewer:** CODEX_EULER  
**Date:** 2026-08-25  
**Verdict:** **PASS mathematically; keep internal rather than export.**

I checked Propositions 3.1--3.3 and the rational regression in Proposition
5.1 against the cited singleton-source/repair declarations and against the
current Fin4 question.  I found no mathematical defect.  There is one trivial
presentation repair: Section 5 repeats the beginning of rule 2 verbatim; one
copy should be deleted.  This does not affect the table definition.

## 1. Claim reviewed

For a checked `FinFourSingletonBaseResetRepairPaidChain`, with sure singleton
owner (e), free set (F), free one-row Bernoulli weights (w(A)), and free
absorption (a=1-w(\varnothing)>0), the note claims:

1. the original source law and literal owner-repair law obey the exact affine
   pushforward identity

   \[
   \mu_{\rm src}=(1-a)\delta_{\{e\}}+
      a(A\mapsto A\cup\{e\})_*\mu_{\rm rep};
   \]

2. the repaired law has a nonempty atom of mass at least
   (\Gamma/(28M)) carrying a gain-aligned half-gap, hence either an owner
   solo comparison or an owner-leave comparison of size at least
   (\Gamma/2);
3. the repaired free restriction is not the deletion equilibrium supplied by
   cardinal minimality, because it retains a full-gap unrestricted deviation;
4. a rational Fin4 table simultaneously realizes all four separately sourced
   operational deletion passports and a floor-safe pair-base profile whose
   cap-tail product Nash root is uniquely all-Continue, while escaping the
   counterexample residual through exact date-zero singleton equilibria.

## 2. Exact law bridge: PASS

In the original root, (e) Quits surely at date zero.  Therefore the free
Bernoulli subset (A\subseteq F) produces (A\cup\{e\}) with probability
(w(A)), including (A=\varnothing).  There is no Never mass.

After the literal repair, (e) Continues surely and the same free product row
is repeated.  The checked `free_absorption_lower` gives

\[
a\ge {\Gamma\over\Gamma+2M}>0.
\]

Thus a fixed nonempty (A) first occurs with total probability

\[
\sum_{t\ge0}w(\varnothing)^t w(A)={w(A)\over a}.
\]

This proves all displayed masses and the measure identity.  It also verifies
the claimed mutual singularity: source coalitions contain (e), repaired
coalitions exclude (e).  The statement is a pushforward relation, not an
incorrect assertion that the two laws are equal.

The identity is literal same-point data: the repair theorem keeps the induced
free Nash point and changes only the owner's strategy to Always Continue.
No source reselection occurs in Proposition 3.1.

## 3. The `Gamma/(28M)` extraction: PASS

The checked source producer gives owner debt at least (\Gamma), and
`repaired_owner_payoff_eq_source_cap` identifies the repaired owner's payoff
with the source stationary cap.  Consequently

\[
U_e(\mathrm{rep})-U_e(\mathrm{src})\ge\Gamma.
\]

Substitution of the law bridge gives

\[
\mathbb E_{\mu_{\rm rep}}g(A)\ge\Gamma,
\quad
g(A)=r_e(A)-(1-a)r_e(\{e\})-a r_e(A\cup\{e\}).
\]

The reward bound implies (g(A)\le2M).  With
(H=\{A:g(A)\ge\Gamma/2\}) and (h=\mu_{\rm rep}(H)),

\[
\Gamma\le2Mh+(1-h){\Gamma\over2}
\]

implies

\[
h\ge {\Gamma\over4M-\Gamma}\ge {\Gamma\over4M}.
\]

Here (0<\Gamma\le2M), so all denominators and comparisons have the stated
orientation.  Since a three-player free set has seven nonempty subsets, one
atom has mass at least (\Gamma/(28M)).

Finally,

\[
g(A)=(1-a)(r_e(A)-r_e(\{e\}))+
      a(r_e(A)-r_e(A\cup\{e\}))
\]

is a convex combination, including the endpoint (a=1).  Hence
(g(A)\ge\Gamma/2) forces at least one of the two displayed differences to
be at least (\Gamma/2).  The alternatives are inclusive.  The note properly
does not identify this atom with the producer's pre-existing heavy atom.

## 4. Deletion-equilibrium nonidentification: PASS

The repair owner is literal Always Continue.  Removing that coordinate
therefore preserves the stopping law and every free player's payoff before
and after any unilateral free-player deviation.  The repair handoff's
`outside_debt` supplies a free player whose unrestricted stationary cap minus
the repaired prescribed payoff is at least (\Gamma).  Under exact
deletion/lift naturality this becomes

\[
\sup_{\sigma_f}
 \bigl(U_f(\tau_{\rm rep}[f\leftarrow\sigma_f])-
       U_f(\tau_{\rm rep})\bigr)\ge\Gamma
\]

in the owner-deleted game.  Attainment of the supremum is not claimed or
needed.  Thus the repaired restriction cannot be a terminal
(\varepsilon)-Nash profile for (\varepsilon<\Gamma).  This is exactly the
source mismatch that prevents direct use of the operational deletion
passport.

## 5. Rational simultaneous-passport regression: PASS

I recomputed the table in Proposition 5.1.

Let (o(j)=j+2\pmod4).  For a deleted (d), choose (j=o(d)) and let (j)
Quit at date one in the retained triple.  Player (j) obtains (1); Never
obtains (0).  Each other retained player obtains (2); preempting gives
(1), tying gives (1), and waiting/Never gives (2).  Pure-time
disintegration therefore gives unrestricted exact Nash.  In the quiet lift,
the deleted player receives (0) from singleton (j) and gains exactly one
by quitting at date zero.  This works for all four deleted labels.

At the pair-base profile ({0,1}), the payoff, cap, and debt vectors are

\[
U=(1,1,2,2),\qquad B=(2,2,2,2),\qquad d=(1,1,0,0).
\]

The owner-0 Never deviation is the claimed paid gain one; reset owner 2 has
zero debt and unit incidence.  A sure opposite singleton gives every player
a punishment cap at most zero, so the displayed source is floor safe.

At cap tail (B), for every player and every pure opponent corner, Quit pays
exactly one less than Continue: on the empty opponent corner this is
(1<2), and on nonempty (A) it is the defining identity
(r_i(A\cup\{i\})=r_i(A)-1).  Affine averaging proves that every product
root with positive Quit probability violates complementarity.  Hence
all-Continue is the unique product Nash root.

At a date-zero singleton ({j}), the owner gets (1), its opposite gets
(0), and the other outsiders get (2).  The only possible unilateral
action before absorption is the date-zero tie: it pays respectively (-1)
to the opposite and (1) to the other outsiders.  The active owner gets at
most (1).  Thus the singleton profile is exact Nash against arbitrary
behavioral deviations.  This correctly makes the global minimum debt zero
and pinpoints the missing hard-residual field.

The sharp-passport calculation also checks:

\[
\ell_d(I\setminus\{d\})=0,\qquad P_d=1,\qquad C_d=0.
\]

Thus the regression is an exact interface countermodel, not a conjecture
counterexample.

## 6. Source and novelty audit

The law identity is not stated by the checked source/repair declarations I
inspected.  Their comments correctly avoid equality of the laws, but the
affine pushforward relation follows from the literal same-point root and is
strictly more informative than mere nonidentification.  The gain-aligned
(\Gamma/(28M)) atom is likewise not the producer's existing heavy atom.

The result does narrow the **description** of the double-inert arm: its two
stationary laws are explicitly coupled and the repaired law contains one
quantitative half-gap atom.  It does not eliminate that arm, enter a checked
Bellman/chronology compiler, produce a return, or decrease a maintained
finite/debt rank.  Proposition 3.3 simultaneously proves that the most obvious
deletion-equilibrium consumer is unavailable.

Accordingly I do **not** recommend an export packet under the current
`exports/README.md` importance/consumer gate.  Keep the result internal as a
precise same-source obstruction and as the finite target for a future
three-player Nash-correspondence connector.  If the project explicitly
authorizes source-alignment packets independent of a consumer, Propositions
3.1--3.2 are mathematically clean enough for such a narrowly labeled packet,
but that would be a policy exception rather than a conjecture-facing chamber
closure.

## 7. Exact nonclaims retained

The reviewed argument does not establish:

* equality of the source and repaired laws;
* a common atom with the earlier producer-selected heavy atom;
* an exact Bellman edge or reached return from the unilateral repair;
* identification with a cardinal-minimal deletion equilibrium;
* regeneration at a quantitative cap-descent limit; or
* contradiction of the double-inert arm or the Fin4 conjecture.

