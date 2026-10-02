# Four-deadline cap orbits compress to an early deletion or a singleton-host bubble

Author: CODEX_SPINOZA

## Status

**Exact ordinary mathematics; source-faithful structural reduction, not
Lean-checked and not yet a terminal consumer.**  Once a profile contains two
distinct prescribed finite sure clocks, at most two additional zero- or
positive-gain exact cap installations make all four prescribed laws
deterministic finite clocks.  Thus the fixed-spectator branch of an arbitrarily
selected two-sure orbit is optional: one may work in the all-active
four-deadline class from the outset.

For deterministic deadlines the complete terminal semantic pair is determined
by the weak order of the four deadlines and the single boundary bit recording
whether the first deadline is zero.  Along an unbounded-span sequence, a
divergent ordered gap therefore has only two essential forms.  If at least two
players lie before it, every clock after the gap is universally invisible and
may be changed to Never without changing any prescribed payoff or unrestricted
cap.  If exactly one host lies before it, then either a nonhost has a fixed-gap
best response which moves to the host side and creates the preceding deletion,
or the terminal gap is carried by the host and its exact cap releases it across
the gap into the three-player late bubble.

The latter release is an actual paid edge from the supplied source, but it is
still horizontal rather than Nash--Bellman.  The theorem does not orient
bounded order-type cycles or show that successive bubble releases decrease a
renewable rank.

## 1. Setting

Let \(I=\operatorname{Fin}4\), let every terminal reward lie in
\([-M,M]\), and assume the complete behavioral terminal problem has a fixed
exploitability gap

\[
 \max_{i\in I} d_i(P)\ge \Gamma>0
 \qquad\text{for every actual profile }P.
\tag{1.1}
\]

A deterministic finite clock is a pure time \(T_i\in\mathbb N\).  All caps
and debts below are against the unrestricted behavioral deviation class.

The input two-sure profiles are those produced by the reviewed late-reset and
unique-sure handoff route.  The arguments in Sections 2--5 are independent of
that provenance; source ancestry matters only when an exact response edge is
selected.

## 2. Finite saturation of the two-sure class

### Proposition 2.1 (at most two preparatory installations)

Suppose an actual profile \(P\) has two distinct players \(a,b\) whose
prescribed stopping times are deterministic and finite.  Then there is a
literal list of at most two unilateral exact-cap replacements ending at a
profile \(P^\sharp\) in which all four prescribed stopping times are
deterministic and finite.  The two original clocks remain finite throughout.

The replacements may have zero gain.  Every intermediate and final profile
has at least two distinct finite sure-clock players and has exactly finite
complete unilateral semantics.

### Proof

Against the opponents of any player \(i\), at least one of the two clocks
\(a,b\) remains prescribed: if \(i=a\), clock \(b\) remains; if \(i=b\),
clock \(a\) remains; otherwise both remain.  Let \(H\) bound the two clock
dates.  Every unilateral outcome is therefore decided by \(H\), and every
pure time after \(H\) is outcome-equivalent to Never.  Pure-time extremality
shows that player \(i\)'s complete behavioral cap is the maximum of a finite
list of pure-time values and is attained by a deterministic finite time
(replace a Never maximizer by any sufficiently late finite representative).

Replace each of the at most two players outside \(\{a,b\}\) by such a finite
cap attainer.  An own replacement leaves the other three prescribed laws
unchanged.  Thus previously installed finite clocks remain finite, and after
at most two replacements all four laws are deterministic finite clocks.  The
same retained-clock argument gives exact finite complete semantics at every
intermediate node.  QED.

This proves that an orbit selector may saturate the active set before making
any positive-gap choices.  The fixed-spectator Never cylinder found for a
non-saturated selector is real, but is not an unavoidable residual.

## 3. Exact semantic quotient of a pure-deadline profile

Let \(T=(T_i)_{i\in I}\in\mathbb N^I\).  For a fixed player \(i\), let

\[
 h_i=\min_{j\ne i}T_j,
 \qquad E_i=\{j\ne i:T_j=h_i\}.
\tag{3.1}
\]

Against the three deterministic opponent clocks, a pure deviation by \(i\)
has exactly the following values:

\[
 \begin{array}{c|c}
 t<h_i & r_i(\{i\})\quad\text{(available iff }h_i>0\text{)},\\
 t=h_i & r_i(E_i\cup\{i\}),\\
 t>h_i\text{ or Never} & r_i(E_i).
 \end{array}
\tag{3.2}
\]

Arbitrary behavioral deviations only average these pure-time values.  Hence

\[
 B_i(T)=\max\Bigl(
 \{r_i(E_i\cup\{i\}),r_i(E_i)\}
 \cup \{r_i(\{i\}):h_i>0\}\Bigr).
\tag{3.3}
\]

The prescribed payoff is the reward of the first deadline block.  It follows
that the full pair \((U(T),B(T))\) is determined by:

1. the ordered partition of \(I\) into equal-deadline blocks; and
2. whether the first block occurs at date zero or at a positive date.

All numerical gaps between consecutive occupied dates are semantically
invisible.  In particular, replacing occupied dates

\[
 t_0<t_1<\cdots<t_q
\]

by \(0,1,\ldots,q\) when \(t_0=0\), and by \(1,2,\ldots,q+1\) when
\(t_0>0\), preserves the complete semantic pair exactly.  This is a finite
semantic quotient, not a literal unilateral transition.

Formula (3.3) also gives a canonical finite cap representative: a singleton
maximizer uses date zero when \(h_i>0\), a tie maximizer uses \(h_i\), and a
Continue maximizer uses any finite date after \(h_i\).

## 4. Universal deletion behind a two-player early prefix

Consider a sequence \(T^n\in\mathbb N^I\).  After subselection fix the weak
order of player labels.  Suppose there is an ordered cut

\[
 E\sqcup L=I,
 \qquad
 \max_{e\in E}T^n_e<\min_{\ell\in L}T^n_\ell,
\tag{4.1}
\]

whose gap tends to infinity.  The divergence is not needed for the next exact
claim; strict separation is enough.

### Proposition 4.1 (universal late-block erasure)

If \(|E|\ge2\), replace every clock in \(L\) by Never and call the resulting
profile \(\widehat T^n\).  Then

\[
 \boxed{\operatorname{Sem}(\widehat T^n)=
        \operatorname{Sem}(T^n).}
\tag{4.2}
\]

### Proof

Under prescribed play some member of \(E\) stops strictly before every member
of \(L\).  Fix any unilateral deviator \(i\).  If \(i\in L\), all of \(E\)
remains.  If \(i\in E\), at least one other member of \(E\) remains.  Hence
under every deviation the outcome is decided by a retained clock in \(E\)
strictly before any prescribed clock in \(L\).  The prescribed clocks in
\(L\) are therefore invisible to the prescribed payoff and to every payoff
in every player's complete deviation problem.  Taking suprema proves (4.2).
QED.

Thus an unbounded gap behind two or three early players has an exact
lower-cardinality representative on the same semantic point.  This is much
stronger than weak convergence of the late clocks to Never.

## 5. The singleton-host gap dispatch

Assume now \(E=\{h\}\) in (4.1).  Thus \(h\) stops strictly before the other
three players.  Put \(s_i=r_i(\{i\})\).  For every nonhost \(i\ne h\), the
host remains prescribed under an \(i\)-deviation and stops before the late
block.  Therefore

\[
 U_i(T^n)=r_i(\{h\}),
\tag{5.1}
\]

and

\[
 B_i(T^n)=
 \max\Bigl(
 \{r_i(\{h,i\}),r_i(\{h\})\}
 \cup\{s_i:T^n_h>0\}\Bigr).
\tag{5.2}
\]

These three nonhost debt coordinates are independent of the internal late
three-player clocks and of the size of the gap.

### Proposition 5.1 (paid join or paid host release)

At every singleton-host source \(T^n\), exactly one of the following useful
alternatives is available.

1. **Paid early join.**  Some nonhost \(i\ne h\) has
   \(d_i(T^n)\ge\Gamma\).  Its cap is attained by a pure time on the host
   side: date zero if the singleton value is maximal, or date \(T^n_h\) if
   the tie value is maximal.  Replacing \(i\) by this cap attainer gives an
   actual gain at least \(\Gamma\) and leaves at least two players weakly
   before the old divergent gap.  The remaining late block is then
   universally erasable by Proposition 4.1.

2. **Paid host release.**  Every nonhost debt is below \(\Gamma\).  By (1.1),
   \(d_h(T^n)\ge\Gamma\).  Quitting at any date strictly before the first
   late opponent still gives \(s_h=U_h(T^n)\), so no such time can attain an
   improving cap.  A finite exact cap representative for \(h\) must tie the
   first late opponent block or occur after it.  Replacing \(h\) by that
   representative is a literal source-attached edge of gain at least
   \(\Gamma\) which crosses the whole gap and releases the three-player late
   bubble.

### Proof

The two alternatives are exhaustive by the terminal gap.  In the first arm,
the Continue value in (5.2) equals the prescribed payoff and cannot produce
positive debt.  Every positive cap is therefore attained by the singleton or
tie action specified there.  If the singleton action puts \(i\) strictly
before \(h\), the early side through \(h\) still contains both \(i\) and
\(h\); if it ties \(h\), the first block itself has two members.  Proposition
4.1 applies in either case.

In the second arm, prescribed play gives \(U_h=s_h\).  Every time before the
late block also terminates at the singleton \(\{h\}\), so it gives the same
value and cannot realize the strict cap gain.  Pure-time extremality and the
finite opponent clocks give an exact finite maximizer, necessarily at or
after the first late deadline.  QED.

## 6. Bounded quotient versus deadline escape

After Proposition 2.1 every selected exact-cap orbit can be kept inside the
four-pure-deadline class.  The finite semantic quotient in Section 3 shows
that bounded relative spans have only finitely many literal normalized
representatives.  A recurrent normalized order type, however, is only a
finite horizontal best-response component: the common compression is a
semantic equivalence, not a Nash--Bellman edge or a source-preserving
unilateral update.  The reviewed two-sure response-cycle regression shows
that such recurrence is not itself a terminal consumer.

If relative spans are unbounded, pass to a fixed ordered partition and an
adjacent gap tending to infinity.  Propositions 4.1 and 5.1 give the exact
exhaustive output

\[
 \boxed{
 \begin{array}{c}
 \text{unbounded four-deadline geometry}\\[1mm]
 \Downarrow\\[1mm]
 \text{universal deletion behind at least two early players}\\
 \text{or a paid nonhost join followed by that deletion}\\
 \text{or a source-attached paid release of the unique early host}\\
 \text{into the late three-player bubble.}
 \end{array}}
\tag{6.1}
\]

This is the precise lower-cardinality timing boundary.  It does not assert
that the deleted representative is a new minimum source, nor that the paid
host-release target is a terminal equilibrium or a forward root.

## 7. Consumer audit

The preparatory saturation eliminates the proper-active escaping branch as a
necessary case: it can always be replaced by an all-active selector without
losing exact cap attainment or the two-sure property.

The two unconsumed cases are now sharper.

1. A bounded normalized response component is finite only at the level of
   semantic order types.  The simultaneous calendar compression between
   representatives is not an executable edge, and a positive-gain finite
   best-response cycle need not be a Nash--Bellman cycle.
2. A singleton-host release is an exact paid edge whose target activates an
   actual three-player late bubble.  The three-player uniform-payoff theorem
   does not by itself control the releasing host's unrestricted cap or lift a
   terminal profile back to the four-player source.  This is the exact
   cardinal adapter still missing.

In particular, the theorem uses the positive terminal gap essentially to
force a paid early join or host release, but it does not convert that payment
into vertical Bellman charge.

## Sources inspected

- notes/CODEX_SPINOZA__TWO_SURE_CAP_ORBIT_ACTIVE_SET_AND_ESCAPING_CUT_RECENTERING.md;
- notes/CODEX_HAHN__TWO_RENEWED_SURE_CLOCKS_GIVE_FINITE_COMPLETE_SEMANTICS.md;
- notes/CODEX_GROMOV__TWO_SURE_CLOCK_FINITE_RESPONSE_CYCLE_NOGO.md;
- notes/CODEX_HAHN__MOVE_TO_FRONT_EXACT_PREFIX_CAP_CYCLE_REGRESSION.md;
- formalized/PURE_FINITE_CLOCK_MINIMUM_DEADLINE_RANK_TO_PAID_PORT.md;
- formalized/FINITE_DEADLINE_NASH_PROJECTIVE_BOUNDARY_AND_COMPATIBILITY.md;
- UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/FiniteClockCanonicalization.lean;
- UniformEquilibrium/Diagnostics/Quitting/TwoSureProductRootTailScreen.lean; and
- UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean.

## Boundary and nonclaims

- A zero-gain preparatory cap installation is allowed because the cap is
  attained; it is not called a paid edge.
- Semantic compression preserves \((U,B)\), not the literal terminal-law date
  labels and not source ancestry.
- Proposition 4.1 needs two retained early players.  With one early host, its
  own deviation can expose the whole late bubble, which is why Section 5 is
  separate.
- The lower-cardinality representative still has four strategic players;
  the erased players use Never and retain unrestricted deviation rights.
- No recurrence, renewable rank, exact Nash--Bellman block, terminal
  approximate Nash profile, or uniform-equilibrium payoff is claimed.

## Next exact question

Can the source-attached paid host release be combined with a three-player
uniform profile of the late bubble while preserving the host's cap inequality,
or can the universal early deletion be upgraded from semantic equality to a
minimum-source support contraction?  Either adapter would consume the only
unbounded-span outputs in (6.1).
