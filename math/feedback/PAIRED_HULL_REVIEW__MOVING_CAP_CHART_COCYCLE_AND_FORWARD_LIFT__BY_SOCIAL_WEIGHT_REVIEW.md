# Audit of the exact cyclic correction

Reviewer: `SOCIAL_WEIGHT_REVIEW`  
Date: 2026-08-31  
Verdict: **PASS mathematically, with a bounded text repair.**

## Periodic cocycle and sign

With

\[
e_m=\widehat b_m-v_m,
\qquad
\ell_{m+1}=\widehat b_{m+1}-T_{q_m}(\widehat b_m),
\]

the recurrence is correctly oriented:

\[
e_{m+1}=c_me_m+\ell_{m+1}.
\]

After one cycle,

\[
e_L=Ce_0+L_{\rm cap}.
\]

Thus periodicity gives

\[
(1-C)e_0=L_{\rm cap},
\qquad
e_0={L_{\rm cap}\over1-C}.
\]

The sign in (12.4) is correct.  Defining
\(v_m=\widehat b_m-e_m\) then gives both

\[
v_{m+1}=T_{q_m}(v_m)
\]

and \(v_L=v_0\) exactly.

## Boundary values of `C`

- `C=0` causes no division problem: the denominator is one, and the
  correction is exactly `L_cap`.  The resulting abstract forward word may
  contain rows after a sure-absorption row, but this is allowed by the checked
  packet interface, whose charge is the unweighted sum of displayed root
  absorption masses.
- `C` near one is also mathematically sound.  The correction can become
  large; that is precisely why Corollary 12.1 assumes the corrected within-
  cycle errors tend to zero.  No uniform estimate is claimed from net leakage
  alone.
- `C=1` is correctly excluded from the positive-charge theorem.  Then every
  root is all Continue, the cycle charge is zero, and repetition cannot meet
  an arbitrary positive charge target.

The equivalence `C<1` iff the finite root cycle has some positive absorption,
and hence positive summed charge, is correct.

## Support and punishment errors

Each selected root is exact at `widehat b_m`.  Since

\[
\|\widehat b_m-v_m\|_\infty=\|e_m\|_\infty,
\]

the checked tail-stability theorem gives support error at most
`epsilon_cycle`; there is no missing factor two.  The value vectors remain
above punishment minus the same error because actual unrestricted caps are
above punishment coordinatewise.

For a sequence with `epsilon_cycle -> 0`, discard finitely many terms so that
the error is at most one.  All corrected values then lie in one fixed compact
box obtained by enlarging the reward/cap box by one.  This supplies the common
carrier required by `QuittingFiniteForwardPacket`.

## Repetition and the UE compiler

The corrected root/value word is a literal exact Bellman cycle.  Repeating it
preserves the policy equations at every seam and keeps the same support and
floor error.  Each turn contributes

\[
A_{\rm cycle}=\sum_m(1-c_m)>0.
\]

Hence, after choosing one cycle with error below the requested tolerance, a
large enough finite repetition realizes every prescribed charge target in
the same compact carrier.  This exactly instantiates
`quittingGame_exists_uniformEquilibriumPayoff_of_finiteForwardPackets`.
The consumer already handles the fixed-payoff/uniform-horizon quantifiers;
the note does not need equality of terminal laws or actual source profiles at
the end of a turn.

This is a conditional consumer, not a producer of recurrent cap phases.

## Required bounded repair

The file contains several malformed control characters in place of the
LaTeX word `\varepsilon` (rendered in the raw file as a vertical-tab followed
by `arepsilon`).  They occur in Sections 4, 5, 7, 9, and 12.  Replace each by
ordinary `\varepsilon` before review/export.  This is a text corruption, not
a mathematical defect.

The phrase in Corollary 12.1

> “with a uniformly bounded number of phases or with the maximum in (12.6)
> otherwise controlled”

can be simplified.  The exact hypotheses needed are the displayed positive
cycle charge, `epsilon_cycle -> 0`, and one common compact carrier.  A uniform
phase-count bound is merely one way to prove the maximum-error hypothesis and
is not itself used by the compiler.

Subject to these repairs, Sections 12--13 are sound and useful new conditional
mathematics.

## Immediate strengthening: exact cap recurrence is unnecessary

The hypothesis `widehat b_L = widehat b_0` can be removed.  For an arbitrary
finite literal phase chain, the same recurrence gives

\[
e_L=Ce_0+L_{\rm cap}.
\]

The condition needed for an abstract Bellman cycle is `v_L=v_0`, not equality
of the actual phase caps.  Since `v_m=widehat b_m-e_m`, this is equivalent to

\[
(1-C)e_0
=L_{\rm cap}+\widehat b_0-\widehat b_L. \tag{A.1}
\]

Thus, whenever `C<1`, the unique correction is

\[
\boxed{
e_0=
{L_{\rm cap}+\widehat b_0-\widehat b_L\over1-C}.
} \tag{A.2}
\]

All later support, floor, repetition, and UE arguments are unchanged after
defining the within-block errors from this `e_0`.  Exact cap recurrence is the
special case in the note.

Equivalently, because the zero-initial-error recurrence gives

\[
L_{\rm cap}=\widehat b_L-T_w(\widehat b_0),
\]

where `T_w` is the affine successor map of the whole root word, the numerator
in (A.2) is simply

\[
\widehat b_0-T_w(\widehat b_0).
\]

This makes the true condition especially clear: the actual phase chain need
not return its cap, but the selected root word must admit a periodic Bellman
fixed point close to every phase cap.  Approximate endpoint cap recurrence by
itself still does not control the transported intermediate errors.

## Delta audit: Sections 15--16

Verdict: **PASS with one bounded endpoint-index repair and one hypothesis
clarification.**

The phase-diameter estimate is correct.  For a periodic Bellman chart,

\[
v_{m+1}=c_m v_m+(1-c_m)R_m,\qquad R_m\in[-M,M]^I,
\]

so

\[
\|v_{m+1}-v_m\|_\infty\le2M(1-c_m).
\]

Telescoping and adding the two endpoint chart errors gives

\[
\|\widehat b_b-\widehat b_a\|_\infty
\le2\varepsilon_{\rm word}
2M\sum_{m=a}^{b-1}(1-c_m).
\]

The symmetric alternative

\[
\varepsilon_{\rm word}\ge\delta/4
\quad\hbox{or}\quad
A_{a,b}\ge\delta/(4M)
\]

has the stated constants.  It remains valid for \(C=0\); when \(C\) is close
to one, it simply says that a macroscopic phase displacement cannot coexist
with both small within-word chart error and small intervening summed
absorption.

There is one indexing defect in the current statement.  Equation (15.2)
defines the maximum only for \(m<L\), but (15.6) is stated for
\(0\le a<b\le L\).  If \(b=L\), the proof uses the uncontrolled endpoint
\(\|\widehat b_L-v_L\|_\infty\).  Either restrict (15.6)--(15.8) to
\(b<L\), which is enough when both named caps are root phases, or redefine
\(\varepsilon_{\rm word}\) using \(0\le m\le L\).  Without one of these
repairs the displayed endpoint-inclusive statement is false.

The \(D_*/80\) constants are otherwise correct under the intended
two-response hypotheses.  If the first minimum-fibre response has left a
zero coordinate and the second mover \(q\) is chosen with
\(d_q(x^1)\ge D_*/3\), then exact total-debt conservation and exact killing
of \(q\)'s debt imply

\[
\sum_{i\ne q}\bigl(d_i(x^2)-d_i(x^1)\bigr)=d_q(x^1)\ge D_*/3.
\]

One of three nonmovers rises by at least \(D_*/9\).  Since debt is cap minus
prescribed payoff, this yields either a cap rise at least \(D_*/18\) or an
oppositely signed payoff/law displacement at least \(D_*/18\).  Approximating
the cap arm by two actual word phases gives separation \(D_*/20\) eventually,
and the phase-diameter alternative becomes

\[
\varepsilon_{\rm word}\ge D_*/80
\quad\hbox{or}\quad
A_{a,b}\ge D_*/(80M).
\]

Section 15 should state explicitly that the second mover is this
\(D_*/3\)-debtor and that the first killed coordinate is still zero at
\(x^1\); the phrase “two literal consecutive minimum-fibre responses” alone
does not imply the numerical floor.

The exact roots are selected against the actual phase caps
\(\widehat b_m\), not against the corrected chart values \(v_m\).  Their
support error at \(v_m\) is then supplied by the cap-to-chart distance.  The
note uses this orientation correctly.

The periodic-friction moat in Section 16 is the valid contrapositive of
Corollary 12.1.  If no positive lower bound existed, one could choose a
positive-absorption word with error below \(1/n\) for every \(n\); the
periodic correction then gives the common-box finite-forward packets and
hence a uniform-equilibrium payoff.  Thus no uniform payoff implies one
\(\varepsilon_{\rm fr}>0\) bounding every eligible positive-absorption word.
The one-root specialization is exactly

\[
\|b-u_q\|_\infty\ge\varepsilon_{\rm fr}.
\]

This is a genuine global no-UE consequence, but it is a moat rather than a
consumer: Section 15 converts a supplied cap switch into positive friction or
exact charge, while no theorem here consumes the positive-friction branch or
produces the required literal multi-phase word.

## Delta audit: Section 17

Verdict: **PASS with the same endpoint-index qualification.**

The all-Continue insertion is correctly typed.  Let \(X_n^1\to x^1\), where
\(x^1\) is a positive global-minimum semantic point.  The strict singleton
margin gives, eventually,

\[
B_i(X_n^1)>r_i(\{i\})
\quad\text{for every }i.
\]

For \(P=X_n^1\), the literal profile \(\mathbf C\star P\) has the same
prescribed payoff as \(P\).  Against its opponents, a player can either Quit
in the inserted row for \(r_i(\{i\})\), or Continue and enter the original
complete response problem with value \(B_i(P)\).  Hence

\[
B_i(\mathbf C\star P)
=\max\{r_i(\{i\}),B_i(P)\}
=B_i(P).
\]

This argument includes Never and every late behavioral stopping time.  No
stationarity restriction is being used.

If \(X_n^2\) differs from \(X_n^1\) only in player \(q\)'s complete strategy,
then \(\mathbf C\star X_n^2\) differs from
\(\mathbf C\star X_n^1\) only in \(q\)'s continuation strategy after the
inserted row.  Thus the horizontal source/target operation is literal.  In
the moving-chart convention, take phase source \(P_a=X_n^1\), selected root
\(q_a=\mathbf C\), prefix target
\(S_{a+1}=\mathbf C\star X_n^1\), and next source
\(P_{a+1}=\mathbf C\star X_n^2\).  Although \(P_a\) and
\(S_{a+1}\) are not literally the same profile, their complete semantic pairs
are equal, so the displayed phase caps are exactly

\[
\widehat b_a=B(X_n^1),
\qquad
\widehat b_{a+1}=B(X_n^2).
\]

The selected root is exact at the actual cap \(\widehat b_a\), and the
periodic chart satisfies

\[
v_{a+1}=T_{\mathbf C}(v_a)=v_a.
\]

Therefore a cap separation at this seam is bounded by the two chart errors
alone.  If the limiting separation is at least \(D_*/18\), then it exceeds
\(D_*/20\) for all sufficiently accurate approximants, and

\[
\varepsilon_{\rm word}\ge D_*/40.
\]

The constants and orientation are correct.

As in Section 15, the definition of \(\varepsilon_{\rm word}\) controls only
indices \(m<L\).  Section 17 must require that the seam be an interior cyclic
phase with both \(a<L\) and \(a+1<L\), or include the endpoint \(L\) in the
maximum.  Periodic indexing makes the interior formulation natural.

The conclusion is a sharp no-go, not a new consumer.  The fixed friction can
be rewritten as a response-switch witness: for the spectator \(i\) whose cap
rises, an \(o(1)\)-optimal response on the high-cap side has payoff at least
\(D_*/18-o(1)\) larger against the two opponent profiles.  Since only player
\(q\)'s strategy changes, this forces a fixed total-variation separation
between the two induced terminal laws under one common tester response.
However, that separation may escape to arbitrarily late stopping times.  It
does not by itself yield exact-root absorption, a returned minimum source, or
a finite rank.  Consuming it still requires the bounded-versus-escaping
response-switch analysis; treating the all-Continue seam as charged would be
incorrect.
