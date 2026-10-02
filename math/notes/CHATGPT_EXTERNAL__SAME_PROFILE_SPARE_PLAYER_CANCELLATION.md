# Same-profile spare-player cancellation at a forced (2+2) source

**Author:** external ChatGPT submission  
**Status (2026-08-25):** ordinary-mathematics claim under independent review;
not Lean-checked and not proposed for export.

## Question

Can a fifth player cancel the two positive debt coordinates of one *actual*
five-player pair-base source without reselecting its terminal law or restricting
unilateral deviations?  The proposed answer below is conditional on explicit
endpoint-complementarity, punishment-floor, and scalar budget inequalities.

## Exact statement

Let the finite player set be partitioned

\[
I=B\mathbin{\dot\cup}F\mathbin{\dot\cup}\{s\},
\qquad B=\{b_0,b_1\},\quad F=\{f_0,f_1\}.
\]

Fix an actual behavioral source profile \(\sigma^{\mathrm{src}}\) whose
first-stage Quit
probabilities satisfy

\[
p_{b_0}=p_{b_1}=1,\qquad p_f\in[0,1]\ (f\in F),\qquad p_s=0.
\]

For \(q\in[0,1]\), let \(r^q\) be the product root obtained from that
first-stage root by changing only the spare player's Quit probability from
\(0\) to \(q\).  Define the literal prefixed profile

\[
\widehat\sigma^q:=r^q\triangleright\sigma^{\mathrm{src}}.
\]

Thus the four original first-stage laws are unchanged and the actual
continuation after an all-Continue outcome is \(\sigma^{\mathrm{src}}\).
That continuation is never reached because both members of \(B\) Quit surely.
The profile \(\widehat\sigma^0\) need not be definitionally equal to
\(\sigma^{\mathrm{src}}\), but the two have exactly the same terminal outcome
law and unrestricted terminal-semantic pair: both absorb at their displayed
first stage, and after any unilateral deviation one sure base quitter remains.
Below, \(D_0\) may therefore be computed from either profile.

For \(i\ne s\) and \(\eta\in\{0,1\}\), let \(C_i^\eta,Q_i^\eta\) be player
\(i\)'s expected first-stage payoff when \(i\) respectively Continues or
Quits, with the other original action laws fixed and the spare fixed to
\(\eta\).  Put

\[
\Delta_i^\eta=Q_i^\eta-C_i^\eta,
\qquad \lambda_i=\Delta_i^1-\Delta_i^0.
\]

For the spare, whose opponents' laws do not depend on \(q\), put

\[
\Delta_s=Q_s-C_s,\qquad \kappa=C_s-Q_s=-\Delta_s.
\]

For \(p\in[0,1]\), define

\[
\Phi_p(t)=(1-p)t_+ + p(-t)_+,
\qquad t_+=\max\{t,0\}.
\]

For an actual profile \(\rho\), write

\[
D(\rho)=\sum_{i\in I}\bigl(B_i(\rho)-U_i(\rho)\bigr),
\qquad
\operatorname{Expl}(\rho)=
\max_{i\in I}\bigl(B_i(\rho)-U_i(\rho)\bigr).
\]

Assume:

1. **Source debt.**  The base players are exactly the positive-debt players:

   \[
   a_b=-\Delta_b^0>0\quad(b\in B),
   \]

   \[
   \Phi_{p_f}(\Delta_f^0)=0\quad(f\in F),
   \qquad \Delta_s\le0.
   \]

   Hence
   \(D(\sigma^{\mathrm{src}})=D(\widehat\sigma^0)
   =a_{b_0}+a_{b_1}=:D_0\).

2. **Collision cancellation.**  At the sure-spare endpoint,

   \[
   \Delta_b^1\ge0\quad(b\in B),
   \qquad
   \Phi_{p_f}(\Delta_f^1)=0\quad(f\in F).
   \]

   Define

   \[
   \tau_b=\frac{-\Delta_b^0}{\Delta_b^1-\Delta_b^0}
   =\frac{a_b}{\lambda_b}\in(0,1],
   \qquad q_*=\max\{\tau_{b_0},\tau_{b_1}\}.
   \]

3. **Punishment floors.**  If \(u^\eta=U(\widehat\sigma^\eta)\) and \(\chi_i\) is
   player \(i\)'s behavioral punishment value, then

   \[
   \chi_i\le u_i^0,\qquad \chi_i\le u_i^1\qquad(i\in I).
   \]

4. **Spare-debt budget.**

   \[
   q_*\kappa\le D_0. \tag{SC}
   \]

Then, with \(d_i(q):=d_i(\widehat\sigma^q)\),

\[
d_{b_0}(q_*)=d_{b_1}(q_*)
=d_{f_0}(q_*)=d_{f_1}(q_*)=0,
\]

\[
d_s(q_*)=q_*\kappa,
\qquad D(\widehat\sigma^{q_*})=q_*\kappa\le D_0,
\]

and every coordinate of \(u^{q_*}\) remains above its punishment floor.
Consequently:

1. if \(q_*\kappa\le\varepsilon\), then \(\widehat\sigma^{q_*}\) is a terminal
   \(\varepsilon\)-Nash profile against all behavioral deviations;
2. if \(\kappa=0\), then \(\widehat\sigma^{q_*}\) is exact terminal Nash and its
   first-stage root defines an exact punishment-floor-admissible edge of
   absorption charge one, with the actual source
   \(\sigma^{\mathrm{src}}\) as continuation; in particular the exact
   terminal-Nash compiler directly gives a uniform-equilibrium payoff;
3. if \(\sigma^{\mathrm{src}}\) is a global minimizer of total terminal debt among all
   actual behavioral profiles (equivalently, its semantic pair is a global
   minimizer in the terminal-semantic carrier) and
   \(\kappa>0\), then minimality forces \(q_*\kappa=D_0\), so
   \(\widehat\sigma^{q_*}\) is another actual minimizer and the positive-debt support
   drops from \(B\) to \(\{s\}\).

In particular, strict inequality \(q_*\kappa<D_0\) is incompatible with a
positive global-minimum source satisfying the hypotheses.

## Proof

### Unrestricted deviations collapse to one stage

After any unilateral behavioral replacement, at least one member of \(B\)
still Quits surely at the first stage.  Hence absorption remains immediate.
If player \(i\)'s deviating first-stage Quit probability is \(\alpha\), its
payoff is

\[
\alpha Q_i(q)+(1-\alpha)C_i(q).
\]

Thus the unrestricted behavioral cap is exactly

\[
B_i(q)=\max\{Q_i(q),C_i(q)\}. \tag{1}
\]

### Exact debts and affine collision lift

For \(i\ne s\), the prescribed Quit probability \(p_i\) is fixed, so

\[
d_i(q)=\Phi_{p_i}(\Delta_i(q)). \tag{2}
\]

For the spare, \(p_s=q\) and \(\Delta_s=-\kappa\), hence

\[
d_s(q)=q\kappa. \tag{3}
\]

Conditioning on the spare's Bernoulli action gives

\[
\Delta_i(q)=(1-q)\Delta_i^0+q\Delta_i^1
=\Delta_i^0+q\lambda_i. \tag{4}
\]

At the terminal-law level each old atom \(S\) is split into \(S\) and
\(S\cup\{s\}\) with masses \((1-q)\Pr_0(S)\) and \(q\Pr_0(S)\).

For a free player, convexity and nonnegativity of \(\Phi_{p_f}\) imply

\[
d_f(q)\le(1-q)\Phi_{p_f}(\Delta_f^0)
+q\Phi_{p_f}(\Delta_f^1)=0,
\]

so \(d_f(q)=0\).  For a base player \(p_b=1\), and therefore

\[
d_b(q)=(a_b-q\lambda_b)_+. \tag{5}
\]

The definition of \(q_*\) makes both base debts zero.  Equations (3)--(5)
give the displayed debt vector and

\[
\operatorname{Expl}(\widehat\sigma^{q_*})=q_*\kappa. \tag{6}
\]

### Punishment floors

Every prescribed payoff coordinate is affine in \(q\):

\[
u_i(q)=(1-q)u_i^0+qu_i^1.
\]

Endpoint floor domination therefore implies floor domination throughout the
interval.

### Exact edge at \(\kappa=0\)

When \(\kappa=0\), all debts at \(q_*\) vanish, so \(\widehat\sigma^{q_*}\)
is an exact terminal Nash profile and its first-stage product root
is exact Nash.  Joint Continue mass and every deviator's opponent-Continue
mass are zero because one of the two forced quitters remains.  Thus the root's
payoffs and Nash inequalities are independent of the continuation.  With the
floor inequalities above, it gives the claimed charge-one exact edge with
tail payoff \(u^0\), current/predecessor payoff \(u^{q_*}\), and relation
orientation

\[
(u^0,\text{stored tail root})\longrightarrow
(u^{q_*},\text{the }q_*\text{ root}).
\]

Behavioral chronology is read in the reverse direction: the current root is
prefixed to the literal continuation \(\sigma^{\mathrm{src}}\), and that
root/profile splice is exactly \(\widehat\sigma^{q_*}\).  Exact terminal Nash
itself, rather than the isolated edge without a return, is what directly
feeds the terminal compiler.

### Global-minimum rank drop

If \(\sigma^{\mathrm{src}}\) is a global minimizer, semantic equality with
\(\widehat\sigma^0\), (SC), and the fact that
\(\widehat\sigma^{q_*}\) is an actual profile imply equality

\[
q_*\kappa=D_0.
\]

When \(\kappa>0\), also \(q_*>0\), so the spare is the unique positive-debt
coordinate at \(\widehat\sigma^{q_*}\).  The support drops from two to one.

## Sharp interval form

For every \(q\in[0,1]\),

\[
\operatorname{Expl}(\widehat\sigma^q)=
\max\left\{q\kappa,
(a_{b_0}-q\lambda_{b_0})_+,
(a_{b_1}-q\lambda_{b_1})_+\right\}. \tag{7}
\]

For \(\varepsilon\ge0\), define

\[
L_\varepsilon=\max\left\{0,
\frac{a_{b_0}-\varepsilon}{\lambda_{b_0}},
\frac{a_{b_1}-\varepsilon}{\lambda_{b_1}}\right\},
\]

\[
U_\varepsilon=
\begin{cases}
1,&\kappa=0,\\
\min\{1,\varepsilon/\kappa\},&\kappa>0.
\end{cases}
\]

Then

\[
\widehat\sigma^q\text{ is terminal }\varepsilon\text{-Nash}
\quad\Longleftrightarrow\quad q\in[L_\varepsilon,U_\varepsilon]. \tag{8}
\]

## Claimed conjecture-facing use and open producer

The theorem is meant as a same-profile five-player verifier.  It removes the
alignment and unrestricted-deviation issues once its hypotheses hold.  The
remaining producer is to derive the two free endpoint-complementarity
conditions and the scalar budget \(q_*\kappa\le D_0\) from an actual four-role
pair-base window.

It does **not** claim that a spare label or a graph cycle alone supplies those
hypotheses.  With only one sure quitter, the behavioral-cap reduction fails;
if endpoint complementarity fails, free-player debt can be recreated; and if
\(q_*\kappa>D_0\), the family cannot cancel the original obstruction within
the global-minimum budget.
