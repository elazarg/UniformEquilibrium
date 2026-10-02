# Consume strict positive-social-surplus escape

## Mathematical data

Let \(I\) be finite and nonempty, and suppose every own singleton reward is
nonnegative. Let \(z=(u,b)\) minimize total terminal-semantic debt, and assume
that no actual behavioral profile attains the value \(D(z)\). Let actual
profiles \(\sigma_n\) realize \(z\). Suppose their compactified marginal
stopping laws converge weakly to laws \((\mu_i)_{i\in I}\), let
\(\bar\sigma\) be the actual product behavioral profile reconstructed from
those laws, and suppose their terminal laws converge to \(m^*\).

If \(m\) is the terminal law of \(\bar\sigma\), define

\[
e(S)=m^*(S)-m(S),
\qquad
R(S)=\sum_i r_i(S).
\]

All coalition sums below range over nonempty coalitions.

Assume the escape is genuinely nonattaining:

\[
\delta:=D(\bar\sigma)-D(z)>0.
\]

The supplied exact account is

\[
e(S)\ge0,
\qquad
\sum_S e(S)R(S)
=\delta+\sum_i\bigl(b_i-B_i(\bar\sigma)\bigr)>0.
\]

## Supplied boundary

The displayed terminal-law escape account, strict positive escape-mass
consequence, and quantitative social-reward floors may be used. The weak and
strict nonpositive-social chambers have direct attainment conclusions.

Also assume that no static nonnegative social costate closes the game. Thus
there is no vector \(\theta\ge0\) with at least two positive coordinates such
that

\[
\theta\cdot s\ge0,
\qquad
\theta\cdot(r(S)-s)\le0
\quad(S\ne\varnothing),
\]

where \(s_i=r_i(\{i\})\). Such a vector would force zero minimum debt and a
uniform-equilibrium payoff directly.

## Question

Using the same realizing sequence and escaped law, prove one of:

1. an actual profile with debt below \(D(z)\);
2. terminal approximate Nash profiles with one limiting payoff;
3. a source-matched positive admissible-payoff return, or a strict finite rank
   on a source-preserving transition system whose every terminal state has a
   terminal or charged-return consumer; or
4. an explicit finite reward table with a certified positive exploitability
   gap against every behavioral profile which realizes the strict escaped
   social-surplus configuration.

## Boundary

If \(R(S)\le0\) for every nonempty coalition, the supplied attainment theorem
gives an actual minimum profile. That chamber is outside this question. An
escaped coalition with positive social reward, without an executable
consumer, is not an answer.
Escaped terminal-law mass is not current root absorption.
