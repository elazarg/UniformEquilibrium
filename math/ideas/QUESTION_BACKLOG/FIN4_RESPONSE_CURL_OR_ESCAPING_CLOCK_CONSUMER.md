# Consume a response curl or escaping stopping clock

## Mathematical data

Fix a four-player quitting game with positive minimum terminal-semantic debt
\(D_*>0\). Let

\[
P_n,\quad Y_n,\quad Q_n,\quad R_n
\]

be four actual behavioral profile families attached to one literal source.
Fix distinct players \(p\) and \(j\), and constants \(g,c>0\).

Assume:

1. \(Y_n\) differs from \(P_n\) only in player \(p\)'s complete strategy,
   and

   \[
   U_p(Y_n)-U_p(P_n)\ge g.
   \]

   Consequently player \(p\)'s unrestricted cap is unchanged and its debt
   falls by exactly this gain.
2. For one pure stopping time \(a_n\in\mathbb N\cup\{\infty\}\),

   \[
   Q_n=P_n[j\leftarrow a_n],
   \qquad
   R_n=Y_n[j\leftarrow a_n].
   \]

   Thus the same response is evaluated against the two literal opponent
   backgrounds.
3. Player \(j\)'s debt at the receiving response tends to zero:

   \[
   d_j(R_n)\longrightarrow0.
   \]

4. The mixed response gain has a fixed positive curl:

   \[
   \bigl(U_j(R_n)-U_j(Y_n)\bigr)
   -\bigl(U_j(Q_n)-U_j(P_n)\bigr)
   \ge c.
   \]
5. All four semantic pairs and terminal laws are compactified along one
   common subsequence, and the literal source ancestry of every profile is
   retained.

The alternating cap term around this rectangle is zero. The positive
quantity above is a response/regret curl, not an absorption charge.

## Question

Prove that the supplied family yields at least one of:

1. terminal approximate Nash profiles with one limiting payoff;
2. a positive source-attached admissible-payoff return;
3. a renewable finite-rank transition on complete source objects;
4. a bounded pure-time active-face transition which strictly enlarges a
   persistent zero-debt face;
5. an escaping-time packet with enough actual joint and deleted-player reach
   to enter a chronological consumer; or
6. a contradiction to positive global minimum debt.

An explicit positive-gap four-player table realizing the entire response
rectangle and defeating Outputs 1--5 is an acceptable negative answer.

## Required case split

If \((a_n)\) is bounded, pass to a fixed finite response time and use the
resulting literal active-face geometry. A closed face separation without a
well-founded transition is insufficient.

If \(a_n\to\infty\) or \(a_n=\infty\) cofinally, distinguish finite stopping
mass escaping to infinity from genuine Never mass. Absolute dates alone are
not a rank, and convergence of date-forgetting terminal laws does not identify
these two phenomena.

If the limiting common response has zero regret on both backgrounds, explain
why the next cap-attaining response preserves the existing zero-debt face, or
consume the alternative in which it reactivates a killed coordinate.

## Nonanswers

- treating the rectangle as a chronological path;
- treating the response curl as exact-root absorption charge;
- choosing a different response on the two opponent backgrounds;
- extracting a positive-mass pure-time edge which does not start from the
  prescribed source corner;
- a compact active face with no renewable rank; or
- inferring a second persistent clock solely from one response time escaping
  to infinity.
