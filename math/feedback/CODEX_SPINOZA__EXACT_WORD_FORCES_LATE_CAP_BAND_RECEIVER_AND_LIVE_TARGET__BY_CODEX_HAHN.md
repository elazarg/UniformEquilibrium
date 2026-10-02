# Review of the exact-word late cap-band receiver theorem

Reviewer: CODEX_HAHN

## Delta review of the strengthened note

The authoritative revised note was checked at exact SHA256
`62d9168b8f734b61f1bced52b8bd19d14386cfd60fe50d520dede7fb96259b06`.

**PASS.**  The revision faithfully incorporates the strengthening below:
all preboundary clocks are outside the band, the target owner survives the
word surely, and target joint reach is exactly the preserved opponent
survival \(\beta_{n,k}\ge\eta\).  The added one-root regression is also
correct.  With only

\[
r_k(\{k,j\})=1,
\qquad r_j(\{j\})=1
\]

nonzero, the source root with sure \(k\) and the tail with sure \(j\) has all
four root comparisons exact.  The late \(k\)-response reaches the tail and
pays one, but at the target player \(j\) gains one by Quitting at the old
root.  The simultaneous \(\{k,j\}\) profile is indeed a terminal Nash
profile, so the regression is correctly restricted to \(D_*=0\) and does
not overclaim against the hard global branch.

Reviewed note:
`notes/CODEX_SPINOZA__EXACT_WORD_FORCES_LATE_CAP_BAND_RECEIVER_AND_LIVE_TARGET.md`
at exact SHA256
`ff76bbcff3fa86861f07c3c7521ae41468fba1197367f85893afa0e0f2723935`.

## Verdict

**PASS, with a strict strengthening available.**  The finite exact-word
screen, forced late-or-Never receiver, vanishing source tail mass, and
pushforward joint-reach argument are all correct.  I found no finite
stopping-law counterexample.  In fact the proof implies that the target
owner has no stopping mass anywhere inside the word, so equation (13) can be
strengthened from \(\eta\kappa/2\) to \(\eta\).

## Claim checked

The note starts with a literal finite word of exact payoff Nash roots over an
arbitrary actual tail.  On the unique-sure persistent branch, the fixed
owner \(k\) has source debt at least \(D_*/2\), and its opponents survive
the word with probability at least \(\eta\).  At cap-band width
\(e=D_*/4\), the note claims that every \(e/2\)-near-cap pure-time receiver
is at the tail boundary, later, or Never.  Redirecting the source bad mass
to such a receiver gives a fixed-gain actual target with positive actual
joint reach to the old tail.

## Detailed audit

### 1. Exact finite-word pure-time screen

For a player who plans to Quit at \(r<m\), the date-\(r\) Quit endpoint is
at most the prescribed value \(u_{r,i}\) by exact one-stage Nash optimality.
Working backward, the deviator Continues at each earlier row.  The Continue
endpoint is affine and nondecreasing in the scalar successor value, and
exact Nash optimality bounds that endpoint by the prescribed value at the
row.  Induction gives

\[
U_i(\Sigma[i\leftarrow Q_r])\le U_i(\Sigma).
\]

This argument does not assume that the source player's own prescribed law is
pure.  It uses the expected payoff of the mixed Nash action as the row value,
so mixed source laws cause no gap.  It is also exactly the finite instance
of the named Bellman-supersolution theorem.

### 2. Forced late receiver

If a receiver \(r<m\) were within \(e/2\) of the cap, the screen would give
\(f_n(r)\le U_k(\Sigma_n)\).  On the other hand,

\[
C_n-e/2
 = U_k(\Sigma_n)+d_k(\Sigma_n)-D_*/8
 \ge U_k(\Sigma_n)+3D_*/8.
\]

The strict near-cap inequality is therefore incompatible with \(r<m\).
The boundary clock \(m\), later finite clocks, and Never are correctly
retained.

This argument needs only the defining supremum of the complete cap, so no
attainment or compactness of behavioral strategies is hidden.

### 3. Vanishing source mass beyond the word

Player \(k\)'s source probability of reaching the tail boundary is the
product of its Continue probabilities over the word.  It contains the
innermost factor \(1-q_{n,0,k}\to0\); hence equation (8) is correct even as
the word length varies.  This is own marginal survival, not joint survival.

### 4. Cap-band target and the stated constant

The checked band inequality gives bad mass at least

\[
{d_k(\Sigma_n)-e\over2R}\ge {D_*\over8R}=\kappa.
\]

After subtracting the vanishing source mass at or beyond \(m_n\), at least
\(\kappa/2\) early source mass is bad.  A late receiver sends that mass past
the boundary.  The target opponents are unchanged and survive with
probability at least \(\eta\), so independence gives the note's lower bound
\(\eta\kappa/2\).  The gain and target-debt bounds in equation (12) are the
standard cap-band bounds with the correct constants.

The least-positive-bad-clock construction also gives a cut strictly before
\(m_n\), and the live roots strictly before that cut are literally
unchanged.  Their Nash property against the changed successor is not
preserved, as the note correctly warns.

## Strict strengthening

Lemma 1.1 gives more than the proof presently uses.  For every \(r<m_n\),

\[
C_n-f_n(r)\ge C_n-U_k(\Sigma_n)
 =d_k(\Sigma_n)\ge D_*/2>e.
\]

Thus **every** finite clock inside the word is outside the width-\(e\) cap
band.  The cap-band pushforward moves all source stopping mass before
\(m_n\) to the late receiver.  Every clock already at or beyond \(m_n\)
either stays there or is also sent to the late receiver.  Consequently

\[
\Pr_{\widehat\Sigma_n}(T_k\ge m_n)=1
\]

and, since the opponents are unchanged,

\[
\Pr_{\widehat\Sigma_n}(\text{joint survival through }m_n)
=\beta_{n,k}\ge\eta.
\]

So the target owner literally Continues throughout the entire exact word.
This is qualitatively stronger than retaining only a positive portion of
the redirected bad mass and is potentially useful for the downstream
adapter.  It does not make the modified product rows Nash for the outsiders.

## Falsification test and precise remaining seam

I tried the minimal one-root construction.  Let player \(k\) Quit surely at
the exact source root, let an opponent \(j\) Continue there and Quit later in
the tail, and choose \(k\)'s rewards so that current Quit and following the
prescribed tail both pay zero while continuing and joining \(j\) later pays
one.  Choose \(j\)'s root rewards so that it prefers Continue while \(k\)
Quits, but prefers Quit when \(k\) instead Continues to the tail.  The source
root is exact and \(k\)'s cap response is necessarily late, yet installing
that response destroys \(j\)'s root Nash inequality.

This local regression has a terminal equilibrium elsewhere and hence
\(D_*=0\); it is not a counterexample to the global positive-minimum branch.
It does prove that exact-word screening plus late receiver and positive
actual reach do not, by themselves, preserve the word as a Nash--Bellman
chronology.  Any repair must use the positive global minimum/no-uniform-payoff
structure to consume the induced outsider root defect.

The exact advance is therefore stronger than a generic paid port: one has a
fixed-gain, source-attached sibling whose mover deterministically survives
the entire old word and which reaches the literal old tail with probability
at least \(\eta\).  The missing compiler is no longer receiver selection or
reach.  It is a theorem that handles the changed outsiders' root comparisons
and the target's conditional owner law at that reached tail—either by
Nashifying the modified word with controlled charge, or by converting a
failed outsider inequality into an accepted source-matched edge or rank.
