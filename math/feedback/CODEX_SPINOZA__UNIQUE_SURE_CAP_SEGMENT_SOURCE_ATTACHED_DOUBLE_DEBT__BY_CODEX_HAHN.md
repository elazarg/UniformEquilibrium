# Review of the unique-sure cap-segment double-debt theorem

Reviewer: CODEX_HAHN

Reviewed note:
`notes/CODEX_SPINOZA__UNIQUE_SURE_CAP_SEGMENT_SOURCE_ATTACHED_DOUBLE_DEBT.md`
at exact SHA256
`5ab551d5981ed18f454d44d58291acc3ed016f6a825f8680eef848211a755d91`.

Dependency checked:
`notes/CODEX_SPINOZA__UNIQUE_SURE_INNER_ROOT_ACTUAL_APPROXIMATE_CAP_HANDOFF.md`
at exact SHA256
`d8225cfd957da22a9cfd836f4e1f5e29ebdf503424e06675627b852d1fe25367`.

Comparison targets:

- `formalized/FINITE_CLOCK_DOUBLE_FULL_GAP_COSOURCE.md`;
- `notes/CODEX_SPINOZA__CAP_SEGMENT_UNIFORM_GAP_AND_SECOND_RESPONSE.md`.

## Verdict

**PASS as exact ordinary mathematics and as a source-attached reduction.**
I found no false mathematical claim, hidden cap-attainment assumption, or
failure of actual behavioral realization.  The surviving contribution is
strictly narrower than a new co-source existence theorem and is not a
consumer: it is an approximate-cap interpolation lemma on the particular
unique-sure source, preserving its literal inner-root and outer-word
ancestry.

## Claim checked

Starting from the actual unique-sure source \(\rho_n\), the retained
\(\varepsilon\)-cap response \(\beta_{n,k}\), and the child
\(\chi_n=\rho_n[k\leftarrow\beta_{n,k}]\), with

\[
d_k(\rho_n)\ge D_*/2,
\qquad
d_k(\chi_n)\le\varepsilon<D_*/16,
\]

the note mixes only player \(k\)'s two complete stopping laws.  It claims an
actual intermediate profile \(\zeta_n\) at which

\[
d_k(\zeta_n)=D_*/4
\]

and some fixed outsider, after refinement, has debt at least \(D_*/4\).
The retained owner response gains more than \(3D_*/16\), and one pure
finite-time-or-Never outsider response gains at least \(D_*/8\), both at
that same source.  No compatibility after either response is claimed.

## Mathematical audit

### Actual stopping-law realization

The convex combination of the two laws on
\(\mathbb N\cup\{\mathrm{Never}\}\) is again a stopping law and is realized
by conditional hazards.  This produces an actual behavioral strategy, not
a correlated or relaxed strategy.  Equality of laws is all that payoff and
cap semantics use.  If one insists on literal hazard equality at the two
endpoints, hazards after a zero-survival date can be chosen to match the
given endpoint strategies; those coordinates are behaviorally irrelevant.

I also tested the proposed interpolation on the smallest nontrivial finite
model, with both owner laws supported on \(\{0,1,\mathrm{Never}\}\) and an
arbitrary fixed opponent product law.  Against fixed opponents there are
numbers \(V(0),V(1),V(\infty)\) such that the owner's payoff is

\[
\mu(0)V(0)+\mu(1)V(1)+\mu(\infty)V(\infty).
\]

It is therefore exactly affine under the proposed law mixture.  No finite
stopping-law counterexample exists to the segment identity.

### Constant cap and affine debt

Only player \(k\)'s law varies.  Its opponents and hence its unrestricted
complete cap are unchanged throughout the segment.  Its prescribed payoff
is affine in its own stopping law.  Thus equation (6) is exact even when the
cap is not attained.  The endpoint inequalities strictly bracket
\(D_*/4\), so the asserted unique parameter \(\lambda_n\in(0,1)\) exists.

### Global-minimum pigeonhole step

Every interpolated profile is actual, so its semantic pair belongs to the
terminal carrier and its total debt is at least \(D_*\).  At the selected
point the three outsider debts sum to at least \(3D_*/4\); nonnegativity of
individual debts then gives one outsider with debt at least \(D_*/4\).
Finite pigeonhole legitimately fixes its label on a subsequence.

### The two displayed responses

The owner's opponents are identical at \(\rho_n\), every point of the
segment, and \(\chi_n\).  Hence the same retained response remains within
\(\varepsilon\) of the same cap and gains at least
\(D_*/4-\varepsilon>3D_*/16\) at \(\zeta_n\).

For the outsider, pure-time extremality identifies the complete cap with
the supremum over deterministic finite quit times and Never.  From debt at
least \(D_*/4\), choosing within \(D_*/8\) of that supremum gives the stated
gain at least \(D_*/8\).  Attainment is not asserted or needed.

### Ancestry and temporal cases

The copied-prefix gain identity is valid: a response which copies the
prescribed finite word and changes behavior only after joint survival has
gain equal to the suffix gain times the word's joint-survival probability.
Exactness of the old roots is not incorrectly transferred to the
interpolated suffix.

The three temporal cases in Section 4 are exhaustive only after taking the
capacity-selected inner cut as the local time origin.  This is indeed how
\(\rho_n=q_n\triangleright X_n\) is defined in the dependency: a pure-time
response at that local profile either quits at its date zero, later, or
Never.  Read as a statement about the unreindexed original profile, an
earlier-time case would be missing.  Corollary 3.2 correctly treats the
outer word separately, so the intended local reading is sound.

## Novelty audit

The result is not a strengthening of
`FINITE_CLOCK_DOUBLE_FULL_GAP_COSOURCE` in its existence or quantitative
conclusion.  That formalized packet already produces, from a game-level
gap \(\Gamma\), one finite-clock source with two distinct debts at least
\(\Gamma\), with finite-menu cap attainments.  The present theorem produces
only two debts at the scale \(D_*/4\), and its outsider response need not
attain the cap.

Nor does it supersede
`CODEX_SPINOZA__CAP_SEGMENT_UNIFORM_GAP_AND_SECOND_RESPONSE`.  When an exact
cap response is available, that theorem gives a more general and more
quantitative labelled segment cover and a literal two-owner response chain.

The exact new contribution is the combination that neither comparison
provides:

1. it works with the nonattained \(\varepsilon\)-cap response furnished by
   the unique-sure inner-root construction;
2. it stays on that particular actual source and preserves the retained
   Continue-then-literal-tail response and its outer exact-word passport;
3. global minimum debt alone forces a second debtor at an explicit point of
   this same source-attached segment.

This is useful source coherence, but not response compatibility.  Applying
either response changes an opponent law relevant to the other response, and
the interpolated first row is not an exact root.  The note correctly stops
before claiming a Nash--Bellman edge, return, renewable rank, terminal
profile, or uniform-equilibrium payoff.

## Minor presentation qualification

The phrase “two co-sourced full debts” should not be read as “two full
terminal-gap debts” in the sense of
`FINITE_CLOCK_DOUBLE_FULL_GAP_COSOURCE`.  The proved quantities are exactly
the two \(D_*/4\) lower bounds.  This is a terminology caution, not a
mathematical objection to the frozen theorem.

