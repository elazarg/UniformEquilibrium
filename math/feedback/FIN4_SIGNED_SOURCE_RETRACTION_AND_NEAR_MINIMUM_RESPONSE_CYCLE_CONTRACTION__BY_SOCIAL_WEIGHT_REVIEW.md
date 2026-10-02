# Review of signed source retraction and near-minimum response-cycle contraction

Reviewer: `SOCIAL_WEIGHT_REVIEW`

Candidate reviewed:
`/tmp/FIN4_SIGNED_SOURCE_RETRACTION_AND_NEAR_MINIMUM_RESPONSE_CYCLE_CONTRACTION.md`
at SHA-256
`0bc63e0e7e4684a4f64f5122e0e8fcf14a44d62f02334a5fe9c0bd665c15fe79`.

## Verdict

**PASS as ordinary mathematics, with two bounded presentation repairs before
export.**  I found no counterexample to the signed retraction, the
near-minimum response chord, or the unrestricted-cap transport.  The packet
does strictly contract the near-minimum horizontal response-cycle arm into
the existing finite support lane.  It does not consume the uniformly
off-minimum signed outputs, and it says so.

The two repairs are:

1. In the source-regeneration paragraph, state the order unambiguously:
   causalize \(H_n^s\) to choose \(W_n\); form
   \(P_n=W_n\star Y_n\); prove the complete limit and shifted marked-mass
   floor for \(P_n\); then causalize the supplied family \(P_n\) at the
   shifted marks to obtain the child source at \(y\).  Causalizing \(Y_n\)
   alone gives a same-point source but does not make the copied-prefix target
   family the child chronology.  The last sentence of the current proof
   already indicates the correct construction; the earlier sentence saying
   to causalize \(H_n^s\) and \(Y_n\) separately is ambiguous and should be
   replaced.  Store \(A_n\to P_n\) and the \(P_n\)-based child in the usual
   thin paired-edge wrapper.
2. Spell out the tailwise cofinal reindexing once.  If the alternative is
   applied to the tail beginning at \(N\) and returns relative source index
   \(k_N\), its original global source index is \(m_N=N+k_N\ge N\).  Select
   the cofinal cycle arm and then a strict subsequence of the \(m_N\).  This
   proves, rather than merely abbreviates, that the retained sources still
   converge to the supplied minimum joint point.  No new hypothesis is
   needed.

These are source-typing and quantifier clarifications.  The required objects
already exist in the proof.

## 1. Tailwise source adapter

`minimumRealizingSequence_exists_actualSourcePureTimeResponseAlternative` in
`ActualSourcePureTimeResponseAlternative.lean` applies to every tail of the
producer's literal realizing family.  Its returned port stores
`sourceIndex`, and `source_to_orbit_profile` gives literal finite behavioral
replacement ancestry from that exact profile to every selected response
orbit state.  Passing to tails makes the corresponding global source indices
cofinal as described in repair 2.  Hence payoff, cap, and complete-law
convergence of the incoming producer is retained after joint
compactification.

The Fin4 wrapper in
`FinFourActualSourcePureTimeResponseAlternative.lean` gives the period and
end bound \(1296\).  Every displayed cycle vertex is strictly off minimum,
and every edge has the checked exact cap-attainment, gain floor \(D_*/4\),
zero target mover debt, and literal target-to-next-source identity.

## 2. Signed four-coordinate retraction

For the coordinate path

\[
 S=Z^0,\ldots,Z^4=X,
\]

some forward increment is at least
\(\delta/4\), where \(\delta=D(X)-D(S)>0\).  Reversing that single coordinate
edge and writing \(A=Z^{r+1}\), \(B=Z^r\), own-cap invariance gives exactly

\[
 D(A)-D(B)
 =U_i(B)-U_i(A)
  +\sum_{j\ne i}\bigl(d_j(A)-d_j(B)\bigr).
\]

The two-case split is correct.  The mover term gives \(\delta/8\); otherwise
one of three nonmovers contributes \(\delta/24\), and splitting that debt
change into cap fall plus reverse payoff rise gives \(\delta/48\).  Since the
cycle excess is at least \(\varepsilon\) while the retained source excess is
eventually at most \(\varepsilon/2\), the packet's final constants
\(\varepsilon/16\) and \(\varepsilon/96\) follow.  The signs in all three
outputs are correct.

The nonmover outputs are semantic externalities, not deviations.  The packet
does not misclassify them.

## 3. Near-minimum chord

Fixing one edge after a common subsequence is legitimate because period,
position, mover, response mode, and coalition labels are finite.  Exact
unrestricted cap attainment gives

\[
 B_i(Y_n)=B_i(X_n),\qquad U_i(Y_n)=B_i(X_n),\qquad d_i(Y_n)=0.
\]

Mixing only player \(i\)'s complete stopping law is an ordinary behavioral
strategy.  Prescribed payoff and terminal law are affine.  For a nonmover,
each fixed complete response payoff is affine in that stopping law, so its
supremum is convex; the mover cap is unchanged because the opponents are
unchanged.  Therefore every chord debt coordinate lies below the affine
endpoint chord, exactly as in
`quittingTerminalSemanticDebt_responseChord_le`.

Both endpoint debt sums tend to \(D_*\).  Global minimality squeezes the
chord sum to \(D_*\), so every coordinate slack vanishes.  Thus the displayed
coordinatewise debt equality is exact at the limit.  The mover is positive
at the chord point and zero at the target; every target-positive coordinate
stays positive at the chord point; and \(D_*>0\) keeps the target support
nonempty.  The strict support inclusion and cardinality at most three are
therefore sound.

## 4. Fixed moving atom and unrestricted caps

A pure-clock target which is not all Never terminates surely at its earliest
finite date in one nonempty coalition.  If all Never occurred cofinally in
the near-minimum family, its fixed semantic pair would have debt \(D_*>0\)
and be a global minimum, contradicting
`not_allNever_positiveMinimumTerminalSemanticDebt`.  Finite coalition
selection therefore gives one fixed \(K\ne\varnothing\).  The \(Y_n\) stage
mass is one, and the one-player stopping-law mixture retains at least \(s\)
of it at the same moving date.

The complete-cap estimate

\[
 \left|B_k(W_n\star T_n)-
 \max\{r_k(\{k\}),B_k(T_n)\}\right|
 \le 2M(1-H_{k,n})
\]

survives all adversarial timing tests.  A pure response either stops in the
nonempty word, in which case it differs from singleton cash-out only when an
opponent fails to survive the word, or it continues through the word and is
coupled to a tail pure response.  Pure-time extremality covers randomized
behavioral strategies, Never, date zero, and arbitrarily late stopping.
Joint survival tending to one forces every deleted survival \(H_{k,n}\) to
one.  The positive-minimum singleton moat selects the tail-cap branch at both
limits.  Thus payoff, law, deleted-law, and unrestricted-cap convergence of
both common-prefix families is valid.

With repair 1, the shifted \(K\)-mass floor on \(P_n\), not merely its limit
law coordinate, supplies `nonempty_sourceFaithfulMinimumCausalization`.
Its chronology fields package a `QuittingMinimumLawCausalSuffixAtom`; the
incoming table-level hard residual, minimum equality, and debt-infimum fields
then give a complete same-residual `FinFourMinimumAtomProducer`.

## 5. Novelty and boundary

The checked finite response-cycle externality ledger already gives a
nonmover payoff fall and debt rise somewhere around a closed cycle.  It does
not orient a coordinate edge back toward the retained source.  The packet's
signed retraction is therefore not a duplicate of that ledger.

The full-debt cap-near response export already contracts a full-support
minimum source.  It does not apply to an arbitrary near-minimum response
cycle whose limiting source support may be proper.  The generic response
chord and common-prefix notes contain the local ingredients, but the present
packet supplies the missing actual-cycle family, fixed target atom, cofinal
source adapter, and support-child conclusion.  This is a genuine strict
reduction of the named off-minimum cycle obligation.

The result remains nonterminal:

* the source-oriented paid edge still enters the paid-cap waist;
* the signed nonmover cap/payoff retraction has no consumer;
* the strict-support child still has the standard tangent exits; and
* no horizontal edge is asserted to be a Nash--Bellman temporal edge.

Those nonclaims are stated accurately.  Subject to the two bounded repairs,
I find no mathematical export blocker.

## Post-repair delta review

Repaired candidate reviewed at SHA-256
`49777d61b4bb486bd08f1e6b2b0680bf22898bd6f4bccab318d05bc56cfa23e9`.

**PASS.**  Both requested source repairs are now explicit.  The tail selected
inside the family beginning at \(N\) is reindexed by
\(m_N=N+k_N\ge N\) before strict refinement.  In the minimum arm the proof
now causalizes \(H_n^s\), copies its selected word to form
\(P_n=W_n\star Y_n\), proves the complete limit and shifted atom floor for
that literal \(P_n\) family, and causalizes \(P_n\) for the child chronology.
The paired wrapper stores the actual \(A_n\to P_n\) edge and the
\(P_n\)-based child.

The strengthened uniformly off-minimum arm is also sound.  If the reverse
mover gain is smaller than half the selected debt decrement, some nonmover
\(j\) satisfies

\[
 d_j(A)-d_j(B)\ge\delta/24.
\]

Since \(d_j(B)\ge0\), this gives \(d_j(A)\ge\delta/24\).  Applying
`positiveDebt_exists_actualJointReach_paidRow_mem_support` at the literal
hybrid \(A\), observer \(j\), and any fixed
\(0<\rho\le d_j(A)\) returns a genuine source-supported paid row of gain
\(\rho/4\), together with

\[
 \rho\le4M\,\operatorname{OwnSurvival},\qquad
 \rho\le8M\,\operatorname{OppReach},\qquad
 \rho^2\le32M^2\,\operatorname{JointReach}.
\]

On the cofinal family, \(\delta\ge\varepsilon/2\), so taking
\(\rho=\varepsilon/48\) gives exactly the stated gain
\(\varepsilon/192\) and reach floors.  This is a profitable unilateral
pure-time comparison selected at the actual hybrid, not a relabelled
nonmover externality.  It strictly strengthens the earlier candidate by
routing every uniformly off-minimum output into the existing paid-cap waist.

Final-path scans on the repaired candidate found no control bytes, no missing
links, and balanced \(136/136\) inline and \(39/39\) display delimiters.  I
find no remaining mathematical or packet-format blocker.

### Final paid-row delta

Final candidate reviewed at SHA-256
`457b994ef4f7ace66865467f56e50a09e3bbb314e8ae7e3be779cc3bbdfc368f`.

**PASS.**  The additional typing step in the large reverse-gain arm is exact.
Because \(A\) and \(B\) differ only in player \(i\), the strategy used by
\(i\) in \(B\) is a legal unilateral response at \(A\).  Hence

\[
 d_i(A)=B_i(A)-U_i(A)
 \ge U_i(B)-U_i(A)=g.
\]

When \(g\ge\delta/8\), the actual-reach theorem may therefore be applied at
the literal source \(A\), observer \(i\), and debt floor \(\delta/8\).  It
returns a source-supported paid row of gain \(\delta/32\) with the same
three explicit reach floors.  On the cofinal family
\(\delta\ge\varepsilon/2\); using the fixed floor \(\varepsilon/16\) gives
the stated row gain \(\varepsilon/64\).  No cap-attainment of the reverse
replacement itself is being assumed.

Thus both uniformly off-minimum alternatives now output genuine paid rows,
and the near-minimum alternative still outputs the strict-support child.
The final candidate has no control bytes or missing links and has balanced
\(145/145\) inline and \(42/42\) display delimiters.  No blocker remains.
