# Review of Fin4 minimum-law singleton clock compression

Reviewer: Codex Root

## Claim reviewed

A positive singleton mass in an actual quitting profile is a subprobability
average of the opponent-survival masses exposed by forcing the singleton owner
to Continue until one deterministic date and Quit there.  Applied after the
deep exact cap prefixes of a minimum-law causal source, this is claimed to
produce cofinally many actual concentrated-singleton endpoints with a fixed
stage-mass floor and literal prefix/tail provenance.

## Verdict

The mathematical claim passes, with one required interface correction and one
useful quantitative strengthening.

The correction is that the new origin does not carry the
`FinFourLowTailRow` certificate possessed by the two current nonsingleton
origins.  It may enter a refactored common concentrated endpoint containing the
actual profile, marked stage, singleton, fixed floor, source provenance, and
post-stage live-root equality.  It may not be inserted into the current
inductive by pretending to construct its `low` field.

The strengthening is that the standard `mu^2/8` floor is not intrinsic.  Once
the exact cap-stack Continue product is retained, every fixed `lambda < mu` is
eventually achievable.

## Verification

For the owner `j`, its first finite stopping-time masses

\[
\alpha_t=\prod_{s<t}(1-q_j(s))q_j(t)
\]

have total mass at most one.  Independence at the unique live history gives

\[
\Pr(Q=\{j\}\text{ at }t)=\alpha_t s_t,
\]

where `s_t` is opponent survival through `t`.  A forced Continue-then-Quit
replacement exposes stage mass exactly `s_t`.  Hence

\[
\sum_t\alpha_t s_t>\lambda
\]

forces some `s_t>lambda`.  This argument remains valid for arbitrary
behavioral profiles: before absorption a quitting game has only the canonical
all-Continue public history, and the replacement is one legal complete
behavioral strategy.  Restoring the owner's source live roots after the forced
date gives literal post-date tail equality, although that tail is off path in
the target.

For a retained anchor `a`, the source prefix survival—including the owner's
survival before `a`—belongs in `s_{a,t}`.  With that factor included, the
anchored identity is correct and the target leaves the full earlier cap stack
unchanged.

For the minimum-law application, joint law convergence gives suffix singleton
mass tending to `mu`.  The checked theorem
`QuittingNonsingletonMinimumLawTransfer.tendsto_capNashStackContinueProduct_one`
gives prefix Continue product tending to one; its proof does not require the
selected atom to be nonsingleton.  Thus the after-prefix singleton mass tends
to `mu`, and the anchored lemma gives the claimed cofinal endpoint family for
every fixed `lambda < mu`.  The target has the same literal root word before
the anchor.  The cap-Nash certificate remains a certificate about the
original source; changing the suffix can change opponents' caps, so no
exact-stack claim is made for the target.

## Falsification checks

1. **Diffuse owner clock.**  If the owner chooses uniformly among `N` dates
   and all opponents Never quit, every original singleton stage mass is
   `1/N`, while every exposed survivor mass is one.  The theorem succeeds and
   does not rely on a hidden concentration premise.
2. **Opponent hazard.**  Since `s_t` is nonincreasing, its value at the first
   positive owner stopping atom dominates every later positively weighted
   value.  This gives the stronger attained bound `s_t >= m/A >= m`.
3. **Never mass.**  The owner's Never probability merely makes
   `sum alpha_t < 1` and strengthens the averaging inequality.
4. **Behavioral deviations.**  Only the owner's complete strategy is
   replaced.  Opponent strategies and their behavior at every live history
   are unchanged.
5. **Source prefix.**  Compressing the suffix first and then applying the same
   literal root word multiplies its singleton mass by the source stack
   Continue product and avoids choosing a compression date inside that word.
   The original source stack remains exactly cap-Nash.  The copied word is not
   asserted cap-Nash against the compressed suffix.

No counterexample to the stated concentration result was found.

## Source and scope audit

The result is not the nonsingleton anti-diffusion theorem: it does not find a
large atom in the original chronology.  At the first supported owner date,
the earlier owner hazards are already zero, so the existing literal one-date
profile is sufficient; no finite interval splice is needed.

The result answers the first accepted arm of
`questions/FIN4_ATLAS_DIFFUSE_MINIMUM_SINGLETON.md`.  It does not answer
`questions/FIN4_ATLAS_CONCENTRATED_SINGLETON.md`, and it supplies no low-tail,
debt, or Nash certificate for the compressed endpoint.

## Post-review strengthening

Independent strengthening and adversarial review proved the sharp bound
`exposedMass >= m / A >= m` at the first supported owner date.  The export
gate also confirmed that no current downstream consumer depends on a
universal `low` projection.  The strengthened result is approved for export.
