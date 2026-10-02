# Fin4 minimum-law singleton clock compression

Author: ChatGPT External

## Current status

The scalar compression theorem and its source-anchored atlas application are
mathematically proved below.  The result answers the concentration arm of
`questions/FIN4_ATLAS_DIFFUSE_MINIMUM_SINGLETON.md`: a positive singleton atom
of the selected minimum law produces a cofinal family of actual concentrated
singleton endpoints with one fixed stage-mass floor.

Subsequent independent review sharpened the construction: choosing the first
positive owner stopping atom after the anchor exposes at least the entire
anchored singleton mass with the existing literal one-date Quit update.  The
reviewed final statement is
[`FIN4_MINIMUM_SINGLETON_CLOCK_COMPRESSION.md`](../exports/FIN4_MINIMUM_SINGLETON_CLOCK_COMPRESSION.md).
The averaging theorem below remains valid but is weaker.

One interface qualification is essential.  The compressed origin carries the
actual minimum-law source with its exact cap-prefix certificate, a target
whose earlier root word is literally unchanged, the concentrated stage, and
literal post-stage tail equality.  Exactness of that prefix is asserted for
the original source, not automatically for the compressed target, whose
continuation caps may change.  The compressed origin also does **not** inherit the
`FinFourLowTailRow` certificate currently stored by the two nonsingleton
origins of `FinFourAtlasConcentratedSingletonEndpoint`.  A common endpoint
interface must therefore expose only the genuinely common endpoint fields and
retain low-tail data inside the old origin tags.  No low-tail inequality is
claimed for the new origin.

## Generic compression theorem

Let `I` be finite, let `sigma` be a behavioral profile in a quitting game, and
fix a player `j`.  On the unique live history at date `t`, write

\[
q_i(t)=\Pr(i\text{ Quits}),\qquad c_i(t)=1-q_i(t).
\]

Define the mass of `j`'s own first finite stopping time at `t` by

\[
\alpha_t=\left(\prod_{s<t}c_j(s)\right)q_j(t),
\]

and define the probability that all opponents survive through date `t` by

\[
s_t=\prod_{i\ne j}\prod_{r\le t}c_i(r).
\]

Then

\[
\sum_{t\ge0}\alpha_t\le1
\]

and the terminal-law mass of the singleton coalition `{j}` is

\[
m_j(\sigma)=\sum_{t\ge0}\alpha_t s_t.
\tag{1}
\]

For a date `t`, define `Compress(sigma,j,t)` by retaining every opponent's
complete behavioral strategy, making `j` Continue before `t`, making `j` Quit
surely at `t`, and restoring `j`'s original live-root strategy strictly after
`t`.  Then

\[
\Pr_{\operatorname{Compress}(\sigma,j,t)}
  (\text{terminal at }t\text{ is }\{j\})=s_t,
\tag{2}
\]

and for every offset `r`,

\[
\operatorname{root}_{\operatorname{Compress}(\sigma,j,t)}(t+1+r)
=\operatorname{root}_{\sigma}(t+1+r).
\tag{3}
\]

Consequently, for every real `0 <= lambda < m_j(sigma)`, there is an actual date
`t` such that the stage mass in (2) is strictly greater than `lambda`.

### Proof

The finite partial sums of `alpha` telescope:

\[
\sum_{t=0}^{T}\alpha_t=1-\prod_{s=0}^{T}c_j(s)\le1.
\]

Independence of the behavioral randomizations on the live history gives stage
singleton mass `alpha_t s_t`; summing over the disjoint terminal dates proves
(1).  Under the compressed profile, the owner survives surely before `t` and
Quits surely at `t`, while the opponents are unchanged, proving (2).  The
definition gives (3).

If every `s_t` on the positive support of `alpha_t` were at most `lambda`,
then

\[
m_j(\sigma)=\sum_t\alpha_t s_t
\le \lambda\sum_t\alpha_t\le\lambda,
\]

contradicting `lambda < m_j(sigma)`.

This is not a large-atom selection from the original chronology.  The
possibly diffuse factor is `alpha_t`; the unilateral replacement removes it.

## Anchored form

Fix an anchor date `a`.  Preserve the source before `a`, force `j` to Continue
on `[a,t)`, force `j` to Quit at `t`, and restore the source after `t`.  Put

\[
\alpha_{a,t}=\left(\prod_{r=a}^{t-1}c_j(r)\right)q_j(t)
\]

and

\[
s_{a,t}=\left(\prod_{r<a}\prod_i c_i(r)\right)
          \left(\prod_{r=a}^{t}\prod_{i\ne j}c_i(r)\right).
\]

The source singleton mass occurring at or after `a` is

\[
m_j^{\ge a}(\sigma)=\sum_{t\ge a}\alpha_{a,t}s_{a,t},
\qquad \sum_{t\ge a}\alpha_{a,t}\le1.
\]

Hence, if `lambda < m_j^{>=a}(sigma)`, some `t >= a` has anchored compressed
stage mass `s_{a,t} > lambda`.  The target agrees with the source before `a`
and strictly after `t`.

More sharply, let `t_0` be the least date with positive
`alpha_{a,t_0}` and put `A_a = sum_t alpha_{a,t}`.  The survivor factors
`s_{a,t}` are nonincreasing, so

\[
m_j^{\ge a}(\sigma)\le A_a s_{a,t_0}.
\]

Minimality of `t_0` implies that the owner already Continues surely on every
live row in `[a,t_0)`.  Therefore changing only its action at `t_0` to Quit
surely exposes stage mass

\[
s_{a,t_0}\ge m_j^{\ge a}(\sigma)/A_a
\ge m_j^{\ge a}(\sigma).
\]

No interval splice is needed.

## Minimum-law atlas adapter

Let `source : FinFourMinimumAtomProducer reward bound`, suppose its selected
atom is the singleton `{j}`, and set

\[
\mu=\texttt{source.point.2 (some source.atom.terminal)}>0.
\]

Unpack `source.atom.chronology` as suffix profiles `sigma_n` and exact cap-root
stacks `roots_n`.  Joint semantic/law convergence gives

\[
m_j(\sigma_n)\longrightarrow\mu.
\tag{4}
\]

The checked cap-stack scaling argument
`QuittingNonsingletonMinimumLawTransfer.tendsto_capNashStackContinueProduct_one`
does not use nonsingleton cardinality, and gives

\[
P_n:=\operatorname{ContinueProduct}(roots_n)\longrightarrow1.
\tag{5}
\]

The singleton mass lying in the suffix of the literally prefixed profile is
exactly `P_n m_j(sigma_n)`, so it tends to `mu`.  Therefore, for **every fixed**

\[
0<\lambda<\mu,
\tag{6}
\]

all sufficiently large ranks admit an anchored compression after the entire
cap-root stack whose actual singleton stage mass is greater than `lambda`.
These targets retain:

- the same selected minimum point, law, atom, and causal source family;
- the literal root word of the source cap-prefix of length `n+1`, while the
  source record retains its exact cap-Nash certificate;
- one actual singleton stage with the common fixed floor `lambda`;
- every opponent's complete strategy;
- the source profile before the suffix anchor; and
- literal equality of the complete live-root tail strictly after the marked
  stage.

Taking

\[
\lambda=\mu^2/8
\]

recovers the standard atlas scale, since `0 < mu <= 1` implies
`mu^2/8 < mu`.

Thus the minimum-law singleton node has no residual temporal-diffusion arm:
it maps source-faithfully to a recurrent fixed-resolution singleton endpoint
family.

## Source correspondence

The relevant checked declarations are:

- `QuittingMinimumLawCausalSuffixAtom` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLawCarrierCausalization.lean`;
- `quittingTerminalOutcomeMass_eq_timeDisintegration` and
  `quittingStageCoalitionMass` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauTimeDisintegration.lean`;
- `quittingBehaviorStoppingLaw_some_toReal` in
  `UniformEquilibrium/Quitting/Paths/BehaviorStoppingLaw.lean`;
- `QuittingNonsingletonMinimumLawTransfer.tendsto_capNashStackContinueProduct_one`
  in `Research/Quitting/NonsingletonMinimumLawLinearTransfer.lean`; and
- the current two-origin common endpoint in
  `Research/Quitting/FinFourProducerAtlas/SemanticConnections.lean`.

The new mathematics is the first-supported-date domination and its anchored
composition with (4)--(5).  Minimality of the selected date shows that the
owner already Continues before it, so the existing literal one-date profile
is the correct formal target.

## Boundary tests and nonclaims

- A stopping law uniform on `N` dates shows that the original stage atoms can
  all be `1/N` while the compressed opponent-survival mass is one.  Thus the
  result genuinely bypasses, rather than disproves, singleton diffusion.
- For one actual source, exposed mass at least `m_j(sigma)` is sharp.  The
  strict inequality `lambda < mu` remains necessary only when extracting a
  uniform floor from a sequence whose masses may approach `mu` from below.
- The compressed target generally has a different terminal law and semantic
  pair from the minimum point.
- No debt, local-Nash, cap, punishment-floor, or low-tail estimate for the
  compressed target is asserted.
- The unchanged root word is not claimed to remain a cap-Nash stack against
  the compressed target's changed continuation caps.
- The result contracts the atlas by mapping the diffuse minimum-singleton
  source to the concentrated endpoint problem.  It does not consume the
  concentrated-singleton node or prove a uniform-equilibrium payoff.

## Review outcome

Independent adversarial, strengthening, and endpoint-interface reviews found
no unresolved mathematical objection.  The final corrected theorem has been
placed in `exports/`.
