# Compile the source-preserving Fin4 residual into an executable program

## Mathematical data

Let $r$ be a bounded four-player quitting reward table and suppose

\[
D_*:=\inf_\sigma\sum_i
\bigl(B_i(\sigma)-U_i(\sigma)\bigr)>0,
\]

where every $B_i$ ranges over all behavioral unilateral replacements,
including Never and arbitrarily late quitting.

Use as supplied the source-preserving Fin4 reduction. On its nonterminal
output it gives one fixed
actual source chronology and a cofinal forced-pair stream with fixed roles, a
positive marked-mass floor, a positive paid-endpoint floor, exact mover-debt
subtraction, and literal preservation of the complete post-row tail. Exactly
one of two terminal components occurs.

1. **Uniform escape:** the literal post-row tail debt stays at least
   $D_*+\delta$ for one fixed $\delta>0$.
2. **Minimum return:** the literal post-row tail debt converges to $D_*$.

The existing branch reductions may be used, including the same-tail exact-root
dispatch in uniform escape and the normalized-return, support-handoff, and
strict-inert or scalar-ray-stall dispatches in minimum return. They are
supplied conditional reductions, not terminal consumers.

## Question

Construct one finite proof-relevant program schema which realizes every
non-elementary transition used to consume these two components.

Finiteness refers to the list of operation and branch types, not to the
cardinality of the source-state space or to a previously classified finite
graph of recurrent components.

Every transition which remains visible while a compact execution limit is
taken must be supplied in one of the following forms:

1. a compact recorded witness, a closed legal-operation relation, and a
   continuous compiler to an actual behavioral source;
2. a finite approximation decoder with explicit reach, payoff, cap,
   stopping-law, and summable error budgets, together with a closed ancestry
   relation; or
3. a finite tagged case or ranked transition whose complete terminal and
   successor branch relations are closed and whose child and backward maps are
   themselves executable.

A well-founded transition may instead be applied after one actual limiting
source has been reconstructed. In that case it must provide an actual child,
a strict natural-valued rank decrease, a backward compiler, and a consumer for
every terminal certificate. Such a pointwise rank argument is not itself a
transition in the compact trace.

For each accuracy, construct a finite execution of this program from the given
source chronology. The executions must be compatible under restriction and
must not promote escaped stopping mass to an actual source. At every initial
or exogenous port which persists through a compact execution limit, prove
finite-coordinate and Never-coordinate convergence together with a common
finite-tail tightness envelope, or discharge the escape defect by an explicit
summable decoder before treating the output as actual. Persistent suffix
operations must retain positive reach; moving witnesses and finite branch
labels must admit common convergent subsequences; and every triangular decoder
must have fixed-column convergence and a uniform summable tail bound.

Prove that the coherent limit is one actual behavioral construction and yields
at least one of:

- terminal approximate Nash profiles whose errors tend to zero against every
  behavioral deviation and whose payoffs converge to one fixed vector;
- actual source-attached finite chronologies whose start and end prescribed
  payoffs, unrestricted caps, retained terminal laws, and required
  deleted-player laws converge to one target packet, and whose cumulative
  admissible payoff charge has one fixed positive lower bound;
- a renewable finite rank which strictly decreases along every recursive edge
  and whose terminal states all have uniform-payoff consumers; or
- one explicit four-player table and one $\gamma>0$ for which every behavioral
  profile admits a unilateral gain of at least $\gamma$.

## Required Fin4 adapter checks

The proof must resolve the following operations wherever it uses them:

- exact-root selection in the uniform-escape component, without assuming that
  maximal absorption among exact roots is a closed selection rule;
- moving-law minimization and actualization in the minimum-return component,
  without identifying a compact carrier point with an attained behavioral
  source;
- source regeneration at a returned endpoint, with the selected child and
  backward map retained;
- every suffix operation whose reach can vary along the compactifying
  sequence; and
- every recursive support or phase transition, with a rank that cannot be
  reset by regeneration.

## Acceptable partial answers

A complete answer for exactly one terminal component is useful if it consumes
that component or replaces it by a strictly smaller source-attached
obligation with an actual-data adapter and a terminal or renewable-rank
consumer.

For one precisely specified operation and adapter class, an exact
source-attached impossibility theorem is useful if it states which stronger
passport, post-limit control, or alternative construction remains possible.

## Nonanswers

- reproducing the uniform-escape/minimum-return split;
- giving the abstract executable grammar without adapters for the operations
  actually used in the Fin4 residual;
- treating maximality among exact roots as a closed graph without a
  comparison-transport proof;
- calling a vanishing-reach conditional suffix the successor of its limiting
  source;
- inserting a pointwise support-rank child into the compact trace without a
  closed selected-child or decoder theorem;
- choosing unrelated behavioral realizations at successive depths;
- another unconsumed endpoint, ray, inert state, or recurrent component; or
- control only of stationary, finite-horizon, or bounded-memory deviations.
