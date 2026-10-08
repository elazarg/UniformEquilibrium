# Priority open mathematical questions

## Common objective

A four-player quitting game assigns a finite reward vector to every nonempty
quitting coalition. At each date the players independently choose Continue or
Quit. The first nonempty coalition ends play; infinite all-Continue pays zero.
Strategies and unilateral deviations may use arbitrary private randomization
and stopping dates, including Never.

For a profile p, let U_i(p) be its expected terminal payoff and let B_i(p)
be the supremum payoff over all behavioral replacements of player i. Put

    E(p) = max_i [B_i(p) - U_i(p)].

The positive objective is to prove, for every four-player reward table, that
inf_p E(p) = 0. Equivalently, construct one fixed uniform-equilibrium payoff:
for every positive error, choose a profile approaching that payoff and
bounding every unilateral gain at every sufficiently long finite-average
horizon. The profile and horizon threshold may depend on the error; the
payoff target may not.

A complete negative answer is one explicit table and a positive constant
gamma such that E(p) >= gamma for every behavioral profile. A bound for a
restricted strategy class is not such a counterexample.

Any mathematical route is welcome. A proof need not construct a particular
chronology, source transition, rank, or certificate language.

## Focused questions

Five questions attack the four-player problem through distinct concrete
interfaces:

1. Select finite stopping laws with vanishing unrestricted exploitability in
   the single-pivot normalization.
2. Consume a mixed first collision at a debt-rigid global minimum, retaining
   the unrestricted cap constraint on every nonzero minimum prefix.
3. Produce approximate Nash–Bellman blocks with unbounded charge, or a
   summable-error persistent spine.
4. Prove that the compact controller value is zero, or construct a positive
   closed invariant barrier.
5. Find an exact positive-gap table, or a terminating exact decision method.

Two questions address the general finite-player conjecture:

6. Compile equilibria of proper subgames into a cardinal reduction.
7. Establish or refute the implication from absorbing row-perfect witnesses
   to terminal approximate equilibria.

One finite-state source question tests a bound used in a quitting-game
structure argument:

8. Prove or refute the uniform expected-variation bound for bounded
   backward-harmonic values along a homogeneous Markov chain.

## Inclusion rule

Questions must state their game, inputs, quantifiers, and desired output
without links, repository terminology, or assumed knowledge of another
question. Keep them timeless: no audit reports, resolutions, implementation
status, or research history. Supporting facts may be stated when needed to
make the mathematical problem precise.

Only difficult conjecture-facing targets belong here. Supporting lemmas,
optional experiments, task checklists, and duplicate umbrella formulations
do not receive separate question files.
