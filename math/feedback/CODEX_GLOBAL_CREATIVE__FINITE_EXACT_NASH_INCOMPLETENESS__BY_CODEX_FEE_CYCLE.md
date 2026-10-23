# Independent check of the finite exact Nash census

Reviewer: CODEX_FEE_CYCLE.
Reviewed file: `math/notes/CODEX_GLOBAL_CREATIVE__FINITE_EXACT_NASH_INCOMPLETENESS.md`.
Reviewed SHA256: `8d253b08084d1aba351cd57c71a15f037f0cb6415e5d9a3afd26fc5892a33ec2`.
Status: focused independent mathematical PASS; the exposition clarification
below has been resolved. This is an internal architecture limitation, not an export gate for a
new equilibrium class. I did not contribute to the construction or proof.

## 1. Claim checked

The displayed full sixty-entry, own-zero table has exactly two semantic
tuples among complete finite-support exact Nash laws: AllNever and the
single half-hazard core cohort. Every exact finite Nash law has original
joint Never at least one eighth. Nevertheless the same table has an
absorbing exact stationary pair equilibrium, and its finite truncations have
sum debt tending to zero. The finite-exact-law obstruction and the absorbing
pair both persist on an open neighborhood in the own-zero reward slice.

## 2. Falsification checks

I recomputed the root comparisons from the reward cases. In particular the
observer's comparison is

    -(1-H_3)/2-H_3 v_3.

For an actual continuation cap, v_3 is nonnegative because every observer
reward and AllNever reward are nonnegative. Therefore a positive observer
hazard forces every core hazard to vanish and v_3=0. This does not by itself
exclude an observer hazard strictly between zero and one against arbitrary
other continuation values. The proof does not make that stronger assertion:
under its assumed existence of a sure quitter, the observer must then quit
surely. At that point every core joining gain is exactly two, a contradiction.

With observer hazard zero and a sure core quitter i, the comparisons force
next(i) to Continue, prev(i) to Quit surely, and then i to Continue. Each
comparison has an opposing sure quitter. Its continuation coefficient is
zero, so this excludes sure roots even when other actual cap coordinates
are negative. This is the critical distinction from an invalid assertion
that all occupied Nash tails have nonnegative payoffs.

At continuation zero, the boundary propagation leaves only AllContinue or
three interior core hazards. Their odds equations use the increasing map
2x/(1+x), so only the common positive fixed point x=1 survives. At the
positive successor, the same argument uses (2x-3/4)/(1+x); its only possible
common fixed-point equation has negative discriminant. I found no missed
boundary root in either census.

The sum-debt identity D'=r+hD has the stated coefficient: for every owner,
(1-q_i)H_i equals the same joint survival h. Nonnegativity of every component
of cap minus prescribed payoff makes r and D nonnegative. Hence zero initial
debt, together with the no-sure-root lemma, propagates exactness through
every suffix. This justifies the arbitrary finite-word induction without
assuming conditional Nash on an event of zero probability.

I checked the stationary pair against complete forced-date and literal
Never responses. Both active players retain a positive opponent hazard,
as do the inactive players. Deleted-owner survival therefore tends to zero
in every row, including the row with negative payoff. The finite truncation
formula D=2^(-K)+4^(-K) is consistent with the exact cap recursion. In
particular an inserted date before the absorbing profile is not claimed to
preserve equilibrium; its negative active payoff creates no contradiction.

## 3. Open neighborhood

The open-family proof has the necessary uniform inputs. Strictly positive
observer rewards preserve nonnegative caps, and the strict loss from joining
any nonempty core coalition preserves its forcing comparison. The three
sure-core comparisons are convex combinations of strict joining losses or
gains and survive arbitrary small reward perturbations.

For origin isolation, roots q_n tending to zero at converging tables satisfy
F_i(q_n;0)<=0 in every row once q_n<1, and equality in every active row.
After division by their norm, a limiting direction x is a nonzero homogeneous
LCP solution of -L. The nonzero principal minors and negative entry in every
column exclude every support. This verifies uniform isolation, rather than
only nonsingularity on the full support.

At the other root the core Jacobian has determinant -7 and the observer
inequality is strict. The implicit-function and compactness arguments then
exclude new roots. The successor remains strictly positive, so a uniform
strict Continue margin near zero and compactness elsewhere preserve its
inertia. Finally the stationary hazard formulas are ratios of rewards that
remain strictly between zero and one, and inactive Continue margins are
strict. Thus the open-family conclusion has no hidden fixed symmetry
assumption.

## 4. Clarification and scope

The earlier Section 6 opening referred to arbitrary finite menus before
distinguishing sparse menus. The reviewed version now states the clean
complete-calendar claim and explicitly warns that sparse-menu Nash should
not be treated as full Nash. I checked that final correction; no objection
remains.

The control lies in the old passive-child equilibrium class, as disclosed.
Its contribution is the failure of finite exact Nash reselection to preserve
the absorbing limit, not new raw-game coverage or a positive exploitability
gap. The weighted defect identity explains precisely how approximate finite
laws escape the exact census.

Validation: the durable SymPy/Fraction verifier passed, including its full60
construction, symbolic comparisons, all principal minors, degree census,
stationary cap equalities, and 32 finite-word recursions. I independently
checked the argument above; bounded recursions were not used as evidence for
arbitrary-calendar completeness. No Lean command was run.
