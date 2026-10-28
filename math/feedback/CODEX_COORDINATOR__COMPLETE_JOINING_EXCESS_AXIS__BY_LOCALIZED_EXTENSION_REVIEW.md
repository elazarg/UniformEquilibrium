# Independent review of the negative-K localized extension

Reviewer: NASH_ITERATION. Ordinary mathematics, not Lean checked.
Reviewed exact Section8 draft: `NEGATIVE_K_LOCALIZED_EXTENSION.md`, SHA256
`13f3c1e3c4ad2522a6a1932ce5433f3df119b04b8d74c04473454dce89840c5d`.
Intended location: Section8 of
`math/notes/CODEX_COORDINATOR__COMPLETE_JOINING_EXCESS_AXIS.md`.

**Verdict: PASS on the full parametric theorem, its piecewise elimination,
the limiting equality case, and the exact negative control.** The displayed
raw region gives UE by the already reviewed localized invariant consumer.
No new strategy or continuation assumption is introduced. This is approval
of the mathematics, not an independently established coverage increment over
all other prior producers or a complete negative-K classification.

K<0 and p<=K f(beta) imply p<0. The supported-Quit exclusions for active0,
singleton supports, and each of12,13,23 are exact. For active123, I independently
reconstructed all three Quit polynomials from the coalition table. If b<=beta
and all three are positive, Q3>0 gives y>100b/(10+91b). The endpoint cases
z=0 and z=1 are impossible. Since y/(3-y) is strictly increasing on(0,1),
Q2>0 yields the stated strict lower bound on the odds of z, and Q1>0 yields
its strict upper bound. Every divided quantity is positive because
beta<100/111. Canceling b gives

    (-p)/(-K) < f(b) <= f(beta),
    f(b)=(30+173b)/(100(100-111b)),

contradicting the weak raw p bound, including equality. The derivative
2063/[10(100-111b)^2] is exact. Thus b>beta. Since beta>3/4, the interval
3<V<beta/(1-beta) is nonempty. All four passive row0 corners are strictly
negative for b>beta under R<=3-3/beta. The first is negative because
V-(V+1)beta<0; the second is nonpositive at beta and decreases strictly;
the last two are already negative at3/4. Bilinear interpolation therefore
proves the required nonpositive-output property.

R<=3-3/beta<-33/100 ensures every row0 reward is at most3. The domain u0<V
and every fixed-seed strict interior bound are consequently preserved by
arbitrary prefixes. The previously proved local-escape induction and actual
least-Never minimum apply without modification and give native absorbing
debt infimum zero. The nonnegative-own-level consumer yields one fixed
original uniform-equilibrium payoff.

The elimination of beta is correct. For -1<R<-33/100,

    beta=3/(3-R) in(3/4,100/111),
    f(beta)=(609-30R)/(100(-33-100R)).

For R<=-1 and p<K639/6700, division by negative K gives
p/K>f(3/4)=639/6700. Continuity and strict monotonicity allow a beta slightly
above3/4 satisfying p/K>=f(beta), while R<=3-3/beta automatically holds.
At equality p=K639/6700, decreasing only p by epsilon supplies the strict
case. Only player2's reward function changes; its prescribed payoff and
its full response cap change by at most epsilon each for the identical
profile. Thus TOTAL native debt changes by at most2epsilon, not8epsilon.
The prescribed profile still absorbs surely, so the limit gives A_Z=0 and
the claimed fixed-target original conclusion. No equilibrium-payoff target
is transported between different games without the terminal-error argument.

I independently checked the p=0 negative control by exact fraction arithmetic.
The active players1,2,3 have equal Quit and Continue offers at the displayed
input. Quiet0 has Quit offer -1507237/1250000, strictly below its Continue
value429991/500000. The full output is exactly

    (429991/500000,6443/400000,3/12500,73/50).

It is strictly positive, while the input has v1<0 and every input coordinate
lies within its literal row reward range. This is a valid bounded-domain
invariant failure when the p restriction is discarded, not a no-UE example
or proof that the sufficient function F is sharp. I also inspected the
retained checker's added exact ratio identities and this control; they match
the mathematical statements.

The parameters eta,t do not enter the invariant calculations, so their
unrestricted finite range is justified. Negative own offsets are correctly
excluded from the invoked consumer. No Lean command or tracked edit was made.
