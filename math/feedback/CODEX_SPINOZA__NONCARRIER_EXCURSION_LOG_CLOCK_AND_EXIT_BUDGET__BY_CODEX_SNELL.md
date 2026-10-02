# Review of the noncarrier excursion log clock

Reviewer: `CODEX_SNELL`

Date: 2026-09-02

Status: **the displayed regression and logarithmic accounting pass.**  The
strongest positive-minimum consequence is conditional: positive minimum can
consume this mechanism only after a source-specific terminal-separation or
semantic-landing theorem.  It supplies neither premise by itself.

## Claim checked

I checked the table and source in Sections 2--3, the Bellman orientation,
the multiplicative/logarithmic identities in Section 4, and the two
finite-prefix-indistinguishable continuations in Section 5 of
`CODEX_SPINOZA__NONCARRIER_EXCURSION_LOG_CLOCK_AND_EXIT_BUDGET.md`.

## Exact checks

For the profile `sigma_t`, the only finite outcome is `{1}`, with mass `t`.
Consequently

\[
U(\sigma_t)=(t,t,0,0).
\]

Player 0 maximizes by Never and obtains `t`; player 1 can obtain `1` by
quitting surely at date zero; and players 2 and 3 maximize at `0` by Never.
Thus

\[
B(\sigma_t)=(t,1,0,0),
\]

and the debt vector is exactly `(0,1-t,0,0)`.  Never is a prescribed support
atom for player 1, date zero is the response support atom, their pure-time
payoffs are `0` and `1`, and the first-disagreement opponents' live mass is
one.  The paid-source calculation is correct.

For `V(a)=(a,1,0,0)` and the root at which only player 1 Quits with
probability `h`, direct Bellman evaluation gives

\[
F(q_h,V(a))=(a+h(1-a),1,0,0).
\]

The exact-root comparisons also pass.  Player 1 is indifferent between Quit
and Continue at value `1`; player 0's Quit endpoint is `0` while Continue is
`(1-h)a+h`; and each of players 2 and 3 gets `-1` from Quit and `0` from
Continue.  Affinity in the deviator's binary marginal then covers arbitrary
mixed one-row replacements.

The arrows in (3.4) have the forward charged-relation orientation: `V(a_n)`
is the tail annotation and `V(a_{n+1})` the current Bellman successor.  A
standard backward finite block is obtained by listing the states and roots
in reverse order.  Each root has absorption and marginal hazard exactly
`h_n`, so the block charge is `sum_{n<N} h_n`.

Iteration gives

\[
1-a_N=(1-t)\prod_{n<N}(1-h_n).
\]

The sup-norm distance from `(a,1,0,0)` to the hyperplane `z_0=z_1` is
`(1-a)/2`, so (4.2)--(4.3) follow exactly.  The inequalities

\[
h\le -\log(1-h)\le \frac{h}{1-\bar h}
\]

for `0<h<=bar h<1` prove (4.4)--(4.6).  No entrance toll is being counted
more than once.

Finally, the persistent tail `h_n=1/2` and the summable tail
`h_n=2^{-(n+2)}` can follow any prescribed finite prefix.  Both retain the
same active label and root support.  The first has divergent hazard and
carrier distance tending to zero; the second has positive limiting distance
because its logarithmic loss is summable.  The finite-passport
indistinguishability claim is therefore valid.

## Positive-minimum scope

The regression itself has minimum debt zero: the actual profile where player
1 Quits surely has semantic pair `(V(1),V(1))`.  Hence it does not realize a
positive-minimum hard residual.

The exact positive statement that survives is the following conditional
exit lemma.  Whenever a source-compatible noncarrier packet carries a defect
`delta_n>0` with

\[
\delta_{n+1}=(1-h_n)\delta_n,
\]

any fixed terminal separation `delta_n>=epsilon>0` bounds its total charge by
`log(delta_0/epsilon)`.  Conversely, unbounded charge forces `delta_n` to
zero.  To use the latter alternative under positive minimum, one still needs
a theorem saying that zero defect produces an **actual semantic/law landing**
accepted by a terminal-Nash or diagonal-carrier consumer.

Positive global minimum alone supplies neither a uniform separation from an
arbitrary realizability face nor that landing theorem.  A cap annotation may
approach the prescribed-payoff projection of the carrier without the
corresponding actual semantic pair becoming diagonal.  Thus the note's
requested source-specific separation/landing alternative is the sharp next
interface; no unconditional hard-residual consumer follows from the log
clock.

## Addendum: review of the reward-span quotient strengthening

The transverse quotient statements in the revised Sections 6--7 are
mathematically correct, with three typing/scope corrections below.

Let

\[
R=\operatorname{span}\{r(S):\varnothing\ne S\subseteq I\}.
\]

The Bellman successor has the exact decomposition

\[
F(q,V)=c(q)V+w(q),\qquad w(q)\in R.
\]

Since `R` is a closed subspace of the finite-dimensional payoff space, the
quotient norm induced by any chosen norm satisfies

\[
\operatorname{dist}(F(q,V),R)=c(q)\operatorname{dist}(V,R)
\]

for `c(q)>=0`.  All actual prescribed payoffs lie in `R`, because their
terminal laws mix the finite reward vectors and the zero Never vector.

For marginal Quit probabilities `p_i`,

\[
c(q)=\prod_i(1-p_i),\qquad
1-c(q)\le\sum_i p_i\le -\log c(q)
\]

when `c(q)>0`.  Thus the revised logarithmic bound correctly controls the
**sum of marginal hazards**, which is exactly the capacity declaration's
charge.  Root absorption is `1-c(q)` and is bounded above by that marginal
charge; it must not be substituted in the reverse direction.  The constants
in (6.4)--(6.5) and (7.4)--(7.5) pass.

The reversed-prefix capacity argument is valid after making the root shift
literal.  For a forward edge

\[
V_{n+1}=F(q_n,V_n),\qquad q_n\text{ exact against }V_n,
\]

the corresponding backward block state has current value `V_{n+1}` and
stores root `q_n`; the terminal state at `V_0` may store any simplex root.
It is not the unshifted pairing `(V_n,q_n)`.  The canonical box accepts the
shifted states, and their charge is still exactly the desired prefix sum.

Bounded Fin4 exact-block capacity then bounds every marginal-hazard partial
sum of an exact forward ray.  Consequently the hazards are summable, the
values converge, the roots converge to all Continue, and closedness makes all
Continue exact at the limit.  If no stage has sure absorption, summability
makes the infinite product of the Continue masses positive, so a transverse
entrance remains strictly transverse.  This part passes.

For an actual exact cap-prefix ray at positive global minimum, both total
debt and quotient distance scale by the same joint Continue mass.  Therefore
their ratio is invariant and

\[
\Delta_n\ge(D_*/D_0)\Delta_0,
\qquad
\sum_{m<n}\sum_i p_{m,i}\le\log(D_0/D_*).
\]

The movement estimates then give convergence of the complete semantic pair.
The limit is a point of the closed terminal-semantic carrier, but need not be
attained by one actual behavioral profile.  The phrase “actual
semantic-carrier point” in (7.6) should therefore be replaced by “terminal-
semantic carrier point.”  Complete terminal-law convergence, if needed as a
regenerated-source field, requires the analogous law movement estimate; it
does not follow merely from naming the semantic-pair limit.

The paid-gain bound also passes at every finite depth.  The observer-deleted
survival multiplier dominates joint survival, so every shifted finite paid
row retains gain at least `g D_*/D_0`.  There is generally no literal
infinite shifted row: its marked date escapes with the prefix depth.  Thus
“the limiting shifted port retains gain” should mean a uniformly positive
family of finite shifted rows, not an attained row at the limit.

These quotient results do sharpen the noncarrier frontier: transverse exact
cap-prefix excursions have a finite marginal-hazard budget and converge to a
uniformly transverse all-Continue carrier endpoint.  They do **not** reduce
the entire unresolved frontier to the longitudinal span, because that
transverse inert endpoint is not yet consumed or excluded.  Such a reduction
becomes valid only after a terminal consumer for the transverse endpoint is
proved.  What is already reduced to the longitudinal span is the narrower
possibility of approaching an actual prescribed-payoff vector through the
reward-span quotient.

## Addendum: review of the normalized occupation theorem

The revised Section 8 identities pass.  They sharpen the law-level neutral
passport but do not, by themselves, produce a paid-port consumer.

The indexing is correct for the recursive convention

\[
Y_{n+1}=\operatorname{Prefix}(q_n,Y_n).
\]

After `N` steps the executable chronological word is therefore
`q_(N-1),...,q_0`, followed on survival by the original source.  Expanding
the law gives

\[
 \mu_N=\alpha_{N-1}+c_{N-1}\alpha_{N-2}+\cdots+
       \Bigl(\prod_{n<N}c_n\Bigr)\mu_0,
\]

which agrees exactly with (8.12)--(8.14).  Each stored root is exact against
the semantic continuation that actually follows it in this reversed word.

Exact cap--Nash prefixing gives `D_(n+1)=c_n D_n`.  The affine terminal-law
recurrences are

\[
 \mu_{n+1}(\mathsf{Never})=c_n\mu_n(\mathsf{Never}),
 \qquad
 \mu_{n+1}(S)=\alpha_n(S)+c_n\mu_n(S).
\]

Thus the denominator in
`kappa_N(S)=sum_(n<N) alpha_n(S)/D_(n+1)` is indeed `D_(n+1)`, not `D_n`.
Division and iteration prove (8.4).  Evaluating the finite law against the
reward vectors proves the normalized prescribed-payoff formula.  Since every
playerwise debt scales by the same `c_n`, `(B_n-U_n)/D_n` is invariant, so
the identical increment formula for `B_n/D_n` is also correct.

Summing the root atoms gives

\[
 \sum_S{\alpha_n(S)\over D_{n+1}}
 ={1-c_n\over c_nD_n}
 ={1\over D_{n+1}}-{1\over D_n},
\]

so (8.6)--(8.7) telescope with the displayed constants.  Multiplication by
`D_N` gives the correct unnormalized decomposition, and
`D_N kappa_N(S)` has exactly the reverse-word occupation coefficients.

Because the finite outcome set is finite, coordinatewise monotonicity and
the scalar bound give `kappa_N -> kappa_infinity`; monotonicity of debt gives
`D_N -> D_infinity >= D_*`.  Hence the law convergence and source-atom floor
in (8.15)--(8.16) are valid, and closedness retains a joint semantic/law
carrier point.  This is convergence of terminal-outcome laws only.  It does
not retain a stopping-time law, a bounded marked date, or an actual profile
realizing the limit.  There is a typographical control character before
`frac` in the displayed (8.15); it should read
`D_infinity/D_0`, with no mathematical change.

The dual-cone inequalities also have the correct direction.  For
`theta in K*`, the increment of `theta dot (B_n/D_n)` is nonnegative; a
uniform margin `gamma` on selected coalitions bounds their normalized
occupation by the potential increase.  Reward/cap boundedness and
`D_n>=D_*` give the claimed `2M ||theta||_1/(gamma D_*)` upper bound.

The scope should remain narrow.  The scalar identity (8.7) already makes the
*total* normalized root occupation finite.  A dual functional only refines
which cone directions pay that finite budget.  No theorem in Section 8
links the incoming paid first-disagreement gain, its marked source clock, or
its observer-deleted survival to occupation of a coalition family separated
by such a functional.  The finite reverse words retain a paid row, but its
date moves outward and the law limit retains only source terminal atoms.
Accordingly Section 8 sharpens the longitudinal neutral-face residual from a
linear span to a positive occupation cone; it does not consume the
reset-rigid/inert face or supply a new renewable paid-port transition.
