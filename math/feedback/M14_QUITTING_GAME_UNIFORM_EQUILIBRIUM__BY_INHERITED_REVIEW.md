# M14 uniform equilibrium: independent adversarial whole-packet review

**Verdict: PASS.** There is no unresolved mathematical objection. This is a
fresh review of the entire final manuscript, including its actual-data
producer, all finite and limiting switches, unrestricted response consumer,
native absorbing limit, and inline exact certificate. Component reviews were
not treated as approval of the assembled result.

Reviewed manuscript SHA-256:
`bfcdc6f7d701f739fc86f7aa4e7e66441cf72fcbdbea6130c1242fa30a55bf0f`.
The reviewed candidate is the 619-line
`math/exports/M14_QUITTING_GAME_UNIFORM_EQUILIBRIUM.md`.
Its complete inline Python certificate has SHA-256
`94390ab21c09ae25ccc0751d277d02df25b63482841e2099a6dbbbeb1efde5b4`.
This review applies to those complete bytes.

## Claim and genuine scope

For the explicitly given 60-coordinate native M14 table, the manuscript
constructs actual finite private independent-hazard words followed by Never
whose four full native debts and joint Never probability tend to zero. Thus
the native augmented absorbing observer-exact face has minimum pivot debt
zero. For the original table obtained by adding 4 to every absorbing reward,
it constructs a fixed uniform-equilibrium payoff `4*1+b_*e2`, with
`b_* in [4/5,9/10]`. Every unilateral behavioral deviation is controlled.
The target is chosen before accuracy, and the selected finite profile works
for every sufficiently large horizon.

This is a table-specific result. It does not settle arbitrary Fin4. The
manuscript does not claim that any infinite proxy phase is an actual
continuation or that the semantic absorbing Nash limit is itself realized by
one actual profile. Neither stronger conclusion is needed.

## Complete proof audit

1. **Raw game to root equations.** The singleton, participant-pair,
   passive-multiple and participant-higher-coalition rules specify all 60
   coordinates. I checked `L=J-Gamma`, the full odds formula `C_i`, and both
   root maps. With all probabilities below one, the diagonal Nash condition
   is exactly `C_i<=v_i`, with equality at positive hazards. Both root maps
   are nonexpansive in their respective terminal annotations; the cap map is
   monotone. These statements hold even when an intermediate cap is negative.

2. **Closure of finite words.** The auxiliary carrier `H_v` consists of
   finite proxy-word outputs with fixed terminal annotation and survival
   coordinates, followed by closure. It is bounded and closed in finite
   dimension. A fixed finite prefix preserves it continuously. Successive
   limiting phases therefore compose inside this carrier. This proves
   approximability of both payoff and full cap, without requiring finite
   approximants to remain exactly Nash at phase switches. The direction of
   prepending, and the reverse chronological order of the eventual finite
   word, are consistent throughout.

3. **Singleton phases and eight atoms.** Every active value is zero in its
   singleton phase, and every quiet inequality is checked. The decreasing
   coordinate obeys `13v/(14+v)` and tends to zero. The three endpoint vectors
   and survival product `1/(1+6b)` are correct. In the owner1 segment, the
   quiet0 lower bound is `x>=a/4`, while quiet3 gives the upper bound; this
   explicitly prices the negative observer0 cap. The count is one initial
   root, six minimum roots, and one final tied root. The resulting ray is
   `lambda*(-25,0,104,65)`, with `lambda=b/(18+133b)`, and survival is
   `18/(18+133b)<=45/311`.

4. **Uniform finite return.** I checked the observer order `(0,1,3)`, the
   matrices `L0,J0,T`, the equation `C0(x)=v`, the observer output `Q0(x)`,
   the pivot output, and the quiet-pivot comparison against the full table.
   The interval scheme verifies a genuine parameter-uniform Banach self-map
   on a positive root box. It does not infer existence from a numerical
   residual. The input box is extended to include the actual nominated
   center's exact input, so every mean-value path lies in the verified
   region. The inverse-Jacobian enclosure follows from the Neumann bound;
   the observer and pivot derivatives, including the pivot's dependence on
   its own continuation value, are correct. Outward dyadic rational
   arithmetic encloses every operation. Floating computations only nominate
   rational centers and preconditioners.

5. **Tail cone.** I independently derived the bounds behind the certificate:
   `||Q0(x)-J0*x||<=41t^2<42t^2`,
   `||L0^-1||=69/379`, and `||L0^-1*J0||<26/25`. The fixed-point ball of
   radius `12t^2` is mapped strictly into itself and has contraction factor
   at most `(69/379)*20t`. The four-corner tests suffice because each cone
   margin is affine in the two ratios. They give positivity, the same cone,
   and `y1<.99t`. For the pivot, the stated `32t/5` bound is valid directly
   from `|y0+2y1-y3|<=3.7t` and `sum(y)<=2.7t` while `|beta|<=1`.
   Summation gives the remainder `640t`. The strict certified enclosure
   inside `(.849,.861)` bootstraps the bound on beta, so it is not assumed
   circularly. The pivot remains quiet at every later root. Observer values
   tend to zero, pivot values converge, and survival coordinates converge.
   This supplies one fixed returned `b'` for every input b, independent of
   subsequent approximation accuracy.

6. **Repeated approximate returns.** The words calibrated at successive
   ideal inputs may be concatenated in the stated reverse order. Errors in
   each terminal annotation accumulate by at most `K*eta`, not by word
   length, and joint survival is bounded by `(theta+eta)^K`. All component
   lengths and hazards can be selected before play. No strategy is executed
   after an infinite phase.

7. **Actual original-game consumer.** Adding 4 to every absorption reward
   and to the artificial terminal annotation adds exactly 4 to both finite
   proxy outputs. The actual postword prescribed payoff is zero and the
   full postword response cap is 4. The proxy annotation `4*1+b0*e2`
   dominates that cap coordinatewise. Therefore monotonicity gives the
   actual cap bound, while the payoff subtraction involves exactly joint
   survival. The debt bound `2K*eta+4.9*(theta+eta)^K` is correct. There is no
   missing opponent-survival term: such a term would be needed for a proxy
   below the real cap, which is not used here. The cap prices all complete
   quitting deadlines or Never; arbitrary private behavioral randomization
   cannot improve their supremum.

8. **Native gap and fixed payoff.** The actual native postword cap is zero,
   and `b0*e2` dominates it. Thus the same argument proves all native debts
   and joint Never tend to zero. Compactness of the full augmented carrier
   supplies an absorbing zero-debt point, contradicting the positive-gap
   premise at M14. The original-game target is selected by one orbit and
   one convergent subsequence before accuracy is requested. The inequalities
   give both convergence to this target and vanishing full terminal debts.

9. **Uniform horizons.** For a chosen finite word, prescribed absorption
   occurs by its final date or never. Under a unilateral deviation, any
   absorption after that date is a positive solo payment of 4; delaying it
   cannot raise a finite average above its terminal payoff. Earlier
   absorption discrepancies are uniformly bounded by `17(T+1)/H`.
   Therefore `max debt+34(T+1)/H` bounds every horizon gain. Together with
   payoff delivery this proves exactly one profile and one threshold for
   each accuracy, valid at every larger horizon.

## Independent execution and falsification attempts

I extracted the inline program from the complete manuscript, verified its
byte equality with the standalone certificate, and ran that extracted
program with its default ten tiles. Every exact prefix identity, tail-cone
inequality and all 305 steps on every tile passed. The certified outer return
range was within `[.849515451799,.860153906425]`; these printed decimals are
only a summary of the exact rational inequalities checked by the program.

The attempted failure points included negative intermediate caps, illegal
switches after infinite phases, a missing quiet-player deviation, reversed
word order, use of a numerical rather than actual root, interval transport
from the wrong center, nonuniform parameter coverage, a circular pivot
bootstrap, mistaking joint survival for opponent survival, omission of late
unilateral quitting, and choosing the payoff after accuracy. None produces
a gap in this final proof. In particular the terminal-cap majorization is
what resolves the otherwise serious joint-survival objection.

## Export admission and source boundary

There is no remaining supplied strategic witness. The raw table produces
all singleton hazards, atomic hazards, 305 certified root selections,
subsequent positive roots, semantic return endpoints and finite-word
approximants. Compact choices of an orbit and a target use objects already
proved to exist. This is a direct complete producer, so no exceptional
conditional admission is being invoked.

I checked the implementation interfaces in
`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`,
`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`,
`UniformEquilibrium/Quitting/Paths/StoppingLawOperationalDistance.lean`, and
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
The named root recursion and stopping-law/behavior declarations have the
claimed semantics. In particular
`quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto` consumes the
fixed target and actual profiles just constructed. Section6 also proves the
needed finite-horizon conclusion directly.

For conjecture-facing overlap, I reread the exact complete-criteria audit in
`math/notes/CODEX_COORDINATOR__NO_CHILD_FIN4_BENCHMARK.md`. Its relevant raw
obstructions include the singleton upper-charge sum `3*sum(w)>0`, joining
sum `3w0+2w1+w2+2w3>0`, the cycle-forced anchor contradiction `13^4>5^4`,
and a negative participant-premium endpoint in every proposed pair. These
are complete-selector failures in the identified earlier criteria, not
failure of only one attempted strategy. The existing accepted M14
finite-mode and eventual-native-Nash-tail results remain conditional
restrictions on a positive-gap source; they do not produce the zero-gap
absorbing limit or original UE now obtained. The coordinator's wider
implemented-producer overlap record remains the appropriate place for its
complete catalog. No claim that every conceivable strategy architecture
fails at M14 is needed or made.

The packet therefore eliminates the specified previously surviving table
and its entire positive-gap source obligation, rather than merely adding a
necessary local condition. I affirm its mathematical admission on that
basis. All conclusions here are ordinary mathematics with an exact finite
certificate. No new Lean theorem, compilation, or formalization seal has
been established by this review.
