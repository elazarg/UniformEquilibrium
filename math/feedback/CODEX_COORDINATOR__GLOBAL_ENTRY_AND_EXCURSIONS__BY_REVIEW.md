# Whole-artifact review of the global entry and excursion note

Reviewer: JOINING_COMPLEMENT. Ordinary mathematical review, no Lean build.
I reviewed the complete canonical artifact, including the final root-to-actual
profile argument. I independently checked the original weighted-drift and
axis-obstruction proofs. I suggested the seven-sign generalization of the
face-root corollary, so this review does not claim independence of authorship
for that strengthening. No unrestricted UE claim or export admission is
being reviewed.

Artifact:
`math/notes/CODEX_COORDINATOR__GLOBAL_ENTRY_AND_EXCURSIONS.md`

SHA256:
`71c5160bf78b4a4df48192381c0480ca4d74b03cd787240cad2574317c26fc80`

Verdict: PASS for every stated mathematical conclusion. No unresolved
mathematical objection remains. The note correctly distinguishes a raw
absorbing-root producer and an actual finite native Nash profile from an
absorbing equilibrium or a recurrent strategy construction for original
games with different own levels.

## Weighted drift and closure

The singleton normalization ell Gamma=1^T and the finite lower bound-K on
weighted nonsingleton rewards give

 ell(v'-v)>=p(1-ell v)-(K+1)eta,
 eta<=6 delta p.

Thus the displayed delta gives the claimed p/4 increment whenever
ell v<=1/4. No nonnegativity of ell and no Nash assumption are needed.
The summable-absorption and positive-survival conclusions follow.

The explicit logarithmic estimate is correctly oriented:
log c>=-(1-c)/cmin and sum(1-c)<=4 ell(v_out-v_in) imply

 log nu>=-4 ell(v_out-v_in)/cmin.

Its uniform endpoint bound passes to finite-word closures and composes
across phases. The note explicitly retains bounds on intermediate
annotations and roots, avoiding an unjustified inference from endpoints
alone. The axis-return drift and impossibility of a bounded invariant
family with uniformly positive absorption follow because ell_p>0.

## The exact small-root trap

The higher joining-term bounds hold uniformly for every finite completion.
The pair and triple monomial estimates give the stated C0 inequality, and
x0=0 gives the stated C1 inequality. At p=0 the separate L10 and L31
arguments correctly exclude active0 and active1; these boundary checks are
essential. L32>0 then excludes active2.

The only remaining proper roots are singleton3 roots, constrained by
L23*x3<=beta. Their update preserves the displayed curve and keeps beta>0
at finite stages because L23>1. Its closed endpoint is all-Continue only.
The curve is closed and invariant under admitted roots; successive limits
and restarting finite words therefore remain trapped. This does not assume
play after an infinite date or exclude sure-quitter moves.

## Uniform finite-amplitude roots

At the perturbed continuation v3=-epsilon, a root with every hazard<=rho
would be proper, have every odds<=delta, and satisfy the same eliminations.
Its player3 comparison then contradicts C3=L32*x2>=0. Therefore finite
Nash existence supplies a root outside the small cube. Compactness of the
mixed-action cube and closed Nash inequalities give an original exact root
with max q>=rho. The bound depends only on raw rewards, not the continuation
parameters. The broader face proof uses precisely the stated seven signs.
No positive absorption, support, or equilibrium witness is supplied as input.

The sure singleton3 possibility in the benchmark departure claim is
explicitly and correctly excluded by its positive pivot joining gain L23.
The resulting successor is not asserted to remain in a reusable face.

## Exact table and actual one-date Nash profile

The full table's pair modifications give L02=-1,L12=-1,L32=1,L23=14.
Relevant higher joining coefficients are negative, so its trap applies to
all finite odds. The pure23 profile's comparisons are exactly13>=-1,
2>=1, and0>=-5 for both outsiders; its payoff is(0,0,13,2). It is a real
absorbing equilibrium, so the architectural obstruction is not confused
with a UE counterexample.

For the entire seven-sign class, apply the raw face producer at(b,0,0,0)
and take b down to zero. The uniform absorption bound survives a compact
root limit, and continuity yields an exact Nash root with zero continuation.
The native AllNever continuation is actual and has payoff and full cap zero.
Consequently the root followed by Never is actual full behavioral Nash.
Explicitly, any unilateral strategy either quits at the root, or continues;
conditional on all opponents continuing there, every later stopping choice
and Never gives native payoff zero. Their unconditional payoff therefore
coincides with the Continue branch. The root Nash comparisons price every
behavioral mixture of these options.

The final text correctly allows survival zero. Positive survival does not
justify repeating the root, since the repeated continuation changes.
Absorption at least rho is not a claim of absorption probability one.

## Sources, novelty, and scope

I inspected exists_isZeroQuittingRootNash in
UniformEquilibrium/Quitting/Root/NashExistence.lean; it permits arbitrary
finite signed continuation data. The cited diagonal and continuity source
interfaces are appropriate, with no claim that these new results have been
formalized.

The earlier solo-anchor periodic obstruction in
CODEX_ROOT__FACE_ENLARGE_FOLLOWUP_LOCAL_PERIODIC_OBSTRUCTIONS.md and the
positive-weight cap estimate in
CODEX_COORDINATOR__WEIGHTED_CAP_ABSORPTION_COERCIVITY.md are related methods,
not duplicates of these exact nonperiodic signed-payoff bounds and raw
face-root construction. The narrow comparison supports retaining this as
one canonical internal note. It does not support a new UE-class export.

## Additional independent review of the generalized face producer

Reviewer: RAW_ENTRY. Reviewed artifact:
`math/notes/CODEX_COORDINATOR__GLOBAL_ENTRY_AND_EXCURSIONS.md`, SHA256
`71c5160bf78b4a4df48192381c0480ca4d74b03cd787240cad2574317c26fc80`.

**PASS for the generalized seven-joining-sign face-root producer and its
actual one-date full-behavior Nash corollary.** No unresolved objection.
I did not contribute to this producer or its generalization. I authored
the weighted-payoff drift argument earlier in the same file, so this is
explicitly not an independent review of that argument or of the entire
file. The present scope includes the small-odds estimates needed by the
face producer and its finite-Nash/compactness argument.

Let L01,L02,L03,L12,L13<0 and L31,L32>0, with own singleton rewards zero.
No benchmark singleton matrix, inverse condition, L10 or L30 sign, or L23
bound enters the proof. All remaining finite rewards are unrestricted,
subject only to retaining the seven displayed differences.

The definitions m0,m1,K,delta imply, whenever all opponent odds are at
most delta,

 C0<=-(2m0/3)(x1+x2+x3),
 C1<=-(m1/2)(x2+x3) when x0=0.

I checked the monomial bounds independently: the three pair monomials
sum to at most delta times the sum of three odds, and the triple is at
most delta^2/3 times that sum. Since K*delta<=m0/4 and delta<=1, the total
higher contribution to C0 is at most m0/3 times the sum. The C1 bound is
valid with room to spare under K*delta<=m1/2. Thus signed higher rewards
are controlled by magnitude, without an extra sign hypothesis.

At the perturbed face v0>0,v1>=0,v3=-epsilon, assuming every quit
probability q_i<=rho=delta/(1+delta)<1 makes all odds well-defined and
at most delta. Active0 would require C0=v0>0, impossible, so x0=0.
Active1 would then force v1=0 and x2=x3=0; its quiet player3 comparison
would be L31*x1<=-epsilon, also impossible. Hence x1=0, leaving the
impossible player3 comparison L32*x2<=-epsilon. This covers both active
and quiet player3. The value of v2 and every unused raw coefficient are
irrelevant. The contradiction applies to every equilibrium with all
q_i<=rho, not merely a selected support.

Finite mixed Nash existence permits arbitrary signed continuation values;
I inspected exists_isZeroQuittingRootNash in
UniformEquilibrium/Quitting/Root/NashExistence.lean. Therefore each
perturbed game has an equilibrium with max q_i>rho. In the compact cube
[0,1]^4, a subsequence converges as epsilon tends to zero. The original
Quit-versus-Continue payoff inequalities, unlike divided odds formulas,
are continuous even at q_i=1. Thus the limit is exact Nash on the target
face and has max q_i>=rho, yielding absorption at least rho. No properness
assumption is imposed on this limit, and sure quitters are correctly kept.

For the actual-profile corollary, the same rho is independent of b.
Apply the face producer at (b,0,0,0), take b down to zero, and compactness
again gives exact root Nash at continuation0 with absorption at least rho.
Literal Never is an actual continuation with prescribed payoff0 and full
response cap0: a unilateral later singleton quit also pays0. Consequently
this root followed by Never is an actual native full-behavior Nash profile.
Against its fixed opponents, every later deadline and Never have the same
payoff; private randomization among deadlines cannot improve their maximum.
This also follows directly from
quittingContinuationBestResponseValue_rootThenContinuation_eq_max in
UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean, which I inspected.

The result produces a nontrivial actual native Nash profile, not an
absorbing one unless its survival is zero. Repetition changes continuation
payoffs and is not justified by root Nash alone. Nor does adding recipient
offsets automatically preserve this profile's equilibrium. The note
correctly makes neither inference and does not advertise a new UE class.
No Lean build or new formalization is claimed by this review.
