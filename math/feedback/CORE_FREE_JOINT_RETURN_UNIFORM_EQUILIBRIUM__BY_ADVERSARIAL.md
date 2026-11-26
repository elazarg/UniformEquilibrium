# Final adversarial review of the direct joint-return theorem

Reviewer: FINITE_PARAMETRIC. Ordinary mathematics; no Lean build.

Reviewed `math/exports/CORE_FREE_JOINT_RETURN_UNIFORM_EQUILIBRIUM.md`, SHA256
`58ddd1d47cb6b0fe7bf86bb6a9c425a148e3ba8a829c8acf1c34de93dbbcadc5`.

Verdict: the complete assembled packet is mathematically valid. I found no
unresolved objection. This review covers the expanded generic hypotheses,
boundaries, raw construction, exact five-date example, local openness,
nonredundancy calculations and full behavioral consumer. It does not infer
an arbitrary-Fin4 conclusion or a new Lean check.

## Generic raw theorem and attempted boundary falsifications

I rechecked the cubic elimination against the literal joint02 expectations.
The equation is exactly equivalent to the row2 affine-return identity after
multiplying positive denominators. The definitions of j and C give the other
nontrivial coordinates. None of this uses d>0, v<e, u>=0, or a simple cubic
root. Those hypotheses were needed by a previous finite-core method and are
correctly absent here. A nonzero polynomial and an admissible real root are
finite raw data, not an assumed strategic certificate.

The dangerous s<0 case is handled correctly. From C<k and s<beta,

    k+s*b>b(k+beta)>0,
    C+s*b=b(beta-s*b)/(1-b)>0,
    0<tau=(C+s*b)/(k+s*b)<1.

The displayed identity proves the j denominator positive even if L>1.
In particular X0=-s*b<k. The actual selected prefix a is positive and proper;
no negative auxiliary hazard is used anywhere in this proof.

The interval in(4) provides all needed conditions, including the additional
bound a<tau. Its lower bound B/(H+B), with B=max(s*b,0), gives the row0
prefix comparison for either sign of s. Its other upper bounds give positive
row1 value and the strict row2 comparison Y2>c*a. Weak inequality in(5) is
sufficient because quiet3's current value is exactly0; no perturbative step
of the generic theorem requires its comparison to be strict.

For j<=0, U0,U2 are positive and U1 is nonnegative, including j=0. The direct
return has proper total mass and nonnegative annotations, so sufficiently
small solo3 hazards are legal. No negative-debt wash is applied on this side.
For j>0, the inequalities give0<j<g, C>k*j/g and T>=c*j/A exactly. Regular
wash preserves these conditions. In particular

    z_next-c*v_next/A
      =[z-c*v/A+h*v/A+c*g*v/A^2]/(1-v/A)>0,

so the weak initial boundary T=c*j/A is fully covered. The least-integer wash
rule terminates because its right side is positive and0<1-g/A<1. It also
handles m=0, when the final wash is already legal. The final successor V has
positive row0,row2 and zero row1. The raw affine identity supplies its return
to Y with proper total mass, since a<X1/(X1+g).

I specifically checked positive zeta0<k, rather than using the older
nonpositive sign assumption. At every return root its current row0 value is
k*q+(1-q)times a nonnegative successor, hence exceeds zeta0*q. During wash
its stronger positive floor gives the same comparison. The only other use
of zeta0 is the explicit prefix interval. All other fixed higher rewards
are absent from played or deviating outcomes except the two row1 coordinates
bounded in K_*; no omitted row0 sign cap is being used.

Player1 always Continues. Thus p=Z2(12) is absent even under every single
player deviation, not merely from the prescribed payoff. The explicit K_*
makes the quiet1 joint offer strictly negative. No relation between K and
|p| is needed, and no unspecified large-K threshold remains.

## Unbounded family and exact five-date certificate

I independently verified the seven rational b formulas, their full four-vector
affine identity, eta monotonicity, and the displayed j,T derivatives. The eta
map is a bijection from(0,1/3) to the positive half-line. The tail cutoff is
exactly its value at331/1000, and j-100T/3 is strictly negative there. Since
j increases and T decreases, the whole unbounded tail satisfies the weak
wash guard. The first prefix inequality follows, also when j<=0, from

    X1-b/10=-(b+30)(109b-435)/[10(7629b+2030)]>0.

The remaining signs and K bound are valid on the entire stated interval,
so this is a family proof, not finitely many sampled eta values.

For the five-date instance I separately enumerated all opponent coalitions
at all five roots using exact fractions. All20 payoff transports and root
comparisons hold. Active owners are indifferent, every quiet comparison is
strict, and the final vector equals the starting vector exactly. The values,
hazards and margin fractions agree with Section6. The K=1 quiet1 margin is
positive and increases with K; the arbitrary p coefficient is identically
absent. No numerical or interval root is a premise for this example.

The all60-reward openness argument supplies the missing equalities, rather
than relying only on strict inequalities. The cubic root is simple at this
example; the selected raw quantities vary analytically with the native data.
Fixing the first two solo3 hazards and defining the remaining two by exact
transport keeps all active equalities. Every quiet inequality is strict and
all hazards are proper, so all survive sufficiently small perturbations.
Original own levels are independent affine coordinates and remain permitted.

## Full consumer, self-containment and new coverage

The joint02 date gives every deviator an opponents-only absorption probability
at least min(x,b)>0 per period. The surviving public history is always all
Continue, so no behavioral replacement alters the opponent clock. Bounded
Bellman unrolling controls every complete deviation, including Never. This
also identifies the annotations with actual terminal payoffs and justifies
independent own-level shifts. The finite expected absorption bound gives the
claimed fixed-profile, fixed-target uniform finite-horizon conclusion.

I inspected the named consumer
`quittingGame_fixedProfile_uniformPayoffWitnesses_of_terminalNash_exact` in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
Its exact terminal Nash premise is supplied by Section4. The producer proof
is self-contained and does not need the earlier long-core theorem: the
finite wash and all return equations are proved here. The exact example
contains all its rational data. The stationary exclusions specify their full
input table and deterministic rational algorithm, rather than relying on a
temporary checker as an unprovided premise.

I reran the enlarged stationary and sure-root calculations on eta in[0,2]:
1486 nodes exclude all80 nonzero stationary patterns, and209 nodes exclude
all65 sure-root patterns, uniformly K>=1000 with p=0. I independently
recomputed all eight origin constants in the packet. The K relaxation,
principal-inverse origin argument and Bernstein subdivision preserve
necessity; the vanishing-hazard stationary limit is also excluded correctly.

I also reran the14 child Farkas sums and checked their coefficient signs.
The previously inspected WithdrawalFutureJoin raw row definitions justify
the relaxed systems. The five-date example fails the older positive-entrance
core guard by the displayed exact negative fraction, and the entire admissible
root set is exhausted by eta monotonicity. The24-label sign check gives the
identity; dropping the Gamma30 sign adds only(0,3,2,1), whose c is0. These
are complete named selector failures. The packet correctly limits its claims
about other supplied-object architectures and unspecified older neighborhoods.

No strategic input is left assumed. The result establishes a new raw reward
region and exact nonstationary profiles, not a universal classification of
all four-player tables. Approval in this review applies to the stated hash;
changed mathematical content requires review of the new bytes.
