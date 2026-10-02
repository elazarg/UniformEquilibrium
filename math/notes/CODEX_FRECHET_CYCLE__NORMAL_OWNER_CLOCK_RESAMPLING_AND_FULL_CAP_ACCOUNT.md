# Normal-owner winning-clock resampling with its complete cap account

Identity: CODEX_FRECHET_CYCLE.

## Status and precise question

Ordinary mathematics, not independently reviewed or Lean-checked. This note
tests an actual independent-clock transformation at the fixed-table global
sources. No full-regret decrease or equilibrium producer is claimed from
those sources. The new marked benefit is only one part of a complete gain;
Sections 4–5 retain the rest and every response cap.

Can the no-UE singleton geometry select the player who should receive an
independent copy of a source's singleton winning clock? A collider and a
solo preemptor need not be the same player. The answer uses the STRONGER
affine rate inequality, not a presumed alignment of its two endpoints.
Punishment completion extends that inequality to every normal owner,
including negative own singletons. This makes the ensuing test applicable
to every singleton component of a source, not just a positive owner.

## 1. Fixed table, gap, and genuine source hypotheses

There are four players, independent complete stopping laws, bounded rewards
|r_i(S)|≤M on nonempty coalitions, and zero payoff at Never. Write s_i=r_i({i}).
Let g>0 be a terminal exploitability witness: every actual independent
profile has a behavioral deviation with gain at least g. In the
[singleton-fiber source](../exports/MEMBERSHIP_STRETCH_AND_SINGLETON_FIBER_SOURCE_REDUCTION.md),
one may fix such a witness at the selected table whose global full MAX
regret infimum is Ω>0. It is not a witness from another normalized table.

Every owner is punishment normal at the same Fin4 table:

    v_i:=inf_(independent opponent laws) full cap_i ≤ s_i.        (N)

This is a field of the checked same-table full-support residual, not a
consequence of the observed source law. Recursive full normal core and
punishment normality are different definitions; the source explicitly
supplies both. The normalized solo matrix below is the raw difference
Γ_(i,h)=r_i({h})−s_i; defining it makes no strategic normalization or
change of Never reward.

The actual near-minimizing source p has finite support in 1,...,N and
Never. Its complete tester pool contains the initial dates, all source
dates, all needed post-support finite dates, Never, and a separate zero
row. Put U_i=U_i(p), B_i=sup_t V_i(t;p), E=max_i(B_i−U_i),
g_(i,t)=V_i(t;p)−U_i. The same probability λ on testers satisfies

    Σ_a λ_a(E−g_a)≤a,
    Σ_a λ_a D_p g_a[q−p]≥−R                       for every allowed q,
    θ_i:=Σ_t λ_(i,t)≥θ₀>0.

The fixed-table source has E→Ω and a,R→0, with θ₀=Ω/4 eventually.
The contested-positive-owner extraction preserves these fields, but does
NOT necessarily preserve total scalar pressure or individual reward
normality. Neither is assumed here. The copy laws constructed below use
only source finite dates through Section 5a and hence lie in its allowed
domain. Section 5b explicitly uses an enlarged, retimed calendar instead.

## 2. Every normal owner has the full affine rate restriction

For k normal and 0<h≤1, there is b≠k such that

    (1−h)[s_b−r_b({k})]
       +h[r_b({k,b})−r_b({k})] ≥ g.                 (1)

For s_k>−g this is exactly the checked
`QuittingTerminalExploitabilityWitness.exists_soloRate_joiningGain`.
Here is a complete independent extension using (N), without that sign
restriction.

Choose a near-minmax independent stationary punishment for k whose full
cap is at most v_k+ε≤s_k+ε. Prescribe k's proper stopping clock

    Pr(T_k=t)=h(1−h)^t  for 0≤t<L,
    Pr(T_k=L)=(1−h)^L.

Every other player Continues through L. Only from date L+1 onward do they
use the chosen punishment. Their conditional tails are actual independent
laws. The prescribed terminal outcome is EXACTLY {k}, so every prescribed
payoff is r_i({k}); the punishment is never reached in prescribed play.

For owner k, every finite response through L gives s_k. Every finite
response after L, and Never, sees the full punishment cap at most s_k+ε.
Thus k's unrestricted debt is at most ε, also when s_k<0. This is the
reason that simply using an infinite solo geometric clock with opponents
Never would not suffice in the signed case.

For any outsider b, k remains properly stopped by L under every b
deviation. Its gains at dates t<L are exactly

    (1−h)^t A_b(h),
    A_b(h)=(1−h)[s_b−r_b({k})]+h[r_b({k,b})−r_b({k})].

Its gain at L is (1−h)^L[r_b({k,b})−r_b({k})], and every response
after L and Never has gain zero. These formulas cover the full cap by
pure-time extremality. They do not pretend the final forced-Quit atom
has the earlier geometric hazard.

If all A_b(h)<g, their finite maximum and zero are strictly below g.
Take ε<g and L with 2M(1−h)^L<g. All four complete debts of this
actual profile are then below g, a contradiction. This proves (1).
For h=1 use L≥1; the residual final atom is zero and the earlier first
date supplies the collision endpoint as it should. The preemption h=0
endpoint follows by finite choice and continuity, but is not needed below.

The punished finite solo construction is already the strategic mechanism
in `quittingStationarilyGeneratedApproximateEquilibria_of_approximate_solo_caps`.
The use here is its fixed-gap raw consequence and its ensuing actual-clock
composition, not a claim of a new punishment producer.

## 3. Actual independent resampling and rate-adapted receiver selection

Let μ(t,S) be the source's DATED first-outcome law. Fix any owner k with
σ_k:=Σ_t μ(t,{k})>0, and define the finite probability law

    f_k(t)=μ(t,{k})/σ_k,
    c_k=Σ_t f_k(t)²,       h_k=2c_k/(1+c_k) ∈(0,1].

Apply (1) at h_k and choose one receiver b≠k. Sample X independently
from f_k, independently of ALL original clocks, and replace only b by

    T'_b=min(T_b,X).                                  (2)

This is an actual marginal law; the other three source laws remain
unchanged. Computing f_k from the supplied profile is permitted. No
player conditions its action on who wins the REALIZED play. In particular
(2) is different from the non-product conditional swap in the
[previous checkpoint](CODEX_FRECHET_CYCLE__CONTESTED_SINGLETON_BLOCK_EXCHANGE_BOUNDARY.md).

Conditional on the ORIGINAL source outcome being {k}, its winning date
and X are independent and identically distributed with law f_k. On the
event X<T_k the new outcome is {b}; at equality it is {k,b}; if X>T_k
the original singleton remains. The expected contribution of ALL original
k-singleton outcomes to b's prescribed-payoff change is therefore

    M_b=σ_k[(1−c_k)/2 ·(s_b−r_b({k}))
                    +c_k·(r_b({k,b})−r_b({k}))]
       ≥σ_k(1+c_k)g/2 ≥σ_k g/2.                      (3)

Thus one raw-table receiver handles both strict races and ties. Separate
preemptor and collider labels need not coincide, and the receiver need not
be the later finite opponent in the originally contested event. On a
varying-source sequence b may vary; after fixing k, the three possible
receivers permit a fixed-label subsequence if needed. No rate limit or
uniform atom size is needed.

## 4. Full dated-outcome and complete-response account

Put F(t−)=Pr(X<t), f(t)=Pr(X=t), and set r_i(Never)=0. Define

    Φ_i(t,S)=F(t−)[r_i({b})−r_i(S)]
               +f(t)[r_i(S∪{b})−r_i(S)],
    Φ_i(Never)=r_i({b}).                              (4)

The reward change on a finite original outcome at t is: a strictly earlier copy wins alone, a
tied copy joins the original coalition, and a later copy changes nothing.
If b already belongs to S, the union term is zero. On original Never,
the proper finite copy makes b the unique quitter. Hence, with expectation
over the source's dated law,

    β_i:=U_i(p')−U_i(p)=∫ Φ_i dμ.                     (5)

For any NONMOVER i≠b, let ν_(i,t) be the original dated outcome law after
its arbitrary pure response t. Applying the same first-outcome coupling
while that response is fixed gives the EXACT complete gain increment

    g_(i,t)(p')−g_(i,t)(p)=∫ Φ_i dν_(i,t)−β_i.       (6)

For i=b the response values are unchanged, since its opponents are
unchanged; EVERY b-owned gain increment is −β_b. In particular

    B'_b=B_b,
    B'_i=sup_t [V_i(t;p)+∫ Φ_i dν_(i,t)]   (i≠b).    (7)

The suprema retain initial, joining, after-support and Never responses.
A source's zero Never mass does not imply zero Never mass after deleting
a proper owner; (4) must still be applied to those response-law Never
events. This is the full envelope, not an estimate on old active rows.

Write β_b=M_b+J_b, where J_b is the contribution in (5) of original
outcomes OTHER THAN {k}, including Never. Let L_b=max(0,−J_b).
Affineness in the one changed marginal and the SAME source certificate
then imply

    θ_b L_b + Σ_(i≠b,t) λ_(i,t)
                   [∫Φ_i dν_(i,t)−β_i]
        ≥ θ_b M_b−R.                                (8)

Thus the marked benefit cannot be called a whole-profile gain. It may be
offset by b's losses on other original outcomes; even if it is not, the
same-weight full cap account must supply cross compensation. When those
own losses are smaller than M_b by a fixed amount, the earlier near-active
cross-amplification argument locates a nonmover cap debt increase. That
generic consequence is credited, not reproved as a new consumer.

## 5. Exact simplification on a singleton/Never-supported source

Assume additionally that the source's ENTIRE finite terminal law is
supported on singletons. At each positive-reach date there is at most one
player with positive Quit hazard: otherwise its root has positive
nonsingleton probability. Consequently μ(t,{h}) and μ(t,{k}) cannot
both be positive for h≠k. In particular, the copied f_k clock cannot
tie a different source singleton owner h.

Put C=μ(Never), and for h≠k define the literal two-draw ordering weight

    w_(k,h)=Σ_t μ(t,{h}) F_k(t−).

It is the probability that an INDEPENDENT k-winning-time sample occurs
strictly before the original h-singleton winning date. It is not a claim
that two different source outcomes occur along the same play. On original
b-singleton outcomes, moving b earlier leaves its own reward unchanged.
Equations (4)–(5) now give exactly

    β_b=M_b−Σ_(h∉{k,b}) w_(k,h)[r_b({h})−s_b]+C s_b. (9)

In Fin4 only TWO other source singleton owners can pay a negative
preemption contribution in this formula. At C=0, failure of b's own
payoff improvement forces a positively rewarded helper among those two,
with its displayed same-source ordering weight. At C>0 the signed term
C s_b cannot be dropped. The all-normal extension in Section 2 means a
negative-singleton helper is not automatically a dead end for a subsequent
resampling test.

Recursive full normal core supplies some nonpositive singleton comparison
in each row, not nonpositivity of BOTH entries in (9). The independent
full-support packet's mixture inequalities also do not identify its packet
masses with the w_(k,h) here. No matrix sign or common-normal identity is
silently transferred between those objects. Even if (9) is positive, all
the nonmover responses (6) remain to be paid.

### 5a. A second independent copy to the compensating helper

Suppose c∉{k,b} is a positive helper in (9), so r_b({c})>s_b.
Independently sample a SECOND Y with law f_k and prescribe

    T''_b=min(T_b,X),      T''_c=min(T_c,Y).

All four original clocks, X, and Y are mutually independent. There is no
shared sampled deadline. For an original c-singleton outcome at t, set

    F_t=Pr(X<t),       C_t=Σ_(u<t) f_k(u)².

As shown above, f_k(t)=0. The b-only clip loses F_t[r_b({c})−s_b]
on this event. Adding the c-clip changes b's payoff relative to that
b-only profile by EXACTLY

    ((F_t²−C_t)/2)[r_b({c})−s_b]
                     +C_t[r_b({b,c})−s_b].          (10)

Indeed Y<X<t restores the singleton {c}, X=Y<t creates {b,c}, and
every other ordering leaves b's payoff unchanged on this original event.
The first event has probability (F_t²−C_t)/2, and the second C_t.
Thus even on the particular helper event, its positive singleton edge
does not sign the total restoration: the copied-clock collision uses a
different raw reward. There is no uniform diffuse bound on C_t here.

For completeness, let K_b and K_c denote adjoining the independent marked
clocks (X,b) and (Y,c) to a DATED first-outcome law. Their output is simply
the earliest of the original event and the added clocks, with all marks
at the earliest date joined. They commute, since this describes the same
literal three-event minimum in either order. If μ is the old source law
and ν_(i,t) an old pure-response law, the double-clipped profile has

    U''_i = ∫r_i d(K_b K_c μ),
    V''_b(t)=∫r_b d(K_c ν_(b,t)),
    V''_c(t)=∫r_c d(K_b ν_(c,t)),
    V''_i(t)=∫r_i d(K_b K_c ν_(i,t))   for i∉{b,c}.  (11)

Every complete cap is the supremum of its entire displayed response row.
In particular each mover's response REMOVES its own copy but not the other
copy. Original Never response events are also transformed; source zero
Never does not delete them. Equation (11), rather than (10) alone, is the
actual candidate to compare with the positive global minimum.

This two-copy test has not produced a descent. The supplied positive
helper edge controls only the first term of (10); it gives no bound on the
second term, outcomes outside that event, or the three other full rows.
The same-λ first-order inequality continues to constrain every independent
mixture toward this actual endpoint, but does not identify its mixed
second-order term with a reward-normal direction. That latter substitution
already fails the own-support averaging test in the
[earlier joint-head account](CODEX_FRECHET_CYCLE__CLAMP_CROSS_AMPLIFICATION_AND_SOURCE_INTERVAL_REACH.md).
No example satisfying the genuine positive-global hypotheses is asserted
to defeat the operation: its orientation from those hypotheses is OPEN.

### 5b. Strictly ordered copies: an actual singleton-preserving variant

Here reselect b by the h=0 consequence of (1), so

    s_b−r_b({k})≥g.

This may be a DIFFERENT receiver from Section 3. Suppose c∉{k,b} satisfies
r_b({c})>s_b for this receiver. With fresh independent X,Y of law f_k,
retime every original date t to 3t+2, put c's copy at 3Y, and put b's
copy at 3X+1. Each mover uses the earlier of its retimed old clock and
its own copy. This is a legal independent profile, not a conditional
priority assignment after seeing X and Y. Equal sampled labels have the
fixed priority c, then b, then the original clocks.

All prescribed terminal outcomes remain singleton. Write

    G_t=Pr(X≤t),          C_t^+=Σ_(u≤t)f_k(u)²,
    q_b(t)=G_t−(G_t²+C_t^+)/2,
    q_c(t)=G_t−(G_t²−C_t^+)/2.

On an original singleton outcome {h} at t, b wins the new race exactly
when X≤t and X<Y; c wins exactly when Y≤t and Y≤X. Therefore EVERY
owner i's prescribed-payoff change on that original event is

    q_b(t)[r_i({b})−r_i({h})]
          +q_c(t)[r_i({c})−r_i({h})].                (12)

On original Never the new payoff is
((1−c_k)/2)r_i({b})+((1+c_k)/2)r_i({c}). These formulas specify the
whole prescribed account, not just one rectangle. For h≠k one has
f_k(t)=0, so G_t=F_t and C_t^+=C_t.

For b on original c-singleton outcomes, adding the c-copy to the
strictly earlier b-copy now restores

    ((F_t²+C_t)/2)[r_b({c})−s_b]≥0.                  (13)

There is no copied-clock pair collision. On original k-singleton outcomes,
c's copy cannot hurt b: both new singleton rewards s_b and r_b({c})
exceed r_b({k}) by at least g. The b-copy alone already contributes at
least σ_k(1+c_k)g/2, since Pr(X≤T_k | original k-win)=(1+c_k)/2.
On original b-singleton outcomes the c-copy is beneficial or neutral.
Thus the remaining prescribed b-bill comes only from unrecovered losses
on c's singleton, the FOURTH player's singleton, and the stated signed
Never term. These conclusions refer to the reselected strict-preemptor
b and its checked helper c; they do not reuse an unverified old pair.

The retiming is NOT assumed cap-neutral. Here is its complete finite
response calculation. Let L=max supp(f_k), a_i(t) be the old conditional
hazard, and h(t)=f_k(t)/Σ_(u≥t)f_k(u). At each t≤L the actual word is

    date 3t:   only c uses hazard h(t);
    date 3t+1: only b uses hazard h(t);
    date 3t+2: use the original independent hazards a_i(t).

Positive original k-winning mass at L implies positive original joint
reach at every t≤L. Singleton support therefore makes each relevant old
root mono-owner as well. At L the c-copy and b-copy each have hazard 1;
after deleting either mover the other still forces absorption, and after
deleting any nonmover both remain. Consequently every prescribed play and
every unilateral response absorbs by date 3L+1. No hidden continuation
or additional after-support response is omitted.

For each solo root with owner j and hazard h, compute the actual payoff
and cap backward from its complete tail (u,B):

    u'_i=h r_i({j})+(1−h)u_i;
    B'_j=max(s_j,B_j);
    B'_i=max((1−h)s_i+h r_i({i,j}),
                 h r_i({j})+(1−h)B_i)  for i≠j.     (14)

These are the two exhaustive responses at EACH new date. In particular
the first branch at every copied-clock row retains every joining tester;
the old source's cap value is not substituted for it. Starting from the
actual terminal tail, this finite fold gives all four exact full debts of
the candidate. Any later tail is screened by the two proper copies.

Thus strict ordering really removes the adverse prescribed pair term in
(10), while replacing it by explicit new joining-cap branches in (14).
The actual source's globality remains available for comparing the final
four maxima, but no sign on those new branches follows from (13). This
is the remaining test, not a full-regret decrease or a cap-preserving
retiming theorem.

There are two separate global comparisons here. The final retimed profile
is admissible for the all-profile infimum η(r), so its complete fold can
always be compared with Ω. However, its dates extend to 3L+1. It need not
belong to the original X_(N+3) directional domain, and the same λ
inequality cannot silently be applied to its chord. Merely retiming the
old source first does not repair that interface: the inserted empty dates
also give previously unavailable preemption responses and may raise its
complete cap. No retained near-minimality of that retimed source is claimed.

The output here is an at-most-one-owner calendar. The checked declaration
`Schedule.one_over_sixtyEight_lt_literal_exploitability`, in
`UniformEquilibrium/Quitting/Examples/SolanVieilleBoundarySoloHazardSemantic.lean`,
gives a positive full-regret floor for EVERY such finite or infinite calendar
on its particular solved table. Its displayed unconditional proof and the
stronger quadratic bound were inspected. This does not refute the present
conditional operation at a genuine positive global source, but does rule
out treating singleton preservation as a strategy-class completeness
argument. No new regression theorem is claimed here.

### 5c. In-calendar atomic thinning: exact full-tester cancellation test

Here is a bounded calculation for the mixed-row operation, retaining the
ORIGINAL source rather than retiming it. Fix a literal singleton donor
atom μ=μ(t,{k})>0. Name the two distinct helpers b,c and the fourth player
d. Independently, with probabilities x and y, respectively, b and c add
a forced stopping clock at the SAME existing date t; otherwise they keep
their original law. Their new laws are thus the chords between the old
law and min(T_b,t), and between the old law and min(T_c,t). This is an
actual two-marginal perturbation in the original finite domain.

Put z_j=Pr(T_j>t) for j≠k and a_k=Pr(T_k=t). All four quantities are
positive and μ=a_k z_b z_c z_d. Singleton support and positive joint
reach at t imply that the three nonowners have NO original atom at t.

The two copies create a prescribed {k,b,c} outcome at t with probability
xyμ. They never create a prescribed grand-coalition outcome: the old d
clock has no atom at t. Fix ANY complete pure tester τ, including Never.
Let H_(i,τ)(S) be the ORIGINAL counterfactual terminal probability of S
under that tester. If |S|≥3, this probability occurs strictly AFTER t:
positive original joint reach through t implies at most one positive
source hazard at every date through t, so a single response can create
at most a pair there. But H can be positive in a hidden later tail after
deleting a proper source owner. Singleton support of prescribed play
does NOT eliminate it.

Put l_b=1−y, l_c=1−x and l_k=l_d=(1−x)(1−y). The coefficient of
the raw reward r_i({k,b,c}) in the COMPLETE gain g_(i,τ)(x,y) is

    i=b:   l_b H_(b,τ)({k,b,c}) + y(μ/z_b) 1_(τ=t) − xyμ;
    i=c:   l_c H_(c,τ)({k,b,c}) + x(μ/z_c) 1_(τ=t) − xyμ;
    i=k:   l_k H_(k,τ)({k,b,c}) + xy(μ/a_k) 1_(τ=t) − xyμ;
    i=d:   l_d H_(d,τ)({k,b,c}) + xy(μ/z_d) 1_(τ>t) − xyμ. (15)

Never counts as τ>t. For instance, under b's response its own added
clock disappears. A triple can then occur only if b itself chooses t,
the c-copy is active, k stops at t, and d survives; independence gives
y a_k z_c z_d=yμ/z_b. The prescribed triple probability xyμ is
subtracted from EVERY b-owned response. The other rows follow by the
same deletion argument. In particular d's response at t is NOT in the
last triple row: it joins the newly created triple and makes the grand
coalition instead. The l_i H terms retain every old later counterfactual
triple, which survives exactly when neither of the retained added clocks
is active. They may not be omitted from a complete cap.

For every owner the complete grand-reward coefficient is exactly

    coefficient of r_i(I) in g_(i,τ)(x,y)
         =l_i H_(i,τ)(I) + 1_(i=d)xy(μ/z_d)1_(τ=t). (16)

Only d acquires a NEW grand event at t. Equations (15)–(16)
are coefficients in the COMPLETE gain rows, not conditional gains on a
selected observed event. Earlier original outcomes, other source dates,
all nontriple rewards and every other tester remain in the envelope (11).

Thus a low triple reward can cancel a helper's prescribed loss in its
joining response, but only in that specific response. If its full cap
instead takes a different date or Never, the universal term −xyμ in
(15) remains while the positive response term disappears. The actual cap
is the maximum over ALL these rows, so neither cancellation is automatic.
With the original same λ, put J_b=Σ_τ λ_(b,τ)H_(b,τ)({k,b,c}). The
b-owned aggregate coefficient is

    (1−y)J_b + yμ[λ_(b,t)/z_b − xθ_b].

The NEW d-grand term contributes xy(μ/z_d)λ_(d,t), in addition to its
scaled old hidden-tail column. No equality between
λ_(b,t), θ_b and z_b is part of the supplied source. The new grand
response remains in the FULL objective even if its old λ weight is zero.

For the specific date-t response, H_(d,t)(I)=0, and (16) is exactly
xyμ/z_d. This new response-event coefficient has zero constant and
first-order terms. No singleton mark signs its raw grand payoff. However,
the SAME undated grand reward may already enter a different source
response through a hidden tail. It would therefore be wrong to infer
that ALL source caps or derivatives are independent of grand rewards.
That stronger independence holds if the ENTIRE literal source calendar,
including its hidden rows, is at-most-one-owner: a response then makes
at most a pair, and varying one additional law makes at most a triple.
Such an additional completion hypothesis has not been supplied here.

The exact unresolved test is whether global near-minimality, the retained
hidden-tail columns, and the no-UE table restrictions together orient the
new fourth-player joining response while both helper strengths are
positive. The full global comparison remains available and has not been
falsified. No arbitrary local fixture is asserted to satisfy its premises.

An exact boundary check for the hidden columns uses k=0,b=1,c=2,d=3,
t=3, x=y=1/3 and the literal laws

    T_k: 3 and 4, each with probability 1/2;
    T_b: 0 with probability 1/5, 5 with probability 4/5;
    T_c: 1 with probability 1/4, 5 with probability 3/4;
    T_d: 2 with probability 1/6, L with probability 5/6.

For L=5 or 6 the prescribed source is singleton-only and μ(3,{k})=1/4.
At L=5, k's response at 5 has H_(k,5)(I)=1/2, so its NEW complete
grand coefficient is (2/3)²/2=2/9, not zero. At L=6 that same old
response instead has H_(k,5)({k,b,c})=1/2; its new triple-gain coefficient
is 2/9−1/36=7/36. For either L, d's date-3 grand-gain coefficient is
(1/9)(1/4)/(5/6)=1/30. These exact probabilities also follow directly
by enumerating the displayed independent clocks. The data test (15)–(16),
not global minimizer provenance, and require no reward table claim.

The bounded SAME-multiplier sign test now stops here. Write the exact
weighted gain polynomial as

    Σ_a λ_a g_a(p_(x,y)) = E−a + xA+yB+xyC.

Here a is the actual weighted inactivity (or use its stated upper bound).
The allowed directions replacing b, replacing c, and replacing both
give A≥−R, B≥−R and A+B≥−R with this SAME λ. Consequently

    E(p_(x,y)) ≥ E−a−R max(x,y)+xyC.                 (17)

Thus a fixed-size improvement would require a sufficiently negative
mixed coefficient C. A negative C is NOT sufficient: (17) is a LOWER
bound, while improvement requires an upper bound on EVERY complete gain
row. The hidden and grand terms in (15)–(16) are part of those rows and
of C. No retained reward-normal hypothesis gives them the missing signs;
individual normality of the chosen source in those coordinates was never
supplied. Scalar singleton pressure, even if additionally retained, is
not such a coordinate normal.

Unrestricted near-globality also remains available, but applied directly
to this family it says precisely max_a g_a(p_(x,y))≥Ω. Rewriting that
comparison does not supply a strict reverse inequality. This is NOT a
theorem that the genuine source hypotheses logically forbid finding a
contradiction: that would decide the outstanding conjecture. It is the
precise stopping point of this proposed coefficient proof. No sufficient
mixed-row sign has been obtained, and the direct test is retired without
another local fixture or claim of a strategy-class obstruction.

## 6. Source correspondence, scope and next check

The following declarations and the definitions used above were inspected:

- `QuittingTerminalExploitabilityWitness.exists_soloRate_joiningGain` and
  `.exists_soloPreemptor`, in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/PreemptionCycle.lean`;
- `exists_quittingStationaryPunishmentRoot_lt_add`, in
  `UniformEquilibrium/Quitting/Punishment/InstantPunishment.lean`, and the
  exact behavioral/stationary punishment identity in `Stationary/MinMax.lean`;
- `quittingStationarilyGeneratedApproximateEquilibria_of_approximate_solo_caps`
  and `_of_normal_noHarmSingleton`, in
  `UniformEquilibrium/Quitting/Classification/Existence/NoHarmSingletonGenerated.lean`;
- `nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff`
  and the residual's `normalCore_eq_univ` and `all_punishmentNormal` fields,
  in `Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`;
- `FinFourQuantitativeFullSupportHardResidual.exists_terminalGap_collision_at_singleton`
  and `.exists_fixedPointFree_terminalGap_collisionMap`, in
  `Collision/SingletonPacket/PunishmentNormalAtomicCollisionHandoff.lean`;
- `normalCore`, `exists_core_blocker_of_mem_normalCore`, `normalizedSoloMatrix`,
  `IsQuittingNormalPlayer` and `QuittingSoloPreempts`, in their respective
  `Quitting/Classification/LCP/NormalCore.lean`, `LCP/Normalization.lean`,
  `AbnormalPlayers.lean` and `PreemptionCycle.lean` files.

The prefixes omitted from the last paths are `UniformEquilibrium/Diagnostics/Quitting/`
for `Collision/...` and `UniformEquilibrium/` for `Quitting/...`.
No Lean files, builds, exports, or shared indexes were changed.

[TARSKI's private-successor no-go](CODEX_TARSKI_PREMIUM__PRIVATE_SUCCESSOR_RESAMPLING_WEIGHTED_SUM_NO_GO.md)
was read completely. It concerns fixed nonnegative coefficients on four
specified responses, not the profile/rate-adapted receiver and minimum-with-
old-clock law (2). It remains a warning against turning the present selected
gains into an unsupported fixed universal weighted certificate.

The current precise unresolved check is whether the strict-preemptor and
positive-helper signs in Section 5b, together with the ORIGINAL actual
global source constraints, orient the four complete folds (14). The
prescribed account alone is insufficient. The extra source used here is
the normal-owner rate restriction, not presumed cap preservation during
retiming or an arbitrary local corner. For sources with nonsingleton
mass, (5)–(8) remain valid but the singleton-only simplifications and
mono-owner word in Sections 5–5b do not apply.

The next distinct bounded operation is therefore to retain the original
calendar and allow both helpers' copied hazards at its existing dates,
independently thinning their two clips before jointly choosing the two
strengths. This keeps the source itself and its allowed directional domain
unchanged but deliberately permits mixed prescribed rows. Its complete
envelope is (11) with each K replaced by (1−z)I+zK, and a mover's own K
still disappears in its response row. Whether the supplied normal-owner
and helper signs orient any positive joint strengths is open; neither the
first-order certificate nor a marked payoff gain is a proof of that sign.
This is a test specification, not an additional conditional consumer.
Section 5c carries out its atomic full-tester cancellation test and
identifies the new grand-coalition response that requires genuinely
nonlocal source information. No further clock spreading or suppression
of that tester is proposed as a repair.

The next proposed operation changes a DIFFERENT part of the source: at
its first actual solo row, with donor hazard 0<h<1, transfer some hazard
to a single receiver while reducing the donor hazard so that joint
Continue probability stays exactly 1−h. For receiver hazard 0≤x≤h,
the donor hazard is (h−x)/(1−x). Keep the actual tail unchanged. This
is an independent two-owner root, not a correlated transfer of the
realized winner. For the two untouched owners, every response strictly
after that first row changes by exactly the prescribed-payoff change;
their corresponding full gain branches are invariant. New joining
responses make at most a triple, not a grand coalition. The first-row
and h<1 restrictions, both changed owners' caps, and any earlier silent
singleton responses must be retained. This is a distinct scoped test,
not a claimed sign or an extension of (17).
