# The produced full-normal MAX source cannot approach the joint cap ceiling

Identity: CODEX_RADO_BOUNDARY. Date: 2026-09-08.

Status: ordinary mathematical source restriction, not independently reviewed
or Lean-checked. The argument below closes the proposed ceiling-face test,
including production of its common weights and pointwise owner floors. It
does not exclude every positive worst-table source, produce an improving
strategy, or settle UE. No export is proposed here. The exact next branch
and the overlap with the older SUM-debt argument are stated in Sections 6–7.

## 1. Question and exact quantifiers

There are four players I={0,1,2,3}. Each independently chooses a private
complete stopping law on ℕ∪{Never}; every unilateral behavioral replacement
is allowed. The first finite stopping time determines its full tied coalition.
Every nonempty coalition S pays r(S)∈[−1,1]^4; joint Never pays zero. No
mixture over different profiles below is an executable public strategy.

For an actual profile p write μ_p for its law on the fifteen nonempty
coalitions and Never. For a pure complete response time t, including Never,
write ν_(p,i,t) for the law after replacing only i. Define

    U_i(p)=E_p r_i,
    V_i(t;p)=E_(p[i←t]) r_i,
    B_i(p)=sup_t V_i(t;p),
    d_i(p)=B_i(p)−U_i(p),       E(p)=max_i d_i(p),
    η(r)=inf_(all actual independent p) E_r(p),
    Ω=max_(r∈[−1,1]^60) η(r).

Pure-time extremality makes B the unrestricted behavioral cap. In particular
all omitted finite dates, collision responses, and original Never are included.
The cap need not be attained. The cube maximum exists because η is
2-Lipschitz in the reward sup norm. Suppose Ω>0, and take the actually
produced worst-table source described next, at one fixed table r* with
η(r*)=Ω.

**Claim.** There is a produced sequence of finite weighted tuples of actual
silent finite-calendar profiles, with all the original same-weight source
fields retained, for which

    liminf_m E_(p∼ω_m) Σ_i [1−B_i(p)] > 0.             (1)

In fact (1) holds for every good-entry tuple subsequence constructed in
Section 2 whose full reward gradients converge to the retained cube normal.
The claim concerns that tuple sequence. It does not assign individual
normality to its entries or to arbitrary near-minimizers.

## 2. Producer: retain the full cube tuple, not a singleton-fiber selection

The originating source is
[NOETHER's coupled worst-table construction](CODEX_NOETHER_SUPPORT__WORST_REWARD_TABLE_COUPLED_CALENDAR_CERTIFICATE.md),
at SHA `fade3cb825778caf0c76a1a4d6b9820e43bd6f430abf6f8af64b5c95973dd854`,
followed by the actual silent-clock transport in
[FRECHET's source bridge](CODEX_FRECHET_CYCLE__SILENT_SOURCE_COUPLING_TO_WORST_REWARD_PRESSURE.md),
at SHA `0e60914311f2ce46855e87a518400543607d0e2f233bce97f9fd70993b6754db`.
This is the FULL sixty-coordinate source before membership stretching or
restriction to a fixed four-coordinate singleton fiber. The singleton-fiber
normal alone would not justify the proof below.

Here is the retained construction, to fix the load-bearing quantifiers.
NOETHER maximizes the common-smoothed calendar-window value at a table r_m.
Its finite tuple entries are actual minimizers p_(b,N), m≤N≤2m, with
original tuple weights w_(b,N)=θ_b/(m+1). Their same softmax tester weights
give an average full reward gradient G_m∈N_cube(r_m). Every entry is
uniformly near-minimizing for FULL E. Passing to a subsequence gives
r_m→r*, η(r*)=Ω, and G_m→G∈N_cube(r*) with ‖G‖₁=Ω.

FRECHET shifts each actual finite clock by one, leaving Never unchanged,
and recomputes its tester weights λ̂ at the shifted profile p̂. The shift
preserves the prescribed law and full cap, by the uniform positive singleton
moat proved in that bridge. These are new weights at the shifted source;
they are not silently identified with the unshifted softmax weights.

Drop the last two calendars, whose original tuple mass is q_m=2/(m+1).
Write R̂_N for the bridge's same-weight simultaneous enlarged-calendar
directional error. Its original-weight mean is at most B_m→0. Retain ALL
remaining entries with R̂_N≤γ_m=√B_m, so the additional discarded mass is
at most γ_m. Renormalize the surviving ORIGINAL tuple weights to ω_m.
Do not select just the one favorable scalar-pressure entry in that bridge.

At EVERY retained entry p and for EVERY owner i, its equation (10) gives

    θ_i(p) κ_i(p) ≥ E(p)−ε_m−R̂_N−4a_m,
    θ_i(p)=Σ_t λ_(p,i,t),     κ_i(p)=B_i(p)−r_(m,i)({i})≤2.

Here ε_m→0, a_m→0, and E(p)→Ω uniformly. Hence, eventually,

    θ_i(p) ≥ θ₀:=Ω/4 > 0       for EVERY entry and owner. (2)

This is not merely a lower bound on averaged owner totals. The same λ at
that entry also satisfies vanishing inactivity

    a(p):=Σ_a λ_(p,a)[E(p)−g_a(p)] →0 uniformly,       (3)

where a ranges over all labelled complete pure-time testers and the zero
tester g_0=0. It controls every simultaneous independent-law chord in the
bridge's enlarged calendar, with error at most γ_m. The zero tester is kept
in (3), but belongs to no owner block.

The full normal survives this filtering. Before the good-entry deletion,
the unnormalized new-gradient average differs from the original normal by
at most 2q_m+2T_m in ℓ¹, with T_m→0, as proved by transporting the complete
sixty-coordinate response rows in the bridge. Deleting bad entries changes
this average by at most 2γ_m, since each reward row has ℓ¹ norm at most two.
Renormalization changes it by at most 2(q_m+γ_m). Thus its difference from
G_m tends to zero. This retains the full normal, not just its scalar
singleton-pressure consequence.

Finally reuse EVERY retained actual law at r*, keeping its λ̂ computed at
r_m. If δ_m=‖r_m−r*‖∞, full E changes by at most 2δ_m, inactivity by at
most 4δ_m, and chord derivatives by at most 16δ_m. The reward-gradient rows
are law differences and are reward-independent. Consequently all the fields
just stated hold at the same fixed table r*. In the rest of this note all
values and laws are evaluated there; hats are suppressed.

There is a useful direct consequence of (2)–(3): since g_(i,t)≤d_i≤E,

    θ_i(p)[E(p)−d_i(p)] ≤ a(p).

Thus d_i(p)→Ω uniformly over EVERY retained entry and owner. This is a
MAX-debt conclusion obtained from the produced weights. It neither assumes
nor establishes that these profiles minimize SUM debt.

## 3. Two genuine global competitor restrictions

Put s_i=r*_i({i}). The checked MAX-minimum singleton moat gives

    s_i ≤ 1−Ω       for every i.                       (4)

Precisely, the compact semantic carrier has a point minimizing maximum
debt Ω, and
`minimumTerminalSemantic_exploitabilitySingletonMargin` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDynamicCostate.lean`
says Ω≤B_i−s_i there. Its cap is at most one. This uses a global minimum
on the carrier associated with ALL actual laws, not a stationary or a
finite-calendar minimum.

The actual all-Never profile has full regret A=max_i max(s_i,0), so A≥Ω.
If A=Ω>0, this actual profile would itself be a global minimum. Some owner
has s_i=A>0 and B_i=s_i against all Never, contradicting its positive
singleton moat. Therefore

    Ω < A ≤ 1−Ω,       hence 0<Ω<1/2.                 (5)

Second, no nonempty coalition S can have r*_i(S)=1 for all four owners.
Indeed the actual profile in which exactly S quits surely at date zero
gives every owner its absolute reward ceiling. Every behavioral deviation,
including Never, has payoff at most one. This is exact terminal Nash and
would imply η(r*)=0. In particular, for any coalition at which all four
reward coordinates are Boolean (each is −1 or +1),

    Σ_i r*_i(S) ≤ 2.                                  (6)

Neither (5) nor this exclusion of an all-ceiling pure profile follows from
arbitrary local KKT arrays. These are the actual-law global comparisons
used in the face argument.

## 4. Proof of the ceiling-face exclusion

Suppose (1) fails. All its summands are nonnegative, so pass to a subsequence
with

    A_m:=E_ω Σ_i[1−B_i(p)] →0.                         (7)

For every nonempty coalition S define owner-weighted measures using the
SAME entry law ω_m and SAME retained tester weights:

    P_i^m(S)=E_ω [θ_i(p) μ_p(S)],
    N_i^m(S)=E_ω Σ_t λ_(p,i,t) ν_(p,i,t)(S),
    G_i^m(S)=N_i^m(S)−P_i^m(S).

Their gradient G^m tends to the full cube normal G. These weighted measures
are accounting objects, not a new correlated play law. They may also be
defined at Never, but normality is asserted only on the sixty nonempty
reward coordinates.

### 4.1. Almost-active responses avoid every strictly sub-ceiling reward

For each owner,

    Σ_t λ_(p,i,t)[1−V_i(t;p)]
      = θ_i(p)[1−B_i(p)] + Σ_t λ_(p,i,t)[B_i(p)−V_i(t;p)].

The second term is at most a(p), because
B_i−V_i=d_i−g_(i,t)≤E−g_(i,t). After averaging, (3) and (7) show that
the left side tends to zero. All outcome reward deficits 1−r_i are
nonnegative, including the deficit one at Never. Therefore

    r*_i(S)<1  implies  N_i^m(S)→0.                    (8)

This uses all complete response laws. No cap attainer is introduced.

### 4.2. Interior coordinates eliminate their entire baseline coalition

If −1<r*_i(S)<1 for some owner i, full cube normality gives G_i(S)=0.
By (8), N_i^m(S)→0, so P_i^m(S)→0. The POINTWISE floor (2) gives

    P_i^m(S) ≥ θ₀ E_ω μ_p(S).                          (9)

Consequently the average prescribed mass of S tends to zero. It would not
be valid to infer (9) from four positive owner totals: different owners
could then put weight on disjoint source entries. Retaining all good entries
with their pointwise floors is essential.

Thus prescribed mass can survive only at coalitions whose four coordinates
are all in {−1,+1}, or at Never.

### 4.3. Original joint Never is also accounted for

Let C(p)=Pr_p(all Never), and D_i(p)=Pr_p(all opponents of i Never).
Always D_i≥C. Against the event defining D_i, every i-response obtains
at most max(s_i,0); off it, its reward is at most one. Taking the supremum
over every complete i-response gives

    B_i(p) ≤ 1−[1−max(s_i,0)]D_i(p) ≤ 1−Ω C(p),       (10)

using (4). This includes arbitrary finite or unbounded responses and Never.
By (7), E_ω C(p)→0. We have not assumed eventual absorption or equated
opponent survival with joint survival.

### 4.4. Boolean social payoff contradicts the strict MAX bound

There are only fifteen coalitions. Equations (9)–(10), bounded payoffs,
and (6) therefore imply

    limsup_m E_ω Σ_i U_i(p) ≤ 2.                       (11)

On the other hand, (7) and the uniform all-owner debt convergence from
Section 2 give

    E_ω Σ_i U_i(p)
      = E_ω Σ_i B_i(p) − E_ω Σ_i d_i(p)
      → 4−4Ω.                                         (12)

Thus Ω≥1/2, contrary to (5). This proves (1).

## 5. Exact solved calibration: full normality alone admits the ceiling

The following single fixture tests the globality boundary, rather than
purporting to be a positive-gap example. Set

    r_i(S)=−1 if i∈S, and +1 if i∉S; joint Never pays zero.

All-Never is exact terminal Nash: quitting earns −1 and Never earns zero.
Thus this table's true η is zero. For N≥1 let all four players independently
choose a uniform finite clock on {1,...,N}. At this silent actual source,
Never is a full cap response for every owner and B_i=1. Exact counting gives

    Pr(i belongs to the first coalition)
      = (1/N⁴) Σ_(k=1,...,N) k³ = (N+1)²/(4N²),
    U_i=1−(N+1)²/(2N²),
    d_i=E_N=(N+1)²/(2N²) →1/2.

Use λ_(i,Never)=1/4 and zero weight for all other testers. These are actual
cap responses with zero inactivity, positive pointwise owner weights, and
all four debts tied. Each individual Never displacement is outward normal
at this Boolean table: it removes every outcome containing its owner, while
for every coalition excluding its owner the prescribed probability is at
most the probability after making that owner Never. The latter inequality
follows by conditioning on the opponents' first coalition and date and
multiplying by the original owner's probability of stopping strictly later.
Both original and response profiles absorb surely, so each displacement's
nonempty ℓ¹ norm is exactly its gain.

Even a uniform simultaneous first-order field survives asymptotically for
these fixed weights. Change any ONE owner's whole law to any complete law.
The other three clocks stay proper. All four Never-response values remain
one, and prescribed absorption stays sure. Therefore the fixed-λ weighted
gain functional is one half of the expected size of the first coalition.
That size is always at least one, whereas its original expectation is
(N+1)²/N². Every one-coordinate derivative is at least
−1/N−1/(2N²). Summing the four derivative columns gives a simultaneous
independent-law chord derivative at least −4/N−2/N², for ALL endpoint laws,
not just the old finite menu. Own-singleton pressure is nonpositive as well.

Exact rational enumeration for N=1,...,6 checked the payoff formula, every
owner's normal sign at all fifteen coalitions, and ℓ¹ displacement=gain.
The displayed arbitrary-N argument, not those finite checks, proves the
calibration. It passes the ceiling, normal, tie, almost-active, and vanishing
directional-error tests. It fails the genuine worst-table provenance:
η=0 and its limiting debt 1/2 is not the global minimum. In particular
the strict inequality (5) is unavailable. This is not a counterexample to
the source theorem or to the UE conjecture.

## 6. What is new here, and what is already known

[HILBERT's extremal reward note](CODEX_HILBERT__EXTREMAL_REWARD_TABLE_VARIATIONAL_TEST.md),
Sections 9–10, at inspected SHA
`0584db0cab4296fa624e0fac6f7acb33f3cb20d6e9093990cf94178d44d4cf58`,
already excludes four ceiling caps for a positive local maximum of the
minimum SUM debt Δ. It retains a common baseline μ and four normalized
response laws ν_i, proves Σ_i TV(ν_i,μ)≤Δ<1, and uses pure-coalition
low-payoff sets to obtain Σ_i(1−B_i)≥η(1−Δ)>0.

That bound cannot simply be transferred to this MAX source. Its total debt
tends to 4Ω, which is not known to be below one. Also the actual owner
weights vary with the source entry, so independently normalizing each owner
block would give four different baseline measures. This note instead keeps
P_i=E_ω[θ_i μ_p], uses the pointwise common-weight comparison (9), eliminates
interior-coordinate coalitions, and applies the Boolean payoff bound with
the MAX-specific strict half bound. The final surplus identity
ΣU=ΣB−Σd is elementary and not new. The source-level ceiling exclusion
requires the preceding full-normal support elimination; it is not supplied
by that identity alone.

The nearby non-pair/finite-event mass, contested-singleton, singleton
pressure A−L, and same-weight double-replacement compensation accounts were
treated as known starting points. None of those scalar accounts was used
as a substitute for the sixty-coordinate normal in (8)–(9). This note
claims a new MAX-source use of the produced full-normal tuple, not a new
general mass-floor method or an exhaustive novelty survey.

## 7. Exact surviving branch and stopping point

Equation (1) supplies a constant β>0 for the produced fixed-table source
sequence, not a universal numerical constant. Eventually A_m≥β. Its SAME
selected complete response laws then satisfy

    E_ω Σ_(i,t) λ_(p,i,t)[1−V_i(t;p)]
      ≥ θ₀ A_m ≥ θ₀β >0.                              (13)

Thus positive weighted response mass must reach an original outcome paying
that response owner strictly below the ceiling; Never has its original
deficit one. Since the outcome set is finite, one owner/outcome pair carries
positive limiting deficit mass along a subsequence. These remain actual
responses at actual near-minimizing profiles, with the same weights and
vanishing inactivity. No fresh favorable multiplier is chosen.

If that outcome is a nonempty interior-coordinate coalition, normality
equates its averaged owner-weighted response and prescribed masses. At a
−1 coordinate it instead bounds response mass above by prescribed mass.
Neither alternative is contradictory. At Never there is no reward-coordinate
normal equation. In particular (13) does not force a law derivative to be
negative, a new singleton sign, or a full-regret decrease after replacement.

A concrete next question, if this restriction merits further work, is whether
the already-produced same-weight directional inequalities impose additional
constraints on this below-ceiling response mass at interior/−1 coordinates
or Never. That requires a new full-cap argument; it is not established here.
The present bounded operation stops with the strict source face exclusion.

Source inspection for this calculation was confined to the two production
notes above, the named MAX-margin declaration under its imports, the strict
half argument in `exports/THREE_SURE_MINIMA_REQUIRE_OPPOSED_MEMBERSHIP_REVERSALS.md`,
and HILBERT's distinct SUM calculation. Earlier local-normal/compensation
records were read as guardrails. No new Lean declaration, build, literature
claim, author-file edit, or export is part of this result.
