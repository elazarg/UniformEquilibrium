# A canonical all-selector counterexample for the global pivot envelope

Author: `CODEX_FRECHET_CYCLE`.

Status: self-contained ordinary-mathematics proof draft. The weak global
geometric-envelope mechanism fails on the explicit table below: every
restricted equilibrium has pivot loss greater than `1/4` for every
`0<δ<1/2`, and its loss tends to `2/7` as `δ↓0`. No independent review,
Lean check, or export has occurred. This is not a counterexample to uniform
equilibrium or approximate-menu selection. A separate full Nash profile is
given below. No hard-matrix residual coverage is claimed.

## 1. Question and literal game

Only player zero is restricted, to independent stopping-clock laws in

```text
B_δ = {μ : Sμ(t)=Pr(T₀≥t)≤(1−δ)^t for every integer t≥0}.
```

Never is included in the survival event, so every member is proper. The
other three players retain arbitrary laws on `ℕ∪{Never}`, equivalently
unrestricted behavioral deviations on the live all-Continue history.
At absorption, the first simultaneous nonempty quitting coalition S pays
the displayed reward forever; before absorption and at all Never, payoffs
are zero. Equilibria in this note are exact terminal Nash profiles of this
restricted game, not unrestricted Nash profiles.

For every nonempty `S⊆{0,1,2,3}` define

```text
r₀(S) = 1 if 0∈S, and 2 otherwise;
r₁(S) = 1[0∈S] if 1∈S, and 3·1[0∈S]−1 otherwise;
r₂(S) = 1[1∈S] if 2∈S, and 3·1[1∈S]−1 otherwise;
r₃(S) = 0 if 3∈S, and 1 otherwise.                         (T)
```

These formulas specify all fifteen rows. The own-singleton vector is
`(1,0,0,0)` and every absolute reward is at most two. All-Never opponents
give each player exactly its own singleton as its unrestricted cap, so the
canonical punishment-normal upper bounds hold directly.

This changes only the pivot rewards in HILBERT's cyclic stress table. The
weak-envelope response surface and its distinction from a daily hazard
floor were read in
[`CODEX_HILBERT__ONE_PIVOT_FORCED_CLOCK_REGULARIZATION.md`](CODEX_HILBERT__ONE_PIVOT_FORCED_CLOCK_REGULARIZATION.md).
The proof below does not transfer that note's daily-floor uniqueness or
assume that conditioning preserves `B_δ`.

The source route is the proper watchdog boundary of `docs/TOOLKIT.md` and
the definitions `IsProperQuittingBehaviorStrategy` and
`IsQuittingProperStrategicallyApproximable` in
`UniformEquilibrium/Quitting/Terminal/StrategicallyPrecompactWatchdogProperBoundary.lean`.
The comments distinguish the proper-approximation interface from a semantic
producer. The finite positive-reach splice underlying
`timingLawTail_isNash_of_isNash_of_positiveContinue` in
`UniformEquilibrium/Diagnostics/Quitting/FiniteDeadlineTimingRecursion.lean`
was inspected in the earlier intake audit; no infinite-clock theorem is
attributed to its finite-menu declaration. The argument here proves its
needed positive-reach comparisons directly.

## 2. Exact conclusion and existence

Fix `0<δ<1/2` and put `a=1−δ`. Define

```text
b = δ/[1+√(1−δ+δ²)],
c = δ(2−δ)/(1−δ²),
D = (1−b)(1−c).
```

**Theorem.** The restricted game has exactly one equilibrium product
stopping law. It has constant hazards

```text
(q₀,q₁,q₂,q₃) = (δ,b,c,0).                                (N)
```

All nonpivot unrestricted regrets are zero. The pivot's unrestricted
regret is

```text
L_δ = δ/[1−a(1−b)(1−c)] > 1/4,
lim(δ↓0) L_δ = 2/7.                                      (L)
```

Uniqueness is for complete stopping laws; behavior after actual absorption
is not being distinguished. Consequently minimizing unrestricted pivot
loss, mean pivot time, or any other objective over the restricted Nash set
cannot repair this mechanism on (T).

Existence can be checked directly, so no general compact-game theorem is
needed for this table. In (N), `0<b<1` and `0<c<1`. The followers' pure
finite-date and Never payoffs are respectively constant at δ and b. This
follows either from the indifference identities in Section 6 or by summing
the geometric race against their two active opponents. Dummy Never attains
one and is optimal. Against the stationary followers,

```text
F₀(t)=2−D^t,
U₀=2−δ/[1−aD].                                           (P)
```

The geometric pivot clock is optimal on `B_δ` for this increasing sequence
F₀, by the response identity proved next. Hence (N) is restricted Nash.

## 3. The pivot's envelope-binding identity

For arbitrary opponents let `K=min(T₁,T₂,T₃)`, allowing `K=Never`.
The actual pivot pure finite-time payoff in (T) is

```text
F₀(t)=1+Pr(K<t).
```

For any proper pivot clock μ, independence and Tonelli give

```text
Eμ[F₀(T₀)] = 1 + Σ[k≥0] Pr(K=k) Sμ(k+1).                 (E)
```

All summands are nonnegative. The geometric clock simultaneously saturates
every upper bound `Sμ(k+1)≤a^(k+1)`. Thus μ is a restricted best response
if and only if

```text
Sμ(k+1)=a^(k+1) whenever Pr(K=k)>0.                       (BIND)
```

This is a GLOBAL condition. No conditional pivot suffix is presumed to
remain feasible, and no arbitrary change of the pivot's current hazard is
used below. Two consequences are useful: if opponents can first quit at
t, then the current pivot hazard is at most δ; its hazard at t+1 is at
least δ. They follow by applying the envelope bounds on either side of
`S₀(t+1)=a^(t+1)`.

## 4. Sure quitting and all positive-reach cases

Consider any restricted equilibrium. At a date t with positive joint live
probability, let qᵢ be the conditional current hazards. The pivot is proper.
Therefore dummy Never pays exactly one. A dummy pure time t pays
`Pr(an active player quits strictly before t)`, which is strictly below one
at every such reached date. Thus `q₃=0` there.

If a follower has positive current Quit probability, its finite pure time
t is a best reply, also compared with the pure time t+1. These comparisons
require no optimal off-path suffix. Its Quit-now values are
`Q₁=q₀` and `Q₂=q₁`, since its quitting reward is the predecessor indicator.
Its Quit-next reward at a surviving next date is always nonnegative.

First suppose `q₁>0` and `q₂=0`. Player one's Quit-next comparison gives

```text
q₀ ≥ 2q₀+(1−q₀)q₀(t+1).
```

Hence `q₀=q₀(t+1)=0`. But player-one activity makes `Pr(K=t)>0`, so
(BIND) forces `q₀(t+1)≥δ`, a contradiction. Thus

```text
q₁>0 implies q₂>0.                                      (A1)
```

When `q₂>0`, player two's Quit-next comparison gives

```text
q₁ ≥ 2q₁−(1−q₁)q₀,
q₁ ≤ q₀/(1+q₀) ≤ δ/(1+δ)=:h.                           (A2)
```

The last inequality uses (BIND), because q₂ activity implies `q₀≤δ`.
In particular `q₁<1`. If `q₂=1`, current absorption is certain from
player one's perspective: Quit pays q₀ and Continue pays `3q₀−1`.
Since `q₀≤δ<1/2`, Quit strictly wins, forcing `q₁=1`, contrary to (A2).
Thus at every active follower date both followers and the pivot have
hazards strictly below one.

If both follower hazards are zero, a sure pivot Quit would give player two
minus one by its prescribed Continue, while Quit now gives zero. This also
cannot occur. We have proved that every reached date has strictly positive
joint Continue probability. Starting at zero and inducting, every finite
date is reached. The dummy consequently chooses Never as a complete law.

This disposes of zero-reach threats before using any conditional suffix
optimality. Since the followers are unrestricted, each can preserve its
prefix and replace its conditional tail at any date. The gain is multiplied
by positive joint reach, so its actual conditional value Vᵢ(t) is its full
conditional cap. In particular

```text
V₁(t)≥q₀(t)≥0,             V₂(t)≥q₁(t)≥0.                (F)
```

When `q₂(t)>0`, its value equals its Quit-now payoff, so
`V₂(t)=q₁(t)≤h` by (A2).

## 5. Every date is active; the pivot is exactly geometric

Call a date active when at least one of q₁,q₂ is positive. By (A1), every
active date has q₂ positive, and hence `V₂≤h` there.

Suppose `S₀(t)=a^t` and date t is inactive. If there is a first later active
date u, then u≥t+1 and the two followers have no hazard before u. Player
two receives minus one if the pivot stops during this inactive stretch.
Its exact conditional value therefore is

```text
V₂(t)=−(1−s)+sV₂(u),       s=S₀(u)/S₀(t)≤a^(u−t)≤a.
```

It follows that

```text
V₂(t) ≤ −1+a(1+h) = −2δ²/(1+δ) < 0,
```

contrary to (F). If there is no later active date, properness of the pivot
instead gives `V₂(t)=−1`, the same contradiction.

Initially `S₀(0)=1=a⁰`, so date zero is active. By (BIND), this gives
`S₀(1)=a`. The preceding argument makes date one active, and induction
proves activity and `S₀(t)=a^t` at every date. Therefore

```text
q₀(t)=δ for all t,       q₂(t)>0 for all t.                (G)
```

This is derived from global-envelope optimality and follower comparisons;
it is not an assumed daily hazard floor.

## 6. Followers are uniquely stationary

We already know `0<q₂<1` and `V₂=q₁≤h`. If `q₁=0` at a date, player
two's interior indifference and Bellman identity give
`0=−δ+aV₂(next)`, forcing `V₂(next)=δ/a>h`, impossible.
Thus `0<q₁<1` and its indifference gives `V₁=δ` at every date.

The exact Continue endpoints for followers are

```text
C₁=2δ−a q₂+a(1−q₂)V₁(next),
C₂=2q₁−(1−q₁)δ+a(1−q₁)V₂(next).
```

The first equality `C₁=V₁=δ` gives `q₂=c` as stated. The second gives

```text
q₁(t)=f(q₁(t+1)),
f(z)=[δ−az]/[1+δ−az].                                   (R)
```

On `[0,h]` its denominator exceeds one and
`|f(z)−f(w)|≤a|z−w|`. Its unique fixed point there is b, the smaller
root of `a b²−2b+δ=0`. Iterating (R) for m steps gives
`|q₁(t)−b|≤a^m h`; letting m tend to infinity yields `q₁(t)=b`.
This establishes complete-law uniqueness claimed in Section 2.

## 7. Full loss and non-counterexample to UE

Both followers have proper geometric clocks, so the pivot's Never payoff
and full cap equal two. Formula (P) gives (L). For the uniform lower bound,
`b<δ` and `c≤2δ` when `0<δ<1/2`, while

```text
1−(1−δ)(1−b)(1−c) ≤ δ+b+c < 4δ.
```

Thus `L_δ>1/4`. Also `b/δ→1/2` and `c/δ→2`, so dividing its denominator
by δ gives the limit `1+1/2+2=7/2` and hence `L_δ→2/7`.
This covers every finite and Never deviation, because the cap is the
literal supremum over the full pure-time set and behavioral mixtures.

The game nevertheless has a simple exact full Nash profile: only player
one uses a geometric clock of hazard `1/2`, and all other players Never.
Its value is `(2,0,2,1)`. Player one's payoff is always zero; the pivot
obtains at most two and attains it at Never; player two obtains at most two
and attains it at Never; and the dummy obtains at most one and attains it
at Never. Thus every unrestricted deviation is capped directly. The same
profile has finite expected absorption delay. The nonowner coordinates
`2,2,1` are global per-stage upper bounds, and player one's reward against
three Never opponents is always zero. Its uniform-equilibrium interpretation
therefore follows directly by averaging these caps and letting the prescribed
finite expected absorption delay vanish relative to the horizon.

The normalized singleton matrix is

```text
Γ = [ 0  1  1  1;
      2  0 −1 −1;
     −1  2  0 −1;
      1  1  1  0].
```

It has homogeneous simplex witness `e₁`, since
`Γe₁=(1,0,2,1)≥0` and the supported coordinate is zero. Therefore this
example is outside the hard nonhomogeneous matrix residual. It disproves
the proposed global-envelope exact-follower selection mechanism on the
stated canonical class; it does not settle that mechanism after adding a
no-homogeneous-witness assumption, nor the original approximate-menu question.

Concrete next check: independently falsify Sections 4–5, especially the
Quit-next comparisons before positive joint reach is established and the
envelope-binding step replacing invalid conditional feasibility.
