# A source-derived family closed under every nonincreasing unilateral repair

Mathematical result by the external author of `gpt/CLOSED_REPAIR_PLATO.md`.
Self-contained preservation and exact verification by CODEX_RENY. The
original source SHA-256 is
`8729d00056bac7bbb6c8ef8293fa450b07a356579c1f7e1b597e0dacdcd097bf`.

Status: ordinary mathematical proof, independently checked in
[the review](../feedback/CLOSED_REPAIR_PLATO__BY_CODEX_RENY.md), not a
Lean theorem or an export. The table has a pure equilibrium. The result
rules out the specified monotone coordinate-repair protocol, not joint
global selection or the quitting-game conjecture.

## 1. Complete data and theorem

There are four players 0,1,2,3. Every player independently chooses a
stopping law on ℕ∪{Never}. At the first finite stopping date the players
stopping then form the terminal coalition S and receive r(S). All-Never
pays zero. This law description is equivalent to unrestricted behavioral
strategies on the unique live all-Continue history. A unilateral response
may be any stopping law, without a finite-support restriction.

The complete reward table is:

| S | r(S) |
| --- | --- |
| {0} | (1,3,3,1) |
| {1} | (−4,0,−2,−1) |
| {2} | (2,2,0,−3) |
| {3} | (3,−2,−2,0) |
| {0,1} | (1,0,−2,−3) |
| {0,2} | (0,−1,3,0) |
| {0,3} | (1,2,3,−2) |
| {1,2} | (−1,−1,1,1) |
| {1,3} | (4,−4,−4,4) |
| {2,3} | (−4,4,1,1) |
| {0,1,2} | (−3,2,2,4) |
| {0,1,3} | (4,−2,−3,−2) |
| {0,2,3} | (−2,0,−3,2) |
| {1,2,3} | (0,−4,−2,2) |
| {0,1,2,3} | (−2,17,−9,−6) |

Thus |r_i(S)|≤17 and the own-singleton vector is (1,0,0,0).
If P_i is the infimum, over independent opponent strategies, of player i's
unrestricted response cap, then P_i≤r_i({i}): take all opponents Never.
This is the precise punishment-normal assertion; the table is not claimed
to lie in the unit reward cube.

Write U_i(p) for prescribed terminal payoff, B_i(p) for the full response
cap, d_i(p)=B_i(p)−U_i(p), and E(p)=max_i d_i(p). Pure finite-date and
Never deviations suffice to compute each cap, because an arbitrary law's
payoff is their mixture. Put z=3/32.

For every probability distribution G on the **positive finite** dates,
define

```text
σ⁽ᴳ⁾_0 = (1/2)δ₀+(1/4)G+(1/4)δ_Never,
σ⁽ᴳ⁾_j = (1/2)δ₀+(1/2)δ_Never       (j=1,2,3),
F = {σ⁽ᴳ⁾ : G({1,2,…})=1}.
```

The superscript G denotes the chosen law, not a public random variable.
Each player samples its own clock independently.

**Theorem.** Let p_i=(1/2)δ₀+(1/2)δ_Never for all i.

1. p is exact Nash in the actual finite timing menu {0,Never}, and
   d(p)=(1/8,0,0,0).
2. The unrestricted infimum of E(τ₀,p_{−0}) over every pivot law τ₀ is
   z. Its minimizers are exactly F.
3. Every σ∈F has d(σ)=(3/32,3/32,3/32,1/32). If a profile τ differs
   from σ in one player's law and E(τ)≤E(σ), then τ∈F. A nonpivot's
   law must remain identical; only the pivot's G can change.
4. The same table has the pure exact terminal equilibrium in which player
   0 quits at date zero and all other players choose Never.

## 2. The exact source and all optimal pivot repairs

Direct first-event evaluation gives

```text
U(p)=(0,1,−7/8,−1/8).
```

For each player its date-zero and Never payoffs equal that prescribed
coordinate. Later finite dates also equal Never for the three zero-own-
singleton players. For player 0 a positive finite quit gains its singleton
one on the event all three opponents choose Never, of probability 1/8.
Its full cap is 1/8; hence the displayed source debts follow.

For an arbitrary replacement of player 0, let u,λ,ν be its masses at
zero, positive finite dates, and Never. Thus u+λ+ν=1. Its cap is still
1/8 and its prescribed payoff is λ/8. Let D₀=(1−λ)/8 and let N_j be
player j's gain from replacing its unchanged half-zero law by Never.
Calculation from the table gives

```text
N₁=(−13u+16λ+13ν)/8,        N₂=(8u−5λ−8ν)/8,
(3/4)D₀+(2/21)N₁+(13/84)N₂=3/32.                       (A)
```

The three positive weights sum to one, and each term is at most E.
Consequently E≥z. Equality forces D₀=N₁=N₂=z; solving yields

```text
u=1/2,        λ=1/4,        ν=1/4.                     (B)
```

Conversely, every law with (B) has the form σ⁽ᴳ⁾. For nonpivot j, its
payoff from the pivot's late singleton is a_j=(3,3,1)_j, its collision
payoff is b_j=(0,3,−2)_j, and its own singleton is zero. Since
a_j≥max(b_j,0), Never weakly dominates every positive finite quit,
pathwise after surviving date zero. A positive-date response either waits
until the pivot has quit, joins its quit, preempts it, or quits when the
pivot is Never; these four comparisons give respectively a_j, b_j, 0, 0
instead of the Never payoffs a_j, a_j, a_j, 0. Earlier absorption is
unchanged. Date zero and Never therefore suffice for the nonpivot caps.

For every G, including unbounded-support laws, exact evaluation gives

```text
U(σ⁽ᴳ⁾)=(1/32,35/32,−25/32,−3/32),
B(σ⁽ᴳ⁾)=(1/8,19/16,−11/16,−1/16).
```

This proves optimality, the exact family debt vector, and the assertion
that **all** optimal first repairs have been accounted for.

## 3. A five-event calculation covers arbitrary nonpivot replacements

Fix σ⁽ᴳ⁾ and replace nonpivot j's law by an arbitrary μ. Draw S∼G and
T∼μ independently, and put

```text
x=Pr(T=0),                     n=Pr(T=Never),
a=Pr(0<S<T<Never),              b=Pr(0<S=T<Never),
c=Pr(0<T<S<Never).
```

These events partition the probability space: S is finite and positive
almost surely, so x+n+a+b+c=1. The two unchanged nonpivot clocks are
zero-or-Never coins. For each of their four outcomes, every relevant
payoff depends on (S,T) only through these five events. Thus conditioning
gives exact affine formulas even when G and μ have unbounded support.

For the updated profile τ, define D_j=B_j(τ)−U_j(τ), N_i as player i's
Never gain, H as the pivot's gain from replacing its full law by G, and
L as the limit of the pivot's gain from deterministic Quit t as t→∞.
Every one is at most E(τ). L is a limit of legal response gains, not a
claim that a late finite supremum is attained. Bounded convergence proves
its existence: on every fixed opponent-clock sample, sufficiently late
Quit sees the first finite opponent outcome if one exists, and otherwise
gets the pivot singleton reward one.

Moreover D_j is affine in the five weights: the mover's opponents are
unchanged from σ⁽ᴳ⁾, so its cap is the same constant as in Section 2 and
is attained by Never. The following coefficient table lists the values
on the five partition events; arbitrary event weights take their weighted
average.

| mover j | event | D_j | H | L | N₁ | N₂ |
| --- | --- | --- | --- | --- | --- | --- |
| 1 | x | 3/16 | −1/8 | −1/8 | 3/16 | −3/8 |
| 1 | n | 0 | 5/16 | 5/16 | 0 | 9/16 |
| 1 | a | 0 | 9/16 | −11/16 | 0 | 7/16 |
| 1 | b | 3/16 | 9/16 | −11/16 | 3/16 | 1/8 |
| 1 | c | 3/16 | −3/8 | −3/8 | 3/16 | 1/8 |
| 2 | x | 3/16 | 1/2 | 1/2 | −9/8 | 3/16 |
| 2 | n | 0 | −5/16 | −5/16 | 21/16 | 0 |
| 2 | a | 0 | −7/16 | −3/16 | 23/16 | 0 |
| 2 | b | 0 | −5/8 | −1/8 | 19/16 | 0 |
| 2 | c | 3/16 | −1/4 | −1/4 | 11/8 | 3/16 |
| 3 | x | 1/16 | 1/4 | 1/4 | −3/8 | 7/8 |
| 3 | n | 0 | −1/16 | −1/16 | 9/16 | −11/16 |
| 3 | a | 0 | −1/4 | 1/4 | 7/16 | −13/16 |
| 3 | b | 3/16 | −1/4 | 1/4 | 3/8 | −13/16 |
| 3 | c | 1/16 | 1/8 | 1/8 | 1/8 | −9/8 |

Exact linear combination gives

```text
j=1: (29/38)D₁+(51/380)H+(9/380)L+(3/38)N₂
       =z+(9/76)b;
j=2: (91/106)D₂+(3/53)L+(9/106)N₁
       =z+(15/848)a+(9/53)c;
j=3: (7/10)L+(11/40)N₁+(1/40)N₂
       =z+(29/160)a+(21/128)b.                         (C)
```

Each line is a convex combination with strictly positive weights. Its
right side is at least z, so E(τ)≥z for every replacement.

## 4. Equality forces the original law, not merely the original regret

Suppose E(τ)≤z. Every positively weighted term in the applicable line of
(C) must then equal z, and every displayed positive excess must vanish.

For j=1 this gives b=0. The coefficient table yields
D₁=(3/16)(x+c) and H−L=(5/4)a under b=0. Thus x+c=1/2,
a=0, and n=1/2. Substitution into N₂ gives N₂=z+c/2. Hence c=0 and
x=n=1/2.

For j=2 the excess first forces a=c=0. Then D₂=3x/16=z forces
x=1/2. Writing n=1/2−b, the L equality is L=z+3b/16=z. Hence b=0
and n=1/2.

For j=3 the excess forces a=b=0. Under these restrictions L=N₁=z is
equivalent to

```text
5x+3c=5/2,             15x+7c=15/2.
```

Subtracting three times the first equation from the second gives c=0;
therefore x=n=1/2.

In every case a+b+c=0 is the mover's **entire** positive finite mass.
Its law is consequently exactly (1/2)δ₀+(1/2)δ_Never. A pivot
replacement is governed by (A)–(B), so it can only change G. This proves
closure under every E-nonincreasing unilateral law replacement, including
neutral changes, with no selection or finite-clock qualification.

## 5. Iterations, limits, and the equilibrium outside the family

Every finite stage of a sequence of such unilateral repairs starting in F
remains in F, at the constant regret z. For a weak limit in the
one-point compactification ℕ∪{Never}, the pivot keeps mass 1/2 at zero
and has positive finite mass λ≤1/4 by Fatou's lemma. Its other three
opponent laws are fixed. Its actual debt is (1−λ)/8≥z. Thus taking a
weak stopping-law limit does not yield an equilibrium either. This is a
direct cap calculation; no continuity of terminal payoff at Never is
assumed.

Outside F, take player 0's law to be δ₀ and all others Never. The pivot
gets one, the maximum it can get against all-Never opponents. The
nonpivots get (3,3,1), while their date-zero joining payoffs are (0,3,−2).
Later deviations cannot change the already absorbed outcome. The profile
is therefore exact terminal Nash with payoff (1,3,3,1), and the same
date-zero argument gives the uniform-equilibrium payoff directly.

In particular the global geometric-repair minimum is already zero with
opponent menu {0,Never}. Neither p nor F is a joint global minimizer.

The exact eliminated guarantee is: from **every** finite-menu exact Nash
source, first optimally repair the pivot against fixed opponents and then
select E-nonincreasing complete unilateral replacements to obtain regret
tending to zero. This table defeats every first-repair tie choice and
every subsequent such coordinate choice. It does not defeat selecting a
different source, a nonoptimal first move, coordinated changes of several
laws, temporary increases, or the actual joint-global-minimum programme.
