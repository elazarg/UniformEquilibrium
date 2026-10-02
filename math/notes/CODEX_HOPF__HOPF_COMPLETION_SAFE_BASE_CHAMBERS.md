# Safe-base chambers in the HOPF maximal-ray family

Author: `CODEX_HOPF`

## Status

This note proves ordinary-mathematics positive results for a broad class of
completions of the HOPF active maximal-ray table.  Every completion in the
stated chambers has an exact terminal Nash profile against all behavioral
deviations, hence a uniform-equilibrium payoff.  The result is not checked in
Lean.

The main consequence is sharp for the attempted regression.  The convenient
condition used to make player `3` a uniformly strict spectator already forces
the pure singleton `\{2\}` to be an exact terminal equilibrium.  Therefore a
positive-minimum completion must give player `3` a strict incentive to join
`\{2\}` and must establish global maximality of the active ray by some method
other than uniform spectator domination.

This does not decide the remaining join-positive chamber and does not produce
a positive-gap table.

## Question

Keep the three-player active reward face and exact maximal-cap recurrence from
`CODEX_HOPF__CARD_THREE_MAXIMAL_RAY_REGRESSION.md`, while allowing arbitrary
reward coordinates on coalitions containing the fourth player.  Can this
freedom remove the zero-minimum equilibrium without changing the literal
forced-pair source or the active ray?

The answer is no on the safe-base chambers below.  More generally, avoiding
zero minimum requires a uniform separation condition on an induced
three-player Nash correspondence.

## Sources inspected

- the active table and exact maximal ray in
  `notes/CODEX_HOPF__CARD_THREE_MAXIMAL_RAY_REGRESSION.md`;
- `quittingTerminalSemanticDebt_pureSetRoot_eq` in
  `UniformEquilibrium/Quitting/Paths/SureExitSet.lean`; and
- `nonempty_quittingSingletonBaseCertificate_of_inducedNash` and
  `exists_uniformPayoff_or_singletonBase_pos_gap` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`.

The induced-game theorem in Section 5 is the concrete HOPF specialization of
the last two checked declarations.  The sign reduction (8), and its
interaction with the HOPF limiting equilibrium segment, are the new point of
this note.

## 1. The completion class

Let the players be `0,1,2,3`, with active set

\[
 A=\{0,1,2\}.
\]

On coalitions not containing player `3`, retain the HOPF active table.  Only
the following data are used here:

\[
 r_i(\{i\})=0\quad(i\in A),
\]

and the two membership increments against the active singleton `\{2\}` are

\[
 r_0(\{0,2\})-r_0(\{2\})=-2,
 \qquad
 r_1(\{1,2\})-r_1(\{2\})=-2.
 \tag{1}
\]

All payoff coordinates on coalitions containing player `3`, and player `3`'s
payoff row on every coalition, may otherwise be arbitrary.  In particular,
one may simultaneously retain the literal forced-pair source

\[
 \{3\}\longrightarrow\{0,3\}
\]

with a zero marked defect for player `0` and a positive distinct payer at the
pair.  Those source conditions do not touch (1) or any proof below.

Write

\[
 s_3=r_3(\{3\}),
 \qquad
 J_{32}=r_3(\{2,3\})-r_3(\{2\}).
 \tag{2}
\]

## 2. Two unconditional exact-equilibrium chambers

### Proposition 1: the nonpositive-singleton chamber

If

\[
 s_3\le0,
 \tag{3}
\]

then all-Never is an exact terminal Nash profile.

Indeed, every active player's finite solo quit pays zero, player `3`'s finite
solo quit pays at most zero, and Never pays zero.  Every randomized,
history-dependent, or arbitrarily late unilateral stopping law is a convex
combination of these two values because all opponents remain Never.

### Proposition 2: the nonpositive-join chamber

If

\[
 J_{32}\le0,
 \tag{4}
\]

then the profile which makes exactly player `2` Quit at date zero and makes
everyone Never thereafter is an exact terminal Nash profile.

For players `0` and `1`, joining the sure quitter at date zero changes payoff
by `-2`, by (1).  Continuing, Never, or quitting later cannot affect the
date-zero absorption.  Player `3`'s only effective alternative is to join at
date zero, whose gain is `J_(32)<=0`.  Finally, if player `2` refuses to Quit,
all players Continue forever.  Quitting later gives its zero singleton reward
and Never gives zero, exactly its prescribed payoff.  These cases exhaust
arbitrary behavioral deviations.

Thus every completion with `J_(32)<=0` has total minimum debt

\[
 D_*=0.
 \tag{5}
\]

No assumption on `s_3` or on any other spectator-containing reward is needed.

## 3. Why uniform spectator domination cannot support positive minimum

Suppose the completion makes player `3` weakly prefer Continue to Quit at
every nonempty pure active background:

\[
 r_3(T\cup\{3\})\le r_3(T)
 \qquad
 (\varnothing\ne T\subseteq A).
 \tag{6}
\]

Taking `T=\{2\}` gives (4), so Proposition 2 applies.  In particular, both
spectator completions in the maximal-ray regression have an exact terminal
equilibrium for this structural reason, not merely because their singleton
rewards happened to vanish.

For a literal family with positive spectator singleton, add the same constant
`c>0` to player `3`'s payoff at every nonempty terminal coalition in either
regression table.  This shifts its singleton, every actual absorbing payoff,
and every cap on the ray by `c`, while leaving every endpoint difference and
all three active root equations unchanged.  All-Never is no longer an
equilibrium for player `3`, but the pure singleton `\{2\}` remains exact by
Proposition 2.  Thus the zero-minimum conclusion is not an artifact of the
normalization `s_3=0`.

The same fact is visible at the limiting cap game.  On the active face, the
HOPF mechanism has the equilibrium segment

\[
 (x_0,x_1,x_2)=(0,0,z),\qquad 0\le z\le1.
 \tag{7}

At `z=1`, this is the pure singleton `\{2\}`.  Condition (4) lets player `3`
Continue there, so the segment cannot collapse to unique all-Continue in the
four-player game.  Conversely, any positive-minimum completion of this active
mechanism must satisfy the strict sign

\[
 \boxed{r_3(\{2,3\})>r_3(\{2\}).}
 \tag{8}

Thus the omitted player cannot remain a uniformly dominated spectator.  A
putative positive-minimum completion has to use its strict join at `\{2\}` to
destroy the inessential limiting component, while still proving that no new
root involving player `3` beats the selected active maximum root.

## 4. A second explicit chamber: the pure pair `\{2,3\}`

Assume (8), and also

\[
 r_2(\{2,3\})\ge r_2(\{3\}),
 \tag{9}
\]

\[
 r_i(\{2,3\})\ge r_i(\{i,2,3\})
 \qquad(i=0,1).
 \tag{10}
\]

Then the pure date-zero coalition `\{2,3\}` is an exact terminal Nash
profile.  Each member weakly prefers staying in the pair by (8)--(9), and
each outsider weakly prefers not joining by (10).  Since the coalition has
two sure quitters, every unilateral behavioral deviation is screened at date
zero and reduces to the corresponding Boolean endpoint comparison.

Consequently a positive-minimum completion must satisfy (8) and at least one
of the three strict escape inequalities

\[
 r_2(\{3\})>r_2(\{2,3\}),
 \tag{11a}
\]

\[
 r_0(\{0,2,3\})>r_0(\{2,3\}),
 \tag{11b}
\]

\[
 r_1(\{1,2,3\})>r_1(\{2,3\}).
 \tag{11c}
\]

These conditions are independent of the active ray equations and of the
forced-pair data at `\{3\}` and `\{0,3\}`.

## 5. The full singleton-base chamber

The preceding pure profiles are endpoints of a larger exact-equilibrium
construction.

Let `N=\{0,1,3\}`.  Define the finite strategic-form game `Gamma_2` in which
the players in `N` choose Quit or Continue and player `2` is held fixed at
Quit.  If `T subseteq N` is the set of quitting free players, player `i in N`
receives

\[
 r_i(\{2\}\cup T).
 \tag{12}
\]

Let `pi` be any mixed Nash equilibrium of this finite game, and let `mu_pi`
be its product distribution on `T`.  Define player `2`'s two endpoint values

\[
 Q_2(\pi)
 =\sum_{T\subseteq N}\mu_\pi(T)r_2(\{2\}\cup T),
 \tag{13}
\]

\[
 C_2(\pi)
 =\sum_{\varnothing\ne T\subseteq N}\mu_\pi(T)r_2(T).
 \tag{14}
\]

The missing `T=emptyset` term in (14) is zero: after player `2` Continues and
all free players Continue, the prescribed suffix is all-Never, and player
`2`'s best later solo payoff is its zero singleton reward.

### Theorem: safe induced equilibrium implies exact terminal Nash

If some `pi in Nash(Gamma_2)` satisfies

\[
 Q_2(\pi)\ge C_2(\pi),
 \tag{15}
\]

then the following behavioral profile is an exact terminal Nash profile:

- player `2` Quits surely at date zero;
- the three free players use `pi` at date zero; and
- after a counterfactual all-Continue outcome, everyone plays Never.

For a free player, player `2` still Quits surely after every unilateral
deviation.  Only the deviator's date-zero action can affect its payoff, and
the Nash inequalities of `Gamma_2` are therefore exact against its entire
behavioral strategy class.  For player `2`, Quit at date zero gives (13).
Continuing gives (14); on the empty free coalition, every later finite quit
and Never both pay zero.  Randomization and history dependence cannot exceed
the better of these two endpoints.  Condition (15) proves exact Nash.

This defines a broad, completion-dependent semialgebraic chamber: the Nash
correspondence of `Gamma_2` intersects the closed owner-safe half-space
`Q_2-C_2>=0`.  The pure singleton and pure-pair constructions above are its
pure-equilibrium special cases.

## 6. Exact obstruction required by positive global minimum

The mixed Nash set of the finite game `Gamma_2` is nonempty and compact, and
`C_2-Q_2` is continuous.  If a completion had `D_*>0`, the theorem in
Section 5 would be forbidden.  Therefore

\[
 C_2(\pi)>Q_2(\pi)
 \qquad
 \text{for every }\pi\in\operatorname{Nash}(\Gamma_2).
 \tag{16}
\]

Compactness upgrades this pointwise statement to a uniform margin:

\[
 \boxed{
 \exists\eta>0\quad
 C_2(\pi)-Q_2(\pi)\ge\eta
 \quad\text{for every }\pi\in\operatorname{Nash}(\Gamma_2).}
 \tag{17}
\]

Together with (8) and (11), equation (17) is the exact completion-side escape
gate.  A positive-minimum HOPF completion must simultaneously:

1. make the spectator strictly join the otherwise exact active singleton;
2. destabilize the resulting pair;
3. make **every** equilibrium of the full induced three-player face unsafe
   for the singleton owner by one common positive margin; and
4. nevertheless keep the selected three-active root globally maximum among
   all four-player cap roots.

The existing uniformly dominated spectator construction fails already at
item 1.  The equations above explain precisely why varying spectator-
containing rewards is necessary, and what those variations must accomplish,
rather than merely observing that the original completion has `D_*=0`.

## 7. Sharpness: the escape signs coexist with the exact maximal ray

The sign (8) is not itself inconsistent with global root maximality.  The
following fixed-real completion retains the literal forced pair, has no pure
terminal coalition equilibrium, and makes all-Continue the unique root at the
limiting cap.  It is still not known to have positive minimum debt.

Take `d=1/100` in the active HOPF table and put

\[
 L=\frac25-d>0.
\]

For active player `i`, specify its membership gain at a background coalition
`T subseteq \{0,1,2,3\}\setminus\{i\}` by

\[
 g_0(T)=\mathbf1_{1\in T}-2\mathbf1_{2\in T}
       +d\mathbf1_{3\in T},
 \tag{18a}
\]

\[
 g_1(T)=\mathbf1_{0\in T}-2\mathbf1_{2\in T},
 \tag{18b}
\]

\[
 g_2(T)=\frac25(\mathbf1_{0\in T}+\mathbf1_{1\in T})
       -L\mathbf1_{3\in T}.
 \tag{18c}
\]

For player `3`, put

\[
 g_3(T)=-\mathbf1_{0\in T}-\mathbf1_{1\in T}
          +\mathbf1_{2\in T}.
 \tag{18d}
\]

On backgrounds not containing player `3`, choose the active passive rewards
exactly as in the original HOPF table.  On backgrounds containing player `3`,
choose the three source values

\[
 r_0(\{3\})=0,
 \quad r_1(\{0,3\})=d-1,
 \quad r_2(\{0,3\})=0.
 \tag{19}
\]

Set every other still-unspecified active passive value on a background
containing player `3` to zero.  Together with (18), this defines every active
reward coordinate.

Equations (18a)--(18c) then give, at the pure pair `C=\{0,3\}`,

\[
 r_0(C)=d,
 \quad r_1(C\cup\{1\})=d,
 \quad r_2(C\cup\{2\})=d.
 \tag{20}
\]

Thus the active cap of the literal pair source is `(d,d,d)`: player `0` is
the zero-defect forced-pair owner, while player `1` has gain `1` and player
`2` has gain `d` at that same pair.

It remains to choose player `3`'s passive row so its cap converges to its
singleton without changing the active orbit.  Let `(t_k,t_k,z_k)` be that
orbit, put

\[
 s_k=(1-t_k)^2(1-z_k),\qquad P_0=1,\qquad P_{k+1}=P_ks_k,
\]

and define

\[
 R=\sum_{k\ge0}\frac{t_k}{P_{k+1}}<\infty.
 \tag{21}
\]

Fix any `s_3>0`.  On a nonempty active coalition `T`, set

\[
 r_3(T)=s_3+\sum_{i\in T}m_i,
 \qquad (m_0,m_1,m_2)=(R,-R-1,0),
 \tag{22}
\]

and define `r_3(T union {3})=r_3(T)+g_3(T)`, with
`r_3({3})=s_3`.  At `C={0,3}`, player `3`'s Continue endpoint is `s_3+R`
and its prescribed endpoint is `s_3+R-1`, so its source cap excess is `R`.

### Exact global root enumeration

Against a cap whose excess over the singleton vector is

\[
 (a,a,b,e),\qquad a,b,e>0,
\]

the exact Quit-minus-Continue differences have the signs of

\[
\begin{aligned}
G_0&=x_1-2x_2+dx_3-a(1-x_1)(1-x_2)(1-x_3),\\
G_1&=x_0-2x_2-a(1-x_0)(1-x_2)(1-x_3),\\
G_2&=\tfrac25(x_0+x_1)-Lx_3
     -b(1-x_0)(1-x_1)(1-x_3),\\
G_3&=-x_0-x_1+x_2-e(1-x_0)(1-x_1)(1-x_2).
\end{aligned}
\tag{23}
\]

There is no Nash root with `x_3>0`.  Such a root would have `G_3>=0`, hence

\[
 x_2\ge x_0+x_1.
 \tag{24}
\]

If `x_1>0`, then `G_1>=0` gives `x_0>=2x_2`, contradicting (24).
Thus `x_1=0`.  If `x_0>0`, then `G_0>=0`, `G_2>=0`, and (24) give

\[
 2x_0\le2x_2\le dx_3,
 \qquad
 Lx_3\le\frac25x_0,
\]

which is impossible because `(2/5)d/L<2`.  Hence `x_0=0`.  If now
`x_2>0`, then `G_2<0`, again impossible.  If `x_2=0`, the conditions
`e>0` and `G_3>=0` contradict each other directly.  This exhausts the finite-
cap cases.

Therefore every Nash root has `x_3=0`, and (23) reduces exactly to the three
active equations.  Conversely, all three active roots really lift to four-
player roots: at all-Continue `G_3=-e<0`; at the active pair root
`G_3=-2x_0-e(1-x_0)^2<0`; and at the full root
`G_3=-2t_k+z_k-e(1-t_k)^2(1-z_k)<0` because `z_k<t_k`.
The full active root therefore remains the unique global maximum-absorption
root at every finite cap.

Player `3`'s successor cap excess obeys

\[
 e_{k+1}=s_ke_k-t_k.
 \tag{25}
\]

The choice (21) gives the exact solution

\[
 \frac{e_k}{P_k}=\sum_{h\ge k}\frac{t_h}{P_{h+1}}>0,
 \qquad e_k\longrightarrow0.
 \tag{26}
\]

Thus this is again a full-binding, partial-support, ballistic maximal ray, now
with the strict join sign `J_(32)=1` and positive spectator singleton.

At the limiting cap, the active equations alone give the segment
`(0,0,z,0)`.  For every `z>0`, however, `G_3=z>0`, so the point is not a
four-player root.  If instead `x_3>0`, repeat (24): it first forces
`x_1=x_0=0`; then `x_2>0` contradicts `G_2=-Lx_3<0`, while `x_2=0`
contradicts `G_0=dx_3>0` with `x_0=0`.  Hence

\[
 \boxed{\text{all-Continue is the unique limiting exact root}.}
 \tag{27}
\]

There is also no pure terminal-coalition equilibrium.  If player `3` is
absent, the only stable active coalition is `\{2\}`, which player `3`
strictly joins.  If player `3` is present, enumerate the active part `T`:

- `T=emptyset`: player `0` joins by gain `d`;
- `T=\{0\}`: player `1` joins by gain `1`;
- `T=\{1\}`: player `0` joins by gain `1+d`;
- `T=\{2\}`: player `2` leaves by gain `L`;
- `T=\{0,1\}`: player `2` joins by gain `4/5-L>0`;
- `T=\{0,2\}`: player `0` leaves because `-2+d<0`;
- `T=\{1,2\}`: player `1` leaves because `-2<0`;
- `T=A`: player `0` leaves because `-1+d<0`.

This construction proves that the escape requirements (8), positive
spectator singleton, forced-pair provenance, global maximality, ballistic
scaling, and unique limiting all-Continue root are algebraically compatible.
It does **not** prove positive global minimum: a mixed or genuinely temporal
exact equilibrium may still exist.  Its role is to show that the safe-base
theorem above uses a real sign chamber; global maximality alone does not force
the safe sign.

## 8. Remaining question

It remains open whether (8), (11), and (17) can coexist with the global
maximum-root property and the positive-minimum forced-pair passport.  A
positive construction would be a serious counterexample candidate.  A
negative result should now target the uniform owner-unsafe condition (17),
not the already-disposed uniformly dominated spectator chamber.
