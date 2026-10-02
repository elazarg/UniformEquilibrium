# Feedback on `CODEX_RAMSEY__POSITIVE_ATOM_ROOT_REPAIR_FLOOR`

Reviewer: `CODEX_CEDAR`

## Scope and verdict

I independently attempted to falsify Sections 3--6: sure-observer tail
invariance, the localized other-player debt floor, the `gamma/(8M)` root-
movement estimate, two-label persistence, and observer-cap contraction.

**Verdict: VALID ordinary mathematics in the stated positive-target collision
scope.**  The conclusion is a root-displacement/small-debt-entry obstruction,
not a repaired exact root or a chronology producer.

## Checks

1. If `q_o(Quit)=1` and `i!=o`, then both forced actions of `i` and its
   prescribed mixture absorb in the current row.  Thus their endpoint values,
   prescribed successor, and coordinate Nash defect are independent of every
   artificial tail.  In particular `O_i(q)=0`.  Combining the exact localized
   identity

   ```text
   globalGain_i=liveMass*g_i(q,u)
   ```

   with `liveMass<=1` and `globalGain_i>=gamma` gives the tail-independent
   lower bound `g_i(q,w)>=gamma` for every successor annotation `w`.

2. For the root-movement estimate, couple all Bernoulli marginals maximally.
   The union bound gives mismatch probability at most
   `D(q,qhat)`.  Off the mismatch event the old sure observer is also Quit in
   the new root, so both coupled rows absorb in the same coalition and neither
   tail is read.  Each forced endpoint and the prescribed successor therefore
   changes by at most `2M D`; max is 1-Lipschitz in its two endpoints, yielding

   ```text
   |g_i(q,u)-g_i(qhat,w)| <= 4M D(q,qhat).
   ```

   Since normalized repair implies `g_i(qhat,w)<=eta`, the displayed
   `(gamma-eta)/(4M)` bound and its `gamma/(8M)` specialization for
   `eta<gamma/2` follow with the correct inequality orientation.  The stated
   hypothesis that rewards and both tails lie in `[-M,M]` is essential.

3. From `liveMass*rootMass(T)>=lower` and `liveMass<=1`, one gets
   `rootMass(T)>=lower`.  Any fixed `b in T\{o}` therefore has marginal Quit
   probability at least `lower`, while `o` Quits surely.  Deleting `o` leaves
   per-row survival at most `1-lower`; deleting any other player leaves the
   sure observer and gives survival zero.  This proves joint and every-player-
   deleted survival on every suffix of any word of the selected roots.

4. The terminal-semantic prefix prescribed payoff and every nonobserver cap
   are tail-independent for the same sure-absorption reason.  For observer
   `o`, only its forced-Continue endpoint can read the successor cap, on the
   all-outsiders-Continue event, so the exact Lipschitz coefficient is
   `O_o(q)`.  Since terminal `T` contains an outsider and has root mass at
   least `lower`, `O_o(q)<=1-lower`.  Iteration gives the claimed geometric
   one-coordinate modulus.  At the head, the selected `i`'s candidate debt is
   exactly its fixed row defect, hence at least `gamma` for every terminal
   annotation.

## Qualification

The norm lower bound does not locate the repairing displacement or show that
the repaired root loses either clock.  Conversely, the literal clock-rich
word cannot satisfy a small initial candidate-debt requirement below
`gamma`; a separate entry block/root change remains necessary.  I found no
route here from behavioral atom mass to an exact admissible Nash--Bellman
edge without that missing bridge.

## Addendum: canonical own-marginal sign refinement

I separately audited Consequence 5B after it was added.  **Verdict: VALID in
its explicitly canonical, one-coordinate scope.**

With opponents and the artificial tail fixed, changing only player `i`'s own
marginal leaves its two forced endpoint values and hence
`B_i=max(Q_i,C_i)` unchanged.  Its prescribed value is identically
`U_i=B_i-g_i`.  Therefore reducing the defect from at least `gamma` to at
most `eta` gives exactly

```text
Uhat_i-U_i=g_i-ghat_i >= gamma-eta,
Bhat_i-B_i=0.
```

The sign is positive and no conditioning factor is missing.

In the exceptional case where `i` is the sole displayed collision partner
and Continue is its better endpoint, write `x` for its Quit probability and
`A=C_i-Q_i>0`.  Since the sure observer is an unchanged opponent,
`O_i=0` before and after the own-marginal repair.  Thus

```text
g_i=xA>=gamma,          ghat_i=xhat A<=eta.
```

As `x<=1`, the first inequality gives `A>=gamma`; hence
`xhat<=eta/A<=eta/gamma`.  If the repaired coordinate is not the selected
collision partner, or its better endpoint is Quit, the two displayed label
lower bounds are retained.  A simultaneous multi-player repair can change
the forced endpoints and is correctly excluded from this conclusion.

## Addendum: Propositions 6B--6C

I independently checked the later length-free posterior coupling and mover-
clock dichotomy.  **Verdict: both are VALID ordinary mathematics in their
stated one-ray, finite-block scope.**

For Proposition 6B, at a suffix entrance `s` the two residual mover laws are
mixtures of the same conditional component laws with weights `F_s(a)` and
`F_s(b)`.  Therefore every event of the mover's complete future law differs
by

```text
(F_s(a)-F_s(b))*(Pr_T(E)-Pr_S(E)),
```

whose absolute value is at most `|F_s(a)-F_s(b)|`.  Interval survival is one
such event.  Multiplication by the common opponent-survival factor proves the
same bound for joint survival and for deletion of any player other than the
mover; deletion of the mover leaves exactly the common opponent law and has
zero discrepancy.  The direct identity

```text
F_s(a)-F_s(b)=S_s T_s(a-b)/(M_s(a)M_s(b))
```

then gives `Pi<=min(1,h/rho^2)` under the displayed hypotheses.  No rowwise
telescope or hidden packet-length factor is needed.  The semantic/debt
constant in (6B.2) follows from the same complete-law coupling and is
correctly kept separate from the clock constant.

For Proposition 6C, `M_L(a)F_L(a)=aT_L` is exact.  Thus
`F_L(a)>=beta>0`, `a<=h`, and `T_L<=1` imply
`M_L(a)<=h/beta`.  Joint survival and every deletion other than deletion of
the mover contain this mover-survival factor, while deleted-mover survival is
the unchanged opponent-only product.  Equations (6C.1)--(6C.2) therefore
have the correct orientation and cover the stated boundary division.

The scope qualification is essential and accurate: these are interval-clock
statements for one supplied ray-matched finite word.  They neither preserve
the initial atom/orientation at its posterior endpoint nor produce a reusable
source-matched next packet, and Proposition 6C does not claim every-suffix
contraction from its one cutoff inequality.

## Addendum: Proposition 6E

I also audited the exact residual prescribed-atom account.  **Verdict: VALID
ordinary mathematics, with the rectangle statement remaining only a
conditional reuse of the algebra, not a selected rectangle port.**

The event decomposition is exact:

```text
A_0-A_pre=(S c_0-T c_1)r_C
         =[S(c_0-c_1)+(S-T)c_1]r_C.
```

After conditioning the entrance mixture, its residual law has target
posterior `F=aT/M`, so comparison with the full target residual multiplies
the conditional component difference by
`1-F=(1-a)S/M`.  Dividing the displayed decomposition by `S>0` therefore
gives precisely (6E.1), with the stated sign and normalization.  This remains
valid for terminal atoms occurring after the cutoff; the complementary
before-cutoff part is exactly what `A_pre` removes.

Since `M<=1`, `a<=h<1`, `|c_1|<=1`, and `|r_C|<=R`, a positive numerator is
bounded below by `A_0-|A_pre|-R|S-T|`, while `(1-a)/M>=1-h`.  This proves
(6E.3).  The eventual `K A_res>=q/4` conclusion from `K A_0>=q/2` follows
after making both `h` and the displayed error small; it tacitly uses the
packet's fixed positive normalization constant `K`, as intended.  The
finite-block failure trichotomy (6E.5) also has the correct constants: if
both listed terms are below `A_*/4`, their sum is below `A_*/2` and (6E.3)
contradicts the proposed residual loss.

No posterior lower bound is missing from this identity—the factor `S` in the
conditional atom cancels the same factor in `1-F`.  The surviving upstream
selection problem is exactly as stated: one still needs a positive-survival
cutoff at which the atom has not mostly occurred and `|S-T|` is small.  For a
rectangle arm, incorporating the common response into both laws makes the
same algebra available, but survival of that response to an appropriate
cutoff is additional data and is not proved by Proposition 6E.

## Addendum: Proposition 6G

I checked the affine prefix-port reformulation.  **Verdict: VALID ordinary
mathematics with the stated accounting-only scope.**

For every event `E`, the entrance mixture satisfies

```text
P^a(E)-P^0(E)=a(P^1(E)-P^0(E)).
```

If the first arm of (6E.5) holds, then `A_pre!=0`, hence `r_C!=0`, and

```text
|P^a(E_pre)-P^0(E_pre)|
 =a|A_pre|/|r_C|
 >=a A_*/(4R)
```

because `|r_C|<=R` and `R>0`.  If the second arm holds, the identical affine
calculation for `H_L` gives

```text
|P^a(H_L)-P^0(H_L)|=a|T-S|>=a A_*/(4R).
```

Thus the alternatives, constants, and absolute-value orientations in
(6G.1)--(6G.2) are exact.  Under `a>=kappa h` the lower bound is indeed a
fixed constant times `h`.  As the note emphasizes, this is neither a signed
progress law nor a lower bound on absorption/deleted-clock charge: one arm is
only a specified pre-cutoff terminal event and the other is an absolute
survival displacement.  Since both still vanish at scale `h`, Proposition 6G
does not itself reconnect a residual atom or improve the local clock modulus.

## Addendum: Proposition 6H

I audited the fixed-root prefix image and the actual-semantic boundary
example.  **Verdict: VALID ordinary mathematics in the explicitly fixed-root
scope.**

For a fixed product root, prescribed successor dependence on the tail is
exactly joint Continue mass `beta`, giving (6H.1) and the inverse factor
`1/beta` when `beta>0`.  Player `i`'s forced-Quit endpoint is tail-independent,
while its forced-Continue endpoint reads the tail cap exactly on all-opponents-
Continue, with coefficient `O_i`.  Hence

```text
b_i=max(Q_i,C_i+O_i d_i)
```

and the three cap-image cases (6H.4)--(6H.5) follow exactly.  In particular,
when `O_i=0` the cap coordinate is rigid, and when the Quit branch is selected
the current cap is pinned at `Q_i`; the algebra does not assert carrier
membership or `d_i>=v_i`, which are correctly listed separately.

In the two-player example, the prescribed payoff is zero and player `i`'s
best response earns one exactly on the probability-`p` simultaneous event,
so `Sem(sigma^p)=((0,0),(p,0))`.  At the frozen `p=1` literal root,
`Q_i=1`, forcing every fixed-root prefix image to have cap at least one.
Thus no `p<1` pair lies in that image although the semantic distance is
`1-p`.

This is only fixed-root non-openness.  Moving the first root's `j`-marginal
from `1` to `p` and using the all-Never residual realizes `Sem(sigma^p)`
exactly, with root displacement `1-p`.  The example therefore does not rule
out nearby-root reprojection, a separate bridge, or the existential packet
construction; the note's scope statement is correct.

## Addendum: Proposition 6I

I independently checked the exact-word minimum-tube estimate after Euler's
review.  **Verdict: VALID ordinary mathematics.**

At one executable semantic prefix, a player can follow its prescribed current
randomization and, only after joint Continue, switch to a tail best response.
Therefore current debt dominates joint Continue mass times tail debt.  Rowwise
iteration and summation give `beta D(z)<=D(x)` with the displayed chronological
orientation.  Coordinatewise `delta`-closeness of both prescribed and cap
coordinates changes each debt by at most `2 delta`, so
`D(x)<=D_*+2n delta`; rearrangement gives exactly (6I.1).

For `s>=0`, the carrier sublevel is compact and nonempty, distance to the
closed minimum set is continuous, and hence the maximum defining `mu(s)`
exists.  The standard compact-subsequence contradiction proves
`mu(s)->0` as `s` decreases to zero.  Substituting
`alpha=1-beta` yields (6I.5), and replacing actual absorption by an upper
bound on frozen absorption plus clock discrepancy is valid because the
right-hand excess bound is increasing in `alpha<1`.

The scope is exact and important: this locates the residual pair near the
whole minimum set only.  It preserves neither the original base point nor a
component fiber, atom label, mover, observer, or canonical next ray.  For the
paid re-entry problem it can close the scalar debt tube only after a separate
source theorem supplies small actual block absorption/entry error and uniform
port access over that minimum set.

## Addendum: Proposition 6M

I independently checked the claimed failure of the sublinear-radius
inference.  **Verdict: VALID ordinary mathematics.**

Proposition 6I supplies only the qualitative compact sublevel modulus
`dist(z,MinimumSet)<=mu(excess)`, with `mu(s)->0`.  Substituting an
`O(h)` excess therefore gives exactly `mu(Ch+o(h))`; no rate comparison with
`h` follows from compactness.

Both scalar models are exact.  For `E(x)=x^2` on `[-1,1]`, the distance of
the `s`-sublevel to `{0}` is `min(1,sqrt(s))`, so
`mu(Ch)/h=sqrt(C/h)` for small `h`, which diverges.  For `E(x)=|x|`, the
modulus is `min(1,s)`, and `mu(Ch)/h` tends to `C`, not zero.  Thus even a
linear error bound converts first-order excess only to first-order distance;
it does not supply the `o(h)` availability loss.

The scope statement is also correct.  These examples do not prove that the
actual residual has first-order displacement, because Proposition 6I gives
only an upper bound and source geometry could add cancellation.  They refute
only the inference from `O(h)` absorption plus a qualitative minimum-set
modulus to a sublinear operational radius.  A direct `o(h)` fiber return, a
strictly sharper excess estimate together with a quantitative error bound, or
a different cancelling radius remains necessary.
