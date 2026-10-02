# Final export-gate audit: same-stage endpoint monodromy reduction

Reviewer: Codex Monodromy

## Verdict

**APPROVE AFTER THE EXACT REPAIRS BELOW.** The constants, quantifiers,
circulation identity, Fin4 dichotomy, boundary cycles, and strict
conjecture-facing reduction are correct. The claim `K <= 8` is safe, including
directed two-cycles, after adding the explicit two-cycle sentence below.

There is one semantic precision issue that must be repaired before placement
is approved. The checked
`quittingStagePureEndpointBehaviorDeviation` is a canonical time-only strategy
which agrees with the source on its live-root marginals before and after the
marked date. It need not equal an arbitrary source strategy on histories which
are already absorbed or otherwise off the canonical live history. Therefore
the present sentences saying that this checked update retains the player's
*complete literal behavior* outside the marked date, or that the canonical
profiles equal the original behavior profile outside that date, are not
literally justified.

The clean repair is to define the mathematical operation as the direct
one-date override below. It is a legal behavioral deviation, preserves the
complete profile outside the marked date, and has the same live root sequence,
terminal outcome law, payoff gain, and routed mass as the already-checked
canonical deviation. This makes repeated root equality genuinely imply
equality of complete behavioral profiles.

The Research adapter has one presentational seam as well. Its proof reaches
the routed-transfer subsequence only in the `eventually not TailRow` branch,
and that negation is exactly the low-tail inequality at the selected scale.
The public `RoutedTransferSubsequence` structure does not retain this negated
field. The ordinary mathematical adapter is complete, but the Lean handoff
must either expose the field or invoke monodromy inside the same proof branch.

## Required patch 1: define the literal operation exactly

Replace the paragraph beginning “At date `t`, a **same-stage endpoint
update**...” by:

```markdown
At date `t`, a **same-stage endpoint update** by player `p` is the following
literal one-date behavioral override.  Against the current profile `rho`,
choose a pure action `a` maximizing `p`'s one-row payoff at the unique live
all-Continue history of date `t` against the literal continuation payoff, and
define

\[
\widehat\rho_p(s,h)=
\begin{cases}
\operatorname{pure}(a),&s=t,\\
\rho_p(s,h),&s\ne t,
\end{cases}
\qquad
\widehat\rho_j=\rho_j\quad(j\ne p).
\]

Thus every player's complete behavior is retained before and after date `t`,
and every opponent's complete strategy is retained everywhere. Route the
marked coalition through the same Boolean coordinate update.
```

This definition resolves probability mode and agency completely: the update
is one legal unilateral behavioral replacement and introduces no correlation
or extra randomization.

## Required patch 2: connect the literal override to checked declarations

After the three bullets in “Source correspondence,” add:

```markdown
The checked endpoint theorem is stated using
`quittingStagePureEndpointBehaviorDeviation`, which canonicalizes the mover's
off-path behavior. The literal one-date override used here has exactly the
same live-root sequence as that checked deviation. Since a quitting game has
only the all-Continue live history before absorption, the two deviations have
the same terminal law, terminal payoffs, marked stage mass, and mover gain.
The new formalization therefore needs one local live-root congruence lemma (or
may state the finite iteration directly for the canonical family). No
strategy-class restriction is involved.
```

This is a proof, not a deferred mathematical assumption: equality of terminal
data follows directly because every finite active history is the unique
all-Continue history and the two strategies agree there at every date.

## Required patch 3: correct the canonical-family wording

Replace:

```markdown
After the preliminary phase, all profiles belong to one canonical family:
they equal the original profile outside date `t` and are indexed only by the
pure root used at `t`. Repetition of a root is therefore equality of complete
behavioral profiles, not merely equality of payoffs or semantic pairs.
```

by:

```markdown
After the preliminary phase, every profile equals the original complete
behavior profile at every date other than `t`; at date `t` it is indexed only
by the pure action profile used there. Hence repetition of that pure root is
equality of complete behavioral profiles, not merely equality of terminal
laws, payoffs, or semantic pairs.
```

This statement is literally true for the direct one-date override.

In the Lean handoff, replace “Define the post-preliminary canonical profile
family explicitly as the original behavioral profile with one time-indexed
product root replaced” by the more exact instruction:

```markdown
Define the post-preliminary finite profile family by overriding every
player's strategy at exactly the marked date (at all histories of that date)
and retaining the original strategy at every other date. Prove that its live
root word agrees with the existing canonical stage-endpoint deviation. Do not
quotient arbitrary behavioral profiles by live-root equality.
```

## Required patch 4: make `K <= 8` formally safe

Replace the opening of “Fin4 geometry” by:

```markdown
If `K = 2`, the two vertices differ by one cube coordinate and have nonempty
intersection, so (6) holds immediately. Suppose `K > 2`. Minimality of the
repeated segment makes its vertices distinct except for the closing endpoint;
its underlying undirected cube walk is therefore a simple cycle of length at
least four. The induced four-cube graph on subsets of cardinality at least two
is bipartite. Its odd side consists of the four triples, so this simple cycle
is even and has length at most eight.
```

The remainder of the star/triangle proof then applies. Thus the safe exact
claim is

\[
K\in\{2,4,6,8\},
\]

and in particular `K <= 8`.

## Required patch 5: state the checked-adapter seam honestly

At the end of “Source correspondence,” add:

```markdown
In the checked proof of
`QuittingMinimumLawCausalSuffixAtom.nonempty_tailEscape_or_routedTransferSubsequence`,
the routed-transfer arm is selected only after `TailRow` is eventually false.
With the packet's stage scale `lambda = mu^2/8`, that negation is precisely
the low-tail inequality `E < lambda * D_*/2` used here. The currently public
`RoutedTransferSubsequence` structure does not retain this inequality as a
field. The formalization should expose it, or compose this theorem inside the
existing `hnotTail` proof branch. This is a public-interface omission, not a
new mathematical hypothesis.
```

Also add to the source audit:

```markdown
No external literature theorem is used in the new finite iteration or Fin4
classification. A narrow repository search found no existing theorem with
this literal same-stage closed-cycle conclusion.
```

## Gate checklist after repair

1. **Exact statement:** pass; `n`, `lambda`, `D_*`, stage mass, tail excess,
   number of updates, and both outputs are quantified.
2. **Complete proof:** pass after the literal-override congruence is stated as
   above. There is no deferred producer inside the theorem.
3. **Probability/agency audit:** pass. Stage mass is unconditional; every edge
   is one legal behavioral replacement; caps remain unrestricted.
4. **Adapter or strict narrowing:** pass. The Research causal/anti-diffusion
   proof supplies the low-tail row in its non-tail branch, and this theorem
   closes literal same-row regeneration, leaving only two finite Fin4 cycle
   geometries.
5. **Boundary tests:** pass. Singleton routing, failure of low-tail, a
   common-host cycle, and a complementary-pair cycle are all displayed.
6. **Source audit:** pass after the no-literature/no-duplicate sentence.
7. **Independent review:** pass; two substantive reviews are linked.
8. **Lean handoff:** pass after the literal-override wording and the missing
   Research field are identified.

## Constants and examples rechecked

- The general endpoint floor is
  \(mD_*/(2n)\ge\lambda D_*/(2n)\).
- On `Fin 4` this is \(\lambda D_*/8\).
- There are \(2^n-n-1\) pure nonsingleton roots.
- The circulation sign in (5) is correct:
  telescoping gives zero equals mover losses minus gains plus nonmover changes.
- The common-host cycle
  `01,012,02,023,03,013,01` is a valid six-cycle with common player `0`.
- The complementary-pair cycle
  `01,013,0123,123,23,023,02,012,01` is a valid eight-cycle with empty total
  intersection and complementary pairs `01`, `23`.
- Independent exhaustive enumeration gives 37 undirected simple cycles of
  length at least four in the induced Fin4 graph and no violation of (6).

After the five textual repairs above, I explicitly approve the packet's
placement in `exports/`.

## Post-repair confirmation

The assembled packet was reread after all five repairs were applied. The
literal one-date override is now defined exactly, its correspondence with the
checked canonical deviation is stated, the Research low-tail interface seam
is disclosed, and directed two-cycles are separated before the simple-cycle
argument. The constants and examples remain unchanged and correct.

**Final gate verdict: approved for placement in `exports/`.**
