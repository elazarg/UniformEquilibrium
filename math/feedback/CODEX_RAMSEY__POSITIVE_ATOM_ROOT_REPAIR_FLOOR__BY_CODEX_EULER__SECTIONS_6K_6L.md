# Review of Sections 6K--6L / Propositions 6K--6L

Reviewer: `CODEX_EULER`

## Verdict

**VALID ordinary mathematics, with the stated common-fiber scope.**  The
four-player split replacement has `O(h)` one-row absorption, exact two-label
and every-player-deleted exposure, and a fixed same-orientation atom remaining
after conditioning.  Proposition 6L correctly abstracts the construction:
its denominator, posterior, atom, and semantic-seam constants all check.  It
does not supply arbitrary reached-source entry, a positive-minimum source, or
later every-interval clock control.

## Proposition 6K

At date zero, each mover first selects its full replacement with outer weight
`h` and then that replacement Quits with probability `c=1/4`.  Each literal
marginal hazard is therefore `h/4`, and the joint one-row absorption is

```text
1-(1-h/4)^2=h/2-h^2/16.
```

This lies between `h/4` and `h/2`.  Deleting either reset mover leaves the
other hazard `h/4`; deleting `a` or `o` leaves both.  Thus joint and every
one-player-deleted exposure are at least `h/4`, and the root mesh is exactly
`h/4`.

For the initial `{m}` comparison, a full `m` target Quits at date zero with
probability `1/4` or at date one with probability `(3/4)(1/2)`, for total
probability `5/8`.  The independent outer `n` law must avoid its sole date-zero
Quit, an event of probability `1-h/4`.  Hence the full-target-versus-source
terminal mass difference is exactly

```text
(1-h/4)*5/8,
```

and multiplication by `r_o({m})=-1` gives the claimed positive orientation.

Conditioning on `m` Continuing at date zero updates its target weight to

```text
F=[h*(3/4)]/[(1-h)+h*(3/4)]
 =(3h/4)/(1-h/4).
```

This is increasing on the stated interval and equals `1/5` at `h=1/4`.
After the cutoff, the conditional source is Never and the conditional full
target Quits at date one with probability `d=1/2`.  Comparing the reached
mixture to the full target therefore gives

```text
A_res=(1-F)/2 >= 2/5.
```

Since `A_0(h)<=5/8`, this is also strictly more than `A_0(h)/2`.  Conditional
survival removes the only Quit branch of the `n` target, making its residual
source and target laws both Never; no omitted residual collision changes the
calculation.  All probabilities are rational for rational `h`.

## Proposition 6L

With entrance target weight `a`, source prefix survival `S`, and target prefix
survival `T`, actual survival is

```text
M=(1-a)S+aT.
```

Thus

```text
1-M=(1-a)(1-S)+a(1-T)<=Ch+h.
```

Furthermore,

```text
F=aT/M
 <= h/[(1-h)(1-Ch)] = pi(h),
```

because `aT<=h` and `M>=(1-a)S>=(1-h)(1-Ch)`.  The stated domain condition

```text
(1-h)(1-Ch)>h
```

simultaneously makes the denominator positive and gives `pi(h)<1`.  The
assumption `T>0` makes the conditional target component nonvacuous; the same
domain condition also forces `S>0`.

If `c_0,c_1` are the conditional residual terminal probabilities for the
fixed label, then the reached residual probability is

```text
(1-F)c_0+F c_1.
```

Its difference from the full target is `(1-F)(c_0-c_1)`, so the exact signed
atom lower bound is `(1-pi(h))A_*`.

Coupling the reached residual mixture to the source conditional component
fails only on the target-mixture branch, with probability at most `F<=pi(h)`.
For rewards bounded by `R`, prescribed payoff changes by at most `2R*pi(h)`.
The same bound is uniform over every unilateral behavioral deviation, so it
survives taking the best-response supremum and gives the cap seam
`2R*pi(h)`.  Subtracting prescribed from cap gives the debt seam
`4R*pi(h)`.  These constants and the unrestricted-deviation interpretation
are correct.

## Scope

Proposition 6K shows only that the earlier obstructions are sharp: temporal
splitting can reserve a same-orientation residual atom while paying an early
two-label clock at `O(h)` absorption.  Its semantic head is the head generated
by the chosen prefix and common component fiber.  It is neither
positive-minimum data nor an entry theorem for an arbitrary nearby reached
semantic source.

Proposition 6L assumes precisely the additional high-survival source and
conditional residual atom fields that the checked static atom access does not
store.  The `2R*pi(h)` estimates concern the immediate residual port.  For a
later finite word, every-interval clock control still depends on the direct
posterior modulus `Pi_L` and fresh likelihood/reach information; the argument
does not identify `Pi_L` with `pi(h)` or smuggle in persistent clocks.  The
note states all of these limitations accurately.
