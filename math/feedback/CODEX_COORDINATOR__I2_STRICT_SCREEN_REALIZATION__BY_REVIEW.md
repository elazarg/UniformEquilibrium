# Independent whole review of exact quiet-contact tails

Reviewer: LARGE_ROOT_SUCCESSOR. I did not author the construction. This is an
ordinary mathematical review; no Lean file was edited or built.

Reviewed artifact: math/notes/CODEX_COORDINATOR__I2_STRICT_SCREEN_REALIZATION.md.
SHA256: 6653b47af934431857c986343b2045cb5ff77b9a781dea9d16f490aae97c11a8.

Verdict: PASS for all stated claims. No unresolved mathematical objection.
The result realizes strict local common-support screens, including the
extreme-law property, for arbitrary fixed finite higher rewards. It does not
supply a positive absorbing gap, an original head, or global minimality, and
therefore closes no UE class and does not refute UE.

## Exact response and moment equations

I independently derived the conditional Never numerator by splitting the
pair law into singleton, ordered, and tied outcomes. The partner contact
identity gives b_order=(1/rho-1)T. In normalized variables this yields
 g*u+d*v+g*u*v+K*t.
Expanding immediate Quit over the four opponent action outcomes gives
 rho*X*u+rho*X*u*v+Y*b+(Y+rho*E)*u*b.
Their difference is exactly H_j in (3), including both passive-pair and
participant-triple coefficients. The common positive denominator is
(1+u)(1+v). At each date its sign is the sign of the full deadline-minus-Never
comparison, after multiplication by the positive probability that the other
clocks have survived to that date. Thus no prior-calendar payoff was omitted.

The recursions for u,v,t and the factor rho in the tie sum are correct. For
b_n=rho*lambda*u_n, its geometric tie sum is
 rho*lambda*u_n^2/(2-rho), as stated. I symbolically checked the general
substitution producing (5), not only the rational example.

## Sequence-space construction

The weighted sequence space is a Banach space by its isometry with l-infinity.
For |r|<q the displayed forward inverse has value zero at index0 and solves
L Rf=f at every index; its norm is at most 1/(q-|r|). For |r|>q the backward
sum is absolutely convergent and solves the same equation, with norm at most
1/(|r|-q). Negative r causes no change in the estimates. The explicit two
choices for q guarantee a usable weight in (a^2,a). In particular r=a^m
creates no omitted resonance case: the argument does not invert coefficientwise
in a power-series basis.

For Tw, summing absolute values gives
 rho*u0*(1+q)*a^n*q^n*||w||/(1-a*q).
This proves both the stated Banach norm bound and the stronger tail estimate
used later. The other terms in N carry u_n<=u0, so its operator norm is at most
u0*D. Banach contraction therefore applies to the entire weighted sequence
space, before any positivity assumption, and gives (8). Applying L to its
fixed-point equation supplies exact contacts, not an approximate solution.
When Q=0 the selected fixed point is zero, correctly including that case.

Because q<a, (8) implies |w_n|<=C0*u0*u_n and the same uniform small relative
bound on successive differences. A table-dependent reduction of u0 makes
v_n, b_n and v_(n+1) positive for all n simultaneously. They tend to zero.
Telescoping then gives the exact total masses and positive Never masses after
the displayed Np,Ni normalization. The tie series is absolutely convergent
and positive after this step, so its interpretation as the actual tie moment
is established rather than assumed. In particular the Tw remainder is
O(u0*u_n^2), since (q/a)^n<=1; this validates the strongest estimate in (9).

## Full caps, extremality, and scope

The partner's every date response is tied by J alpha_n=G P_n. The constructed
h comparisons vanish exactly. The k comparison has a strictly positive linear
coefficient times u_n with an O(u0*u_n) remainder, uniform in n. The pivot
comparison is positive because beta_n/I_n=rho+O(u0) and A-rho*C>0. Hence all
full caps equal Never and all observer debts vanish. Complete private behavior
induces a deadline or mixture along the unique live history; no finite-query
or bounded-deviation restriction enters this argument. Positive pivot mass at
strictly inferior finite deadlines gives strictly positive pivot debt.
The exact debt formula and limit (A-rho*C)/(2-rho) check algebraically.

For extremality, fixed I fixes Ni. Thus every h-gap is affine in the varying
partner law when the pivot law and I,T are retained. A midpoint with gap zero
forces both feasible endpoint gaps to vanish at every date. Nonvanishing of
Y_h+(Y_h+rho E_h)u_n then determines b0 from fixed initial moments and determines
all subsequent atoms recursively. This proves extremality in exactly the
stated infinite feasible set; no compactness or generic-rank assumption is
silently substituted for uniqueness.

I independently checked the rational control: H_h=0,
H_k=5u/3+u^2/18, pivot gap I/2, and pivot debt PI/3. The strict first-order
screen yields lambda=-c_h/b_h and the other quiet margin precisely through
its strict cross inequality. Thus every strict passing screen with Y_h nonzero
is realized, while the equality boundary is correctly left open. The result
persists under the stated singleton/pair perturbations and allows all fixed
finite higher rewards; the allowed small mass may depend on those rewards.

I inspected quittingContinuationBestResponseValue_rootThenContinuation_eq_max
in UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean and the current
pair-contact replacement/source formulas. These are existing semantic
interfaces, not formalization of this new construction. The theorem decisively
prevents using local common-support calendars and their extreme quiet contacts
alone as an I2 contradiction. It does not replace the missing global source
or compensated-activation argument.

## Final canonical additions

I reread the whole canonical artifact. Its mathematical construction and
bounds are unchanged; the added link makes no new mathematical assumption.
The added solved-game control is correct: on pure coalition01 the displayed
complete table gives every recipient reward zero. If owner0 or1 Continues,
the other still quits surely and that owner's singleton payoff is -1.
If quiet owner2 or3 joins, its reward on012 or013 is still zero. These
comparisons exhaust every unilateral behavioral replacement because at least
one other prescribed owner quits at the first date. Thus pure01 is an
absorbing exact native Nash profile, and this local pair-tail example has no
positive absorbing gap. The text correctly preserves the distinction between
this solved exact control and the open raw neighborhood's local realization
claim. Whole final verdict remains PASS with no unresolved objection.
