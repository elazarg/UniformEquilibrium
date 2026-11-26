# Independent review of the complete finite-calendar actual geometry

Reviewer: APPROXIMATE_GEOMETRY.
Artifact: math/notes/CODEX_COORDINATOR__BOUNDED_CROSSING_SELECTION.md.
Reviewed SHA256: b8a4301204706ffa6c3277eb79e32630b78e21ab02bca83e1708b9623aa0d128.

Verdict: PASS for the complete Section8 classification, minimum, and path
barrier. The checked integration clarifications are present in the pinned
version. No unresolved mathematical objection remains.
The introduction and final scope statements accurately distinguish finite exact
profiles from infinite calendars and positive-debt approximants.

Independence boundary: I did not author the Section8 classification. I developed
Section10's exact-fibre theorem, so my Section10 check is an AUTHOR integration
check, not an independent proof review. FIBER_REVIEW independently reviewed its
complete source proof at SHA256
336d00a42732d6486565e590f6eab6db49ba659e069fc38ff1332b73860ca7b1;
that independent report is /tmp/EXACT_FIBER_REVIEW.md, SHA256
a5b43136a275e778a8fe726fbb02a84587a2fdf4af0d9bce81150139a787cff1.
The coordinator also requested FIBER_REVIEW to check the final integrated
Section10 directly. This review does not substitute self-review for that check.

## 1. Exact claim checked

For the binding table gamma=(-194/3599,5408/3599,6), every actual finite-calendar
native exact Nash profile with positive joint Never mass and min U<=0 has the
full(U,B,e,N) annotations of AllNever, solo0, pair13 over solo0, or triple123
over solo0. The pair range is 0<r<=1/2; the triple range is 0<r<1/2.
The nonsolo marked annotation class has unique minimum nu=3599/9000 at the
binding pair endpoint. Its two arcs form a loop attached to the solo interval
only at AllNever. Every continuous path in the marked finite-calendar exact
annotation set from the binding point to smaller nu passes through nu=1.
Calendar lengths may be unbounded along that path.

This does not assert a positive unrestricted behavioral gap, a counterexample
to UE, or a corresponding classification for genuinely infinite calendars or
closure points of positive-debt profiles. Pure0 remains an absorbing equilibrium.

## 2. Full-support root exhaustion

I independently derived the core gap factorization

    g_i=(1-q0)g_i^core-(1+gamma_i)q0.

All gamma_i>-1. A sure0 therefore forces all core owners to Continue. When
q1=0, the only possible equality in g3^core occurs at r=q2=0; activity of3
then forces2 to Quit, contradiction. With3 quiet, activity of2 either has
negative own gap or makes C0=-3q2<0 at r=0, again forcing incompatible sure0.
Thus either all core owners are quiet or q1>0.

In the quiet-core case, player1's comparison is exactly
ar-q0(1-a+ar)<=0, giving the displayed solo0 threshold. The aggregate update
r'=q0+(1-q0)r preserves the prescribed and Never payoffs and all N. A single
aggregate solo0 root is exact Nash from AllNever since gamma_i>-1, so its
full caps also match.

For q1>0, the forbidden q2 interval and high-branch row0 bound are correct.
At q2=97/99, the maximal C0 is -91/99. On the low branch, a positive q2
requires g2^core>=0, giving S>=gr/(4+gr); C0 is then strictly positive.
Hence q0=0. The pure endpoints q1=1 and q3=1 are inconsistent with this
low branch. The single-owner1 possibility is excluded separately at r=0
and r>0. This leaves exactly supports12,13,123, not merely a census of
interior roots. No support containing0, sure core owner, pair23, or singleton
has been omitted.

## 3. Pair and triple algebra

The pair12 odds, quiet3 gap, and all-positive output are correct. Exact worst
endpoint coefficients are

    4g-404a-6+(28/3)ga = -816439130/38858403 <0,
    6-2g/3+4a-8ga = 177422458/38858403 >0.

Thus this branch always leaves the marked set. Pair13 exists precisely when
3r(2r-1)/7198<=0. Its binding-table C2 formula is
r(3614-2r)/[(r+2)(3599+2r)], not the earlier unbinding-table numerator6001.
The integrated version states this distinction explicitly.

For triples, q2<=4ar/(1+4ar) bounds its odds by4ar, so the denominator
97-2y is positive. The forced formulas for x,z and the endpoint formula
for F were independently checked symbolically. The strict endpoint value
is for r>0; at r=0 it equals zero.

The derivative estimates can be checked on larger rational rectangles:

    x_y >=1170/(12+7/4)^2 >61/10,
    z_y > -(97/4)/(97-1/2)^2 >-1/300,
    x <(6+101/4)/12 <3.

These imply F_y>18. For r<=1/2,y<1/8,

    x_y >1191/(12+7/8)^2 >7,
    x <(3+101/8)/12 <4/3,
    z_y >-(97/4)/(97-1/4)^2 >-1/380.

Together with the signs at y=0 and y=4ar, this proves exactly one positive
triple for0<r<1/2 and none outside that interval. No numerical root search
is being used as an exhaustiveness argument.

## 4. Full-cap semantics and every finite calendar

The whole profile's positive joint Never mass makes every finite
all-Continue history have positive reach. If a conditional tail had a
profitable replacement, using it only after that history would profit in
the original profile. Every conditional tail is therefore full Nash, and
each stage is a one-step Nash root against that exact tail payoff.
Conversely exact backward Nash prefixing from AllNever preserves all full
response caps, by the full max recursion. This supplies the required
actual-game adapter to finite root words.

Empty dates require care: at a zero root, immediate native Quit earns0,
so a zero root is Nash only at a coordinatewise nonnegative continuation.
One cannot insert an idle date before a negative marked tail. The integrated
proof explicitly handles this. Deleting a zero period from an already exact
profile is harmless; silently adjoining one would not be.

The triple estimates imply the general trap inequalities of Sections6–7.
I checked all output signs and bounds; in particular C2<.503r, C3>3r,
V>39r, and0<A<100r/1799. The same inequalities hold for the binding pair
using its correct formula. Every nonsolo marked output has just the pair12
Nash continuation, which is all-positive; only AllContinue can follow that.
Together with the exhaustive AllNever/solo classification, this proves the
claimed induction over every finite calendar and arbitrary supports.

## 5. Global minimum on the loop and the exact path barrier

Pair13's survival decreases strictly up to r=1/2. For triples, the estimate
y<(1/2-r)/47000 bounds (1+x)(1+y)<5/4. Also1-r>1/2 and
1+z<=1+1/3599. Therefore every triple has strictly larger survival than

    (1/2)/[(5/4)(1+1/3599)] =3599/9000.

The parameter is recovered from N0=1-r. N2 distinguishes the open triple
and pair arcs. F_y>20 gives a continuous triple arc up to each endpoint;
it meets the pair only at AllNever and the binding point. Hence the loop
claim is justified, rather than merely suggested by a picture.

For the path barrier, take the compact union K of the two closed core arcs.
Its Never product is at least3599/9000. At a first exit from K, continuity
keeps nu positive in a neighborhood. The classification forces nearby
points outside K onto the solo arc. But K meets the closure of the solo
arc only at AllNever. This proves the barrier even when calendar lengths
are not uniformly bounded and the eventual endpoint is absorbing.

Sharpness uses an actual two-date path: decrease r to0 along pair13;
then increase a solo0 hazard at the FIRST physical date from0to1. At the
junction both profiles converge to AllNever. Leaving the solo0 hazard at
the second date behind an empty first date would be false; the integrated
version retains the corrected first-date construction.

## 6. Section10 author integration check and limits

The integrated statement retains the reviewed quantifiers and constants:
for ANY semantic closure point, exact U,e,N are achieved on40k+64 Fin4
dates with coordinatewise cap error12M/k. The proof fixes k before taking
a bounded-calendar compactness limit. It preserves absence as well as
presence of initial/interior gaps and keeps late finite replies distinct
from Never. The marked-source consumer specializes to Fin4 before using
the14M nu^(1/4) repair estimate.

The same source's U=e=v and original N are exact across approximants, but
its zero debt is only approached. Therefore Section8 cannot be applied to
these positive-debt profiles. The countable finite-polynomial hierarchy
characterizes membership of(v,v,v,N) in the full semantic closure; it is
not a finite UE decision procedure or a new raw reward-class exclusion.
The final scope statement preserves these distinctions.

## Verification record

I read the whole integrated Sections8 and10, the introduction, remaining
target, and the earlier Section6–7 trap proof used by Section8. Symbolic
rational algebra checked the triple endpoint identity and derivative
expressions. Eighteen independent exact rational inequalities checked all
quantitative bounds used above, including output signs and the strict
survival denominator comparison. These checks passed. They support, rather
than replace, the all-support and arbitrary-finite-calendar proofs.
I also ran the final actual-geometry checker, SHA256
4fbb5e272895cf62e4bdd59c2e67258ec43646583fa949b5478e16c61745d7e5;
all three check groups passed. No Lean, build, git mutation, or tracked-file
edit was performed by this reviewer.
