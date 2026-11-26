# Joint-return root geometry and the sign-changing-root extension

Status: ordinary mathematics, not checked in Lean. This internal note
strengthens scalar root selection in the two frozen joint-return packets. All their other payoff and deviation guards
remain explicit; arbitrary Fin4 remains open. The results concern finite
private independent hazards and unrestricted behavioral deviations, exactly
as in those packets.

## 1. Automatic admissible odd root

Let beta,e,f,k,h,d>0, s<beta, eta>0, w real, and suppose
Delta=f*e*k-h*beta*d>0. Here w=Z3(02). Set

    a=beta-s>0, omega=w+d-e,
    D=d-omega*b, E=D-e*b=d-(w+d)*b,
    B=beta-s*b, T0=k-(k+a)*b,
    F=f*e*T0-h*B*D,
    P_eta=F*E-eta*e*b*(B*D+e*T0).

Define r_C=k/(k+a), and r=min(r_C,d/(w+d)) if w+d>0,
otherwise r=r_C. Then 0<r<=r_C<1. For 0<b<r, both T0 and E
are positive, hence D=E+e*b>0, x=e*b/D lies in (0,1), and
C=b*a/(1-b) lies in (0,k). Conversely, these admissibility inequalities
are equivalent to 0<b<r under the stated positive parameters.

At b=0, P_eta(0)=d*Delta>0. At b=r, T0,E>=0 and at least one
vanishes; D=E+e*r>0 and B=beta*(1-r)+a*r>0. If E=0, then
P_eta(r)=-eta*e*r*(B*D+e*T0)<0. If T0=0, then
P_eta(r)=-B*D*(h*E+eta*e*r)<0. These formulas include the tied
boundary, so no division by a vanishing factor occurs.

The nonzero polynomial P_eta therefore has an interior zero by IVT.
Moreover at least one interior zero changes sign from positive to negative:
factor P_eta over the real numbers, or traverse its finitely many roots
between the opposite-sign endpoints. That zero has odd multiplicity, which
is one or three since deg(P_eta)<=3. At every admissible zero F>0, by
F*E=eta*e*b*(B*D+e*T0)>0. The selected root gives T=x*eta/(1-x)>0.

This removes a supplied-root hypothesis from the core-free packet on the
Delta>0, d>0 chamber, and supplies the odd root required by the extension
of the negative-owner-value packet in Section 5. Other raw guards must
still be verified at at least one selected root.

## 2. A sufficient uniqueness and simplicity condition

If omega=w+d-e<=0, every eta>0 has exactly one admissible root, and it
is simple. Indeed D is nondecreasing and positive. On (0,r), put

    R=e*T0/(B*D), L=E/(e*b),
    H=(f*R-h)/(1+R), eta_map=H*L.

The derivative of T0/B is -a*(k+beta)/B^2<0, so R'<0.
Also L'= -d/(e*b^2)<0, and dH/dR=(f+h)/(1+R)^2>0.
Where eta_map>0, H>0, so eta_map'=H'*L+H*L'<0.
Because R decreases, its positivity locus f*R-h>0 is an interval.
Any admissible root solves eta_map=eta>0; existence from Section 1
and strict monotonicity give uniqueness. Finally

    P_eta=e*b*(B*D+e*T0)*(eta_map-eta)

on (0,r); the multiplier is positive and eta_map'<0 at the root, so
P_eta'<0 there. No IFT hypothesis is left to test in this subchamber.

## 3. Exact triple root inside the physical interval

Let L=(sqrt(403)-2)/21, so 0<L<1 and 21*L^2+4*L-19=0. Choose

    beta=1/2, e=1/5, k=15/2, h=1, s=-2,
    d=L+2, w=3*L+11/5,
    f=(59*L+80)/(21*L+80), eta=361*L/(21*L+80).

All required signs hold, and

    Delta=(59*L+61)/(2*(21*L+80))>0,
    P_eta(b)=d*Delta*(1-4*b)^3.

For a direct identity check, before using 21*L^2+4*L-19=0 the
remainder after subtracting d*Delta*(1-4*b)^3 is
-4*b*(L+2)*(4*b-1)^2*(21*L^2+4*L-19)/(21*L+80), where here
Delta is evaluated as f*e*k-h*beta*d.
At b=1/4, D=1, E=19/20, T0=5, x=1/20, C=5/6<k.
Thus this is a genuine admissible triple root with positive eta and Delta.
The triple root can satisfy every remaining guard of the negative-owner-value
producer. Add the following raw data (the packet's notation):

    g=1, A=2, c=20, d1=1, u=v=0, zeta0=0,
    n=31/30, ell=0, Z1(02)=0, Z3(03)=-1, Z3(023)=0.

The definitions give j=1/30, X1=3/200, A°1=7/80 and

    A*T/c=eta/190<1/30<g*C/k=1/9,
    B_s=0, H0=k>0, X2=(f+eta)/20>0,
    x*(1-b)*Z3(03)+(1-x)*b*v+x*b*Z3(023)=-3/80<0.

For the first inequality, 0<L<1 gives eta<361/80<19/3. The other raw
signs hold by inspection; unspecified rewards may be any fixed finite values
consistent with the packet. Thus Section 5 genuinely adds input to that
producer: its former simple-root hypothesis fails at the only root. This
makes no claim that all other existing equilibrium producers fail here.

## 4. Exact failure of uniqueness

Choose beta=1/10,e=1/2,f=1/1000,k=60,h=1/25,d=5,s=-2,w=5,
eta=1/10000000. Then Delta=1/100, the admissible interval is (0,1/2), and

    P_eta(b)=-151999981*b^3/20000000
             +77305011*b^2/10000000-82610061*b/40000000+1/20.

Its values at 0,1/10,99/200,1/2 are respectively

    1/20, -1736402811/20000000000,
    13214780081/160000000000000, -59/160000000.

There is one root in each of the three intervening open intervals, and a
cubic has no others. Thus all three roots are admissible, distinct and simple.

## 5. Removing simplicity from the negative-owner-value producer

In the first theorem of the frozen joint-quitting packet, “simple root” may
be replaced by “sign-changing root,” with every other strict hypothesis
unchanged. For a nonzero cubic this permits simple or triple roots. The
conclusion remains an exact finite-period terminal Nash equilibrium whenever
K>=M(1+|p|), hence the packet's original uniform payoff. This is ordinary
mathematics, not checked in Lean; neither uniqueness nor analytic dependence
of the resulting equilibrium is asserted.

Write C(b)=b(beta-s)/(1-b), T0=(1-b)(k-C), and epsilon=(alpha,pi).
For a fixed finite core, normalize its two return equations as

    G1=A°1-(g E0+k E1)/(k-E0),
    G2=A°2-(h E0+k E2)/(k-E0).                         (O1)

Their denominator is positive near the limiting core. Leave b free and solve

    X3=0,  T-x*eta/(1-x)=0,  G1=0                    (O2)

for (x,T,j). At epsilon=0, affine core transport gives

    G1=[A°1(k-C)-g C+k j]/(k-C),
    G2=A°2-(k T+h C)/(k-C).

The Jacobian of (O2), in that variable order, is lower triangular with
diagonal -D, 1, [k-L(k-C)]/(k-C), all nonzero. Here A°1=A10-Lj and the
limiting core row3 coordinate is identically zero. Thus the core IFT and then
this three-equation IFT give analytic x,T,j as functions of (b,epsilon), also
allowing A as a local raw parameter. At zero these are exactly the packet's
rational x,T,j, independent of A. The remaining scalar residual satisfies
the exact algebraic identity

    G2(b,0)=b*k*P_eta(b)/[D*(k+s*b)*(D-e*b)*T0].       (O3)

Its prefactor is positive throughout the physical interval. At a
nonresonant b*, choose a short closed interval around it on which every
strict core and prefix guard persists and P_eta has opposite nonzero endpoint
signs. Continuity preserves those signs for all small epsilon. IVT then
solves G2=0 and hence all four outer equations, without differentiating the
cubic.

At resonance, the length N core has last Z=0 and the length N-1 core has wash
margin m=A E2+c E1=0. Necessarily N>=2. Both unconstrained analytic core
branches and both reduced systems (O2) exist near this point. For fixed b,
their limiting derivatives are

    partial_A Z_last,N=-theta_(N-1)/[1-(a0+1)theta_(N-1)]<0,
    partial_A m_(N-1)=E2_(N-1)>0.                    (O4)

The second equality uses the limiting exit formulas and the A-independence
of x,T,j. These derivatives retain their signs nearby.

On the hypersurface Z_last,N=0 the terminal divided owner3 equation gives
(u+d1)Y_last,N=0. The last root is therefore pure3 with hazard q. Its current
row1,2 values are -A*q,c*q. Deleting it produces a shorter exit

    E^- = q*(k,-g,-h,0)+(1-q)*E,
    E^-1=-A*q, E^-2=c*q.

Thus its wash margin vanishes. Its entrance and X3 do not change. Moreover,

    k-E^-0=(1-q)(k-E0),
    c_i E^-0+k E^-i=(1-q)(c_i E0+k Ei),

where c_1=g,c_2=h. Hence both normalized Gi in (O1) are exactly invariant
under deletion. Reduced IFT uniqueness identifies the deleted core with the
shorter branch, with the same b,x,T,j. Consequently the two zero
hypersurfaces in (O4) coincide. They form one graph
A=a_*(b,epsilon): the longer branch has Z_last>=0 on the side A<=a_*;
the shorter branch has m>=0 on A>=a_*.

The other potentially zero hazard is controlled by the exact terminal
owner3 equation:

    Y_last=(e-v)*Z_last/
      [u+d1+alpha*(Z3(123)-u-v-Z3(12)-d1+e)*Z_last]. (O5)

Its denominator stays positive, so Y_last and Z_last have the same sign.
All earlier hazards and all remaining guards are strict. The prescribed
selection therefore supplies a legal core everywhere near the resonance.
On its interface the two values of G2 coincide by deletion invariance, so
the selected G2 is continuous jointly in (b,A,epsilon), although the core
length changes. At epsilon=0 it still equals (O3). Fixing the original A,
choose close opposite-sign b endpoints and apply IVT to this continuous
residual. This proves the sign-changing-root extension at resonance too.

The packet's strict prefix inequalities persist at the obtained root. Its
wash permits the nonnegative boundary margin, so the literal wash and return
close the period. The unchanged joint02 date gives opponents-only absorption
against every behavioral deviation, making the terminal comparisons exact
Nash inequalities and giving the original uniform payoff. Finally
alpha+|pi|=(1+|p|)/K, so a sufficiently large M makes all these local arguments
apply uniformly for every real p under K>=M(1+|p|). Shrink the one- or
two-branch neighborhood so (1-x)b has a positive lower bound. The other terms
in the joint-root quiet1 offer are uniformly bounded there, so increasing M
also makes its negative term -K(1-x)b dominate uniformly.

This proof does not cover an even-multiplicity root or an identically zero
polynomial. The unchanged construction and all raw guards are those of the
frozen packet; its explicit K=1000 certificate and arbitrary Fin4 are outside
the scope of this extension.

## 6. Scope and inspected sources

The frozen [negative-owner-value packet](../exports/JOINT_QUITTING_NEGATIVE_VALUE_UNIFORM_EQUILIBRIUM.md)
assumes a simple admissible root. The frozen
[core-free packet](../exports/CORE_FREE_JOINT_RETURN_UNIFORM_EQUILIBRIUM.md)
requires a nonzero polynomial and an admissible root, and already proves root
existence and strict eta monotonicity for one specific numerical reward family.
The general physical-boundary sign argument, sufficient monotonicity condition,
exact multiple-root examples and Section 5's resonance gluing are the claims
of this note; the frozen constructions are used only under their stated
remaining guards.

Inspected generic declarations:
`exists_cubicAnchor_root_mem_Ioo_of_neg_of_pos` and
`exists_cubicAnchor_root_mem_Ioo_of_pos_of_neg`
(`MathUE/CubicAnchorRoot.lean`). Inspected semantic endpoint:
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
(`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`).
Section 5 uses the frozen packet's direct exact-period argument. No new Lean
claim is made. All displayed polynomial identities and rational sign values
were independently checked by exact symbolic arithmetic; the proofs above
are finite identities and ordinary IVT/IFT arguments.

Next question: characterize uniqueness on the remaining omega>0 chamber;
the exact examples show that neither uniqueness nor simplicity is automatic.
