# Global exclusion of the M14 positive-cap one-date class

Ordinary mathematics. This lemma supplies an actual global competitor, not a
fixed-observer-cap descendant replacement. It concerns the native M14 table
in `math/notes/CODEX_COORDINATOR__NO_CHILD_FIN4_BENCHMARK.md`.

Let Gamma be its singleton matrix and J its participant-pair matrix:

    Gamma=[0,-1,-1,2;-1,0,1,1;1,2,0,-1;1,-1,1,0],
    J=[0,-5,13,-5;13,0,-5,-5;-5,-5,0,13;-5,13,-5,0].

All larger participant rewards are -5 and every passive nonsingleton reward
is zero. The pivot is2 and observers are O={0,1,3}.

## 1. An actual observer-exact rational tail

There is epsilon>0 and an actual tail T_s, 0<=s<=epsilon, with all prescribed
hazards positive when s>0, positive marginal Never masses, zero observer
debts, and pivot Never a full best response. Its cap vector v(s), pivot debt
e(s), and joint Never mass satisfy

    v(s)=k s+O(s^2),       k=(21,52,92,49)/205,
    e(s)=O(s^2),          nu(T_s)=1-s+O(s^2).          (1)

The actual tail at s=0 is literal Never. Every cap is strictly positive for
s>0 sufficiently small. All four players are ALL-END.

Here is a direct construction. Put

    lambda=2/3, zeta=1/3, h=(52,49,46,58)/615.

Exact matrix multiplication gives

    (Gamma-zeta J)h=(3/205)e2,
    Gamma h/zeta=k,        sum_i h_i/zeta=1,
    (Jh)_O=k_O,            (Jh)_2=83/205.             (2)

For a hazard q write H_i=product_(j!=i)(1-q_j), and let Q_i,P_i be the
native Quit and passive Continue offers. Solve the observer contact equations

    Q_i(q)=P_i(q)+H_i(q)Q_i(q_next), i in O,
    (q_next)_2=lambda q2.                            (3)

The derivative of Q_O with respect to q_O at zero is J_OO, whose determinant
is -970. The implicit function theorem gives

    (q_next)_O=A q_O+b q2+R(q2,q_O),
    A=I-J_OO^-1 Gamma_OO,
    b=J_OO^-1(zeta J_O2-Gamma_O2), R=O(|q|^2).

The characteristic polynomial of I-A, up to a positive factor, is
970u^3+493u^2+52u+1. Its coefficients are positive and493*52>970, so its
roots have negative real parts. Hence the eigenvalues of A have real parts
greater than one and some vector norm satisfies ||A^-1||=kappa<1.
By(2), lambda h_O=A h_O+b h2.

On twice continuously differentiable u with u(0)=u'(0)=0, solve

    u(s)=A^-1[u(lambda s)-R(h2 s,h_O s+u(s))].         (4)

Use the maximum of the weighted norms |u(s)|/s^2, |u'(s)|/s and |u''(s)|.
The linear composition has norm at most kappa lambda^2<1; on a fixed bounded
ball the nonlinear difference is O(epsilon). A sufficiently large fixed
ball and then sufficiently small epsilon give a strict invariant contraction.
Thus q(s)=(h_O s+u(s),h2 s), with coordinates placed in their original order,
is an exact C2 curve, q(s)=h s+O(s^2). All its components lie in(0,1) for
small positive s. Prescribe q(lambda^n s) at date n.

The hazard sum is finite, so all marginal Never probabilities are positive.
Equation(3), iterated with Q_i(q(lambda^n s)) tending to zero, proves that
every observer's finite deadline and Never payoff equals Q_i(q(s)). Every
behavioral replacement is a mixture of these deadlines and Never. Hence
observer caps and prescribed payoffs coincide exactly, not approximately.

For the pivot, singleton passive outcomes give its Never payoff
W2(s)=(Gamma h)_2 s/zeta+O(s^2); the sum of double-event probabilities is
O(s^2). Therefore

    W2(s)-Q2(q(s))=9s/205+O(s^2)>0.                  (5)

The same uniform expansion applies at every conditional date lambda^n s.
Comparing a finite deadline with Never multiplies(5) by prior opponent
survival, so Never strictly dominates every finite deadline. Thus W2 is the
full cap. The pivot's debt satisfies the exact recurrence

    e(s)=q2(s)[W2(s)-Q2(q(s))]+c(s)e(lambda s),
    c(s)=product_i(1-q_i(s)).

The nonnegative forcing is O(s^2); summing the geometric bound proves
e(s)=O(s^2). Finally, the product of all survival factors is
1-s sum_i h_i/zeta+O(s^2)=1-s+O(s^2). This proves(1) with an actual tail.
No absorbing-gap or global-minimum hypothesis enters this construction.

## 2. Exact root attachment preserving the pivot gap

For positive root odds x put

    C_i(x)=(J-Gamma)_i x
       -5[sum_(j<k;j,k!=i)x_j x_k+prod_(j!=i)x_j],
    nu0(x)=product_i(1+x_i)^-1.

Consider a one-date profile followed by Never, with all four hazards positive,
zero observer debt and pivot Never optimal. Its root odds x satisfy

    C_O(x)=0,       C2(x)=-g,       g>=0.

Suppose DC(x) is invertible. For the ACTUAL tails from Section1, the implicit
function theorem produces positive x(s) close to x, with

    C(x(s))=v(s)-g e2,
    x(s)=x+DC(x)^-1 k s+O(s^2).                     (6)

Prepend this root to T_s. The observers' root contacts hold exactly and
hence their entire prescribed laws remain optimal. The pivot's Continue
cap exceeds its Quit offer by H2 g, so Continue remains a full maximizer,
including the tie g=0. Thus this is an actual feasible profile on the same
zero-observer-debt carrier. Its full cap is ALL-END. Nothing is replaced
inside a pre-existing inherited head.

Writing z(s)=x2(s), the exact pivot debt and objective are

    d2(s)=nu0(x(s))[z(s)g+e(s)],
    J_r(s)=nu0(x(s))[z(s)g+e(s)+r nu(T_s)].           (7)

In particular for every r>0, with n_i=1/(1+x_i),

    J_r'(0)/nu0(x)
      =g(e2^T-z n^T)DC(x)^-1 k
         -r[1+n^T DC(x)^-1 k].                      (8)

The tail debt contributes no first-order term. Consequently the two strict
finite inequalities

    (e2^T-z n^T)DC(x)^-1 k<0,
    1+n^T DC(x)^-1 k>0                              (9)

rule out this one-date profile as a global J_r minimum for EVERY r>0.
At g=0 only the second strict inequality is needed. The r=m/2 source choice
is included, without any numerical assumption about m.

## 3. Complete class coverage and exact sign certificate

Every nonempty one-date M14 profile with positive caps, zero observer debts,
ALL-END, and positive Never masses has all four hazards positive. Indeed
an active observer must have its premium predecessor active; the resulting
cycle-prefix candidates are02,012,0123 and the pivot singleton2.
Support2 has negative observer0 Never payoff. Support02 cannot satisfy
observer0 contact, which demands14x2=0. On012, observer0 Never numerator is -x1-x2<0. Thus0123 remains.
Equivalently one may apply the complete last-root classification in the
canonical benchmark, which leaves only012 and0123 before cap positivity.

That classification proves that every such full-support root lies on the
single curve C_O=0 with

    alpha<=z=x2<rho0,        3/25<alpha<rho0<4/25.

Here alpha is the pivot-contact endpoint and rho0 is the first zero of the
observer0 cap. The exact resultant proof and rational endpoint signs are
in the canonical benchmark's complete M14 sign partition; this internal
proof uses that existing theorem and its exact checker, not numerical
branch selection. The following additional bounds are proved here:

    x0 in[3/25,9/50],  x1 in[11/100,19/100],
    x2 in[3/25,4/25],  x3 in[13/100,17/100].          (10)

Set z=x2,y=x3,l=5(1+z),h=14-5z,c=6+5z,k=6z,
d=h^2-lk,e=20l,a=c^2-lk,b=20k. The observer contacts give

    x0=(k+cy)/(h-ly), x1=(ay+b)/(d-ey),
    F_z(y)=(4+5z)x1+(7+5z)y+l x1 y-14z=0.

On its legal interval0<y<d/e, F_z is strictly increasing. Clear d-ey and
substitute z=3/25+t/25,0<=t<=1. At y=13/100 its cubic Bernstein coefficients
are

    -2846868/390625, -149862809/6250000,
    -365472493/9375000, -20430076/390625;

at y=17/100 they are

    22085767/390625, 768161213/18750000,
    254116267/9375000, 5841744/390625.

The denominators are positive throughout this rectangle. These opposite
strict signs and monotonicity place y between the two rational endpoints.
The map phi(y)=(k+cy)/(h-ly) increases in both z and y where its denominator
is positive, as does phi composed with itself. Its corner bounds are

    263/2112<=x0<=1058/6107,
    81411/670700<=x1<=81607/465475.

They imply(10).

Write D=DC(x), P=product_i(1+x_i), b=(21,52,92,49), u=adj(D)b and
S=sum_i[P/(1+x_i)]u_i. Define the polynomials

    A=205P detD+S,        B=-[P u2-zS].

The inverse expressions in(9) satisfy exactly

    1+n^T D^-1k=A/(205P detD),
    (e2^T-z n^T)D^-1k=-B/(205P detD).

On the full rational box(10), all tensor Bernstein coefficients of each of
these three polynomials are strictly positive. Their coordinate degrees,
coefficient counts, and exact minimum coefficients are

| Polynomial | Degrees | Count | Smallest coefficient |
| --- | --- | --- | --- |
| detD | (2,2,2,2) |81|695509964106293/62500000000|
| A | (3,3,3,3) |256|8503628877474398758391/4882812500000000|
| B | (3,3,4,3) |320|46778584435393895821/195312500000000|

This is a finite rational certificate. To reproduce it, substitute
x_i=lo_i+(hi_i-lo_i)t_i and write the resulting power coefficients as c_m.
For coordinate degree d_i, the Bernstein coefficient indexed by j is

    sum_(m<=j) c_m product_i binom(j_i,m_i)/binom(d_i,m_i).

All data are the displayed matrix D (the derivative of C), the three
polynomials, and box(10). The compact exact checker implements this formula
and fails if any sign is nonpositive. Hence D is invertible and both
inequalities(9) hold throughout the complete admissible positive-cap branch.
Equation(8) is strictly negative for every r>0 and every g>=0.

## 4. Global-minimum consequence and precise limit

Therefore NO positive-cap one-date ALL-END exact-observer profile at M14
is a global minimum of d2+r nu, for any r>0. The theorem includes the pivot
tie endpoint g=0 and the previously retained positive finite control z=1/8.
That control is now proved not globally minimizing.

For the selected source with0<mu<r<m, every actual minimum has positive
caps by the already established solo-observer prefix descent. Literal
Never has value r>mu. If a proposed minimum has exactly one occupied date,
initial empty dates may be removed: all existing caps are positive, so
extra pure Quit0 options of value zero cannot raise a cap. The theorem
then rules out that minimum. Every surviving finite actual minimum must
therefore have at least TWO occupied dates; its six first/last support
pairs remain subject to the existing endpoint restrictions.

This changes the ENTIRE actual profile by adding an actual infinite tail.
It does not keep the old observer cap values fixed. It cannot be applied
to the final root of a longer profile without pricing the preceding head.
Longer finite profiles, inherited mixed-cap endpoints and arbitrary Fin4
remain open. This is ordinary mathematical evidence, not a Lean proof.
