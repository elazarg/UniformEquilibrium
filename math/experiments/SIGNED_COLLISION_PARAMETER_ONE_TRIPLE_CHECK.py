"""Exact one-triple branch certificate for the signed collision parameter theorem."""
import sympy as s
k,y,q,E=s.symbols('k y q E')
z=2*y/(101-106*y);w=k*y/(3+(k-1)*y)
x=(101*z+97*w-200*z*w)/((1-z)*(1-w))
E2=((2-k)*y+4*w-(3-k)*y*w)/((1-y)*(1-w))
C0_variable=3*y-z+3*w-14*y*z-4*y*w-8*z*w+13*y*z*w+(1-y)*(1-z)*(1-w)*E
C1=-100*z-100*w+211*z*w;C3=-z*(100-101*y)
ell=s.diff(C0_variable,E);base=C0_variable.subs(E,0)
K0=-s.Rational(9,2)+6*x+s.Rational(27,2)*E2
alpha=s.cancel(K0*ell+s.Rational(7,4)*C3-s.Rational(3,4)-C1)
beta=s.cancel(K0*base+(-s.Rational(15,2)+3*x+s.Rational(27,4)*E2)*C3+3*x+s.Rational(27,4)*E2+3*C1)
Esol=s.cancel(-beta/alpha)
F1=(9+6*x-9*E)*C0_variable+(6+3*x-5*E)*C3+3*x-3*E+(3-E)*C1
F2=(6-6*E2-4*E)*C0_variable+(6-3*E2-3*E)*C3-3*E2-E
# Verify the return elimination before inserting rational macro expressions.
cc,dd,ee,xx,zz,rr=s.symbols('cc dd ee xx zz rr')
ff=(9+6*xx-9*rr)*cc+(6+3*xx-5*rr)*ee+3*xx-3*rr+(3-rr)*dd
gg=(6-6*zz-4*rr)*cc+(6-3*zz-3*rr)*ee-3*zz-rr
linear=(-s.Rational(9,2)+6*xx+s.Rational(27,2)*zz)*cc
linear+=(-s.Rational(15,2)+3*xx+s.Rational(27,4)*zz)*ee+3*xx+s.Rational(27,4)*zz+3*dd
linear+=rr*(s.Rational(7,4)*ee-s.Rational(3,4)-dd)
assert s.expand(ff-s.Rational(9,4)*gg-linear)==0
numerator=s.fraction(s.cancel(F2.subs(E,Esol)))[0]
factors=s.factor_list(numerator)[1]
assert [(s.Poly(f,k,y).degree_list(),power) for f,power in factors]==[((0,1),1),((1,3),1),((3,8),1)]
P=factors[-1][0]
C0=C0_variable.subs(E,Esol)
H=k*(31440*y*y-50031*y+19291)-20994*y*y+82576*y-58782
assert s.cancel(E2-s.Rational(3,100)*x-y*H/(100*(y-3)*(y-1)*(108*y-101)))==0
sub={y:q/(k+s.Rational(3,10))}
def rat(expr):return s.fraction(s.cancel(expr.subs(sub)))
Pq=rat(P)[0]
print('root degrees',s.Poly(Pq,k,q).degree_list(),flush=True)

def bern(poly,lo=0,hi=s.Rational(31,10),qlo=s.Rational(11,500),qhi=s.Rational(3,125)):
 u,v=s.symbols('u v');pp=s.Poly(poly.subs({k:lo+(hi-lo)*u,q:qlo+(qhi-qlo)*v}),u,v);a,b=pp.degree_list()
 cc=[[pp.coeff_monomial(u**i*v**j) for j in range(b+1)] for i in range(a+1)]
 return [[sum(cc[ii][jj]*s.binomial(i,ii)*s.binomial(j,jj)/(s.binomial(a,ii)*s.binomial(b,jj)) for ii in range(i+1) for jj in range(j+1)) for j in range(b+1)] for i in range(a+1)]
def split_curve(cc):
 tri=[cc]
 while len(tri[-1])>1:tri.append([(a+b)/2 for a,b in zip(tri[-1],tri[-1][1:])])
 return [r[0] for r in tri],[r[-1] for r in tri[::-1]]
def split(cc,dim):
 if dim==0:
  aa,bb=split([list(r) for r in zip(*cc)],1);return [list(r) for r in zip(*aa)],[list(r) for r in zip(*bb)]
 pairs=[split_curve(r) for r in cc];return [p[0] for p in pairs],[p[1] for p in pairs]
def sign(cc):
 vv=[v for r in cc for v in r]
 return 1 if min(vv)>0 else -1 if max(vv)<0 else 0

def certpoly(label,poly,expected,**kwargs):
 stack=[(bern(poly,**kwargs),0)];leaves=deep=0
 while stack:
  cc,depth=stack.pop()
  if sign(cc)==expected:leaves+=1;deep=max(deep,depth);continue
  assert sign(cc)==0 and depth<24,(label,depth,sign(cc))
  aa,bb=split(cc,depth%2);stack.extend([(aa,depth+1),(bb,depth+1)])
 print(label,leaves,deep,flush=True)

certpoly('lower boundary',Pq.subs(q,s.Rational(11,500)),1)
certpoly('upper boundary',Pq.subs(q,s.Rational(3,125)),-1)
certpoly('P_q negative',s.diff(Pq,q),-1)

guards={
 '-alpha':-alpha,'E0-x':Esol-x,'C0':C0,'C0+C1':C0+C1,'C0+C3':C0+C3,
 'E2':E2,'x':x,'3-x':3-x,
}
allcoeff=[bern(Pq)];labels=[]
for label,expr in guards.items():
 num,den=rat(expr);allcoeff.extend([bern(num),bern(den)]);labels.append(label);print('prepared',label,flush=True)
stack=[(allcoeff,0)];leaves=discarded=deep=0
while stack:
 arrays,depth=stack.pop()
 if sign(arrays[0]):discarded+=1;continue
 flags=[sign(arrays[1+2*i])*sign(arrays[2+2*i])==1 for i in range(len(labels))]
 if all(flags):leaves+=1;deep=max(deep,depth);continue
 assert depth<30,('root guard failure',depth,[labels[i] for i,v in enumerate(flags) if not v])
 splits=[split(cc,depth%2) for cc in arrays]
 stack.extend([([pair[j] for pair in splits],depth+1) for j in [0,1]])
print('all root guards',leaves,'discarded',discarded,'maxdepth',deep,flush=True)

certpoly('wash H<0 for k<=3',rat(H)[0],-1,hi=s.Integer(3))
certpoly('wash H>0 at k=31/10',rat(H)[0].subs(k,s.Rational(31,10)),1)
certpoly('P_y<0 near crossing',rat(s.diff(P,y))[0],-1,lo=s.Integer(3))
certpoly('P_k<0 near crossing',rat(s.diff(P,k))[0],-1,lo=s.Integer(3))
certpoly('H_y<0 near crossing',rat(s.diff(H,y))[0],-1,lo=s.Integer(3))
certpoly('H_k>0 near crossing',rat(s.diff(H,k))[0],1,lo=s.Integer(3))
print('PASS: unique regular one-triple root, all return guards, unique wash crossing in (3,31/10).',flush=True)

for K, expected in [(s.Rational(61441,20000),-1),(s.Rational(153603,50000),1)]:
 pp=s.Poly(Pq.subs(k,K),q)
 lower,upper=s.Rational(11,500),s.Rational(3,125)
 for _ in range(35):
  middle=(lower+upper)/2
  if pp.eval(middle)>0: lower=middle
  else: upper=middle
 assert pp.eval(lower)>0 and pp.eval(upper)<0
 hh=H.subs(k,K)
 signs=[s.sign(hh.subs(y,Q/(K+s.Rational(3,10)))) for Q in [lower,upper]]
 assert signs==[expected,expected]
 print('Critical bracket endpoint',K,'q interval',lower,upper,'H signs',signs,flush=True)
print('Critical k is strictly between 3.07205 and 3.07206.',flush=True)
