"""Exact rational certificate for the positive-cap one-date M14 control."""
from fractions import Fraction as Q

def add(a,b):
 c=[Q(0)]*max(len(a),len(b))
 for i,x in enumerate(a):c[i]+=x
 for i,x in enumerate(b):c[i]+=x
 while len(c)>1 and not c[-1]:c.pop()
 return c

def mul(a,b):
 c=[Q(0)]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]+=x*y
 while len(c)>1 and not c[-1]:c.pop()
 return c

def scale(a,r):return [x*r for x in a]
def summ(*xs):
 a=[Q(0)]
 for x in xs:a=add(a,x)
 return a

M=Q(14);z=Q(1,8);L=5*(1+z)
y=[Q(0),Q(1)];p0=list(map(Q,[6,53]));d0=list(map(Q,[107,-45]))
p1=list(map(Q,[960,2539]));d1=list(map(Q,[11179,-7200]))
f=list(map(Q,[120986,-919862,324945]))
g0=summ(scale(p1,4+5*z),scale(mul(y,d1),7+5*z),scale(mul(y,p1),L),scale(d1,-M*z))
g1=summ(scale(p0,-M+5*z),scale(mul(y,d0),6+5*z),scale(mul(p0,y),L),scale(d0,6*z))
g3=summ(scale(mul(p0,d1),6+5*z),scale(mul(p1,d0),-M+5*z),scale(mul(p0,p1),L),scale(mul(d0,d1),6*z))
assert g0==scale(f,Q(-1,8)) and g1==[0] and g3==[0]
yl=Q(13828,100000);yu=Q(13829,100000)
poly=lambda t:sum(a*t**i for i,a in enumerate(f))
x=lambda t:(53*t+6)/(107-45*t)
v=lambda t:(2539*t+960)/(11179-7200*t)
assert poly(yl)>0>poly(yu)
assert 2*f[2]*yu+f[1]<0
assert 107-45*yu>0 and 11179-7200*yu>0
xl=Q(13225,100000);xu=Q(13228,100000)
vl=Q(12874,100000);vu=Q(12877,100000)
assert xl<x(yl)<x(yu)<xu and vl<v(yl)<v(yu)<vu
lower=[-vu-z+2*yl,-xu+z+yl,xl+2*vl-yu,xl-vu+z]
assert lower==[Q(2279,100000),Q(131,1000),Q(3143,12500),Q(803,6250)]
assert all(t>0 for t in lower)
glo=6*xl+7*vl-14*yu+5*(xl*vl+xl*yl+vl*yl+xl*vl*yl)
ghi=6*xu+7*vu-14*yl+5*(xu*vu+xu*yu+vu*yu+xu*vu*yu)
assert glo>Q(3596,100000) and ghi<Q(366,10000)
nuhi=1/((1+xl)*(1+vl)*(1+z)*(1+yl));r=Q(1,20)
assert nuhi*(r+z*ghi)<r
assert (1+z)*lower[2]-z*ghi-r>0
assert r*Q(13,11)<z
print('PASS: exact algebraic observer contacts, strict pivot ALL-END, all four positive caps, and scalar source-inequality control.')
