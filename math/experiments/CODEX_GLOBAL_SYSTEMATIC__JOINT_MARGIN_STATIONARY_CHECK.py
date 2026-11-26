"""Exact stationary-gain exclusion at t=16, R=1/100.
Run with Python 3; standard library only. Every mathematical operation uses
Fraction. The domain is v in[0,1], a,b in[4/9,1], c=4/(9ab)<=1.
"""
from fractions import Fraction as Q
class I:
 __slots__=('l','u')
 def __init__(self,l,u=None):self.l=Q(l);self.u=Q(l if u is None else u)
 def __add__(a,b):
  if not isinstance(b,I):b=I(b)
  return I(a.l+b.l,a.u+b.u)
 __radd__=__add__
 def __neg__(a):return I(-a.u,-a.l)
 def __sub__(a,b):return a+-b if isinstance(b,I) else a+I(-b)
 def __rsub__(a,b):return -a+b
 def __mul__(a,b):
  if not isinstance(b,I):b=I(b)
  z=[a.l*b.l,a.l*b.u,a.u*b.l,a.u*b.u];return I(min(z),max(z))
 __rmul__=__mul__
 def __truediv__(a,b):
  if not isinstance(b,I):b=I(b)
  assert b.l>0 or b.u<0
  return a*I(1/b.u,1/b.l)
 def __rtruediv__(a,b):return I(b)/a
 def sq(a):
  if a.l>=0:return I(a.l*a.l,a.u*a.u)
  if a.u<=0:return I(a.u*a.u,a.l*a.l)
  return I(0,max(a.l*a.l,a.u*a.u))
 def haszero(a):return a.l<=0<=a.u
 def width(a):return a.u-a.l
P=Q(4,9);R=Q(1,100)
def ff(a,b,v):
 ab=a*b;h=(1-a)*(1-b);C=1-2*ab
 B=a-2*b+4*ab-1-h*C+h*R
 D=h*(-15*a+30*b+4*ab-1+R)
 return C+v*B-v.sq()*D
stack=[(I(0,1),I(P,1),I(P,1))];n=0
while stack:
 v,a,b=stack.pop();n+=1
 if (a*b).u<P:continue
 c=P/(a*b)
 if c.l>1:continue
 c.u=min(c.u,Q(1))
 vals=[ff(a,b,v),ff(b,c,v),ff(c,a,v)]
 if any(not z.haszero() for z in vals):continue
 # Bisect a widest coordinate; the two closed boxes cover the parent.
 boxes=[v,a,b];j=max(range(3),key=lambda i:boxes[i].width());old=boxes[j];mid=(old.l+old.u)/2
 if old.width()<Q(1,2**24):
  raise RuntimeError(('Unresolved box',[(z.l,z.u) for z in boxes]))
 left=boxes.copy();right=boxes.copy();left[j]=I(old.l,mid);right[j]=I(mid,old.u)
 stack.append(tuple(right));stack.append(tuple(left))
assert n==9589, ('Unexpected subdivision count',n)
print('EXACT RATIONAL PASS: no simultaneous zero; boxes',n)
