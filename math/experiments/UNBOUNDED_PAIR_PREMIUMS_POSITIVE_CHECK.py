"""Exact return and quiet-comparison certificate for K>=100, p>=2K.

Uses rational interval arithmetic on the compact parameter box
u=100/K in[0,1], t=p/(p+K/50) in[100/101,1]. Every acceptance test
uses exact Fraction endpoints; no numerical samples or root approximations
enter the certificate. The artificial endpoints only compactify the proof.
"""

from fractions import Fraction as F

class I:
 def __init__(self,a,b=None):
  self.a=F(a);self.b=F(a if b is None else b)
  assert self.a<=self.b
 def __add__(x,y):
  y=lift(y);return I(x.a+y.a,x.b+y.b)
 __radd__=__add__
 def __neg__(x):return I(-x.b,-x.a)
 def __sub__(x,y):return x+-lift(y)
 def __rsub__(x,y):return lift(y)+-x
 def __mul__(x,y):
  y=lift(y);v=[x.a*y.a,x.a*y.b,x.b*y.a,x.b*y.b];return I(min(v),max(v))
 __rmul__=__mul__
 def __truediv__(x,y):
  y=lift(y)
  if y.a<=0<=y.b:raise ZeroDivisionError
  return x*I(1/y.b,1/y.a)
 def __rtruediv__(x,y):return lift(y)/x
 def __repr__(x):return f'[{x.a},{x.b}]'
def lift(x):return x if isinstance(x,I) else I(x)

def calc(u,t,w):
 y=u*(1-t)/25
 zb=2*(1-t)/(2525-106*u*(1-t));z=u*zb;Kz=100*zb
 L=Kz+100*w-(Kz+111*z)*w
 X=2*t/25+3*w-(2*t/25+y)*w
 T3=-z*(100-101*y)
 x=(Kz+z+97*w-(Kz+100*z)*w)/((1-z)*(1-w))
 E2=(2*t/25+2*y+4*w-(2*t/25+3*y)*w)/((1-y)*(1-w))
 ellT=(1-y)*(1-z)*(1-w)
 baseT=3*y-z+3*w-14*y*z-4*y*w-8*z*w+13*y*z*w
 S=2/((2+X)*(1+L))
 den=100-99*t+u*(1-t)
 Kchi=50*(1-t)*S*L*X/den;pchi=t*S*L*X/den;chi=u*Kchi/100
 pi1=(pchi+S*X)/2;pi2=Kchi+S*L
 C3=-2*pi1+pi2-6*chi+S*T3
 ell=S*ellT;base=3*pi1-pi2-12*chi+S*baseT
 K0=-F(9,2)+6*x+F(27,2)*E2
 alpha=K0*ell+F(7,4)*C3-F(3,4)
 beta=K0*base+(-F(15,2)+3*x+F(27,4)*E2)*C3+3*x+F(27,4)*E2
 E=-beta/alpha;C0=ell*E+base;T0=ellT*E+baseT
 F2=(6-6*E2-4*E)*C0+(6-3*E2-3*E)*C3-3*E2-E
 mid=C3+((C3/2+1)*X+(C3-1+u)*L)/2
 endscaled=100*w-(100+111*u)*zb*w+101*u*(1-t)*zb/25-101*u*(1-t)*X*L/(200*t)
 guards={'minus_alpha':-alpha,'E_minus_x':E-x,'C0':C0,'C3':C3,'T0':T0,'L':L,'X':X,'x':x,'three_minus_x':3-x,'wash':E2-3*x/100,'one_minus_C3':1-C3,'twoL_minus_X':2*L-X,'quiet0':C0*(2+X)/2-3*X/2,'quiet3_mid':mid,'quiet3_end_scaled':endscaled}
 return F2,guards

UL=(F(0),F(1));TL=(F(100,101),F(1));WL=(F(1,250),F(11,2500))
def certify(mode):
 # Fixed deterministic subdivision; adaptive only refines unaccepted boxes.
 bounds=(UL,TL,WL if mode=='guards' else ((WL[0],WL[0]) if mode=='left' else (WL[1],WL[1])))
 stack=[(bounds,0)];accepted=0;depthmax=0;mins={};fail=None
 while stack:
  box,depth=stack.pop()
  try:
   f,g=calc(*(I(*b) for b in box))
   checks=g if mode=='guards' else {'endpoint':f if mode=='left' else -f}
   good=all(v.a>0 for v in checks.values())
  except ZeroDivisionError:good=False
  if good:
   accepted+=1;depthmax=max(depthmax,depth)
   for k,v in checks.items():mins[k]=min(mins.get(k,v.a),v.a)
   continue
  if depth>=30:
   fail=(box,checks if 'checks' in locals() else 'division');break
  # Cycle dimensions: endpoint checks only u,t; guard checks u,t,w.
  j=depth%(3 if mode=='guards' else 2);a,b=box[j];m=(a+b)/2
  for part in ((a,m),(m,b)):
   bb=list(box);bb[j]=part;stack.append((tuple(bb),depth+1))
 print(mode,'accepted',accepted,'depth',depthmax,'FAIL',fail)
 # Lower endpoints remain exact rationals; only the proof counters are printed.
 return fail is None

if __name__=='__main__':
 assert certify('left')
 assert certify('right')
 assert certify('guards')
 print('All positive-cone return and quiet-comparison checks passed exactly.')
