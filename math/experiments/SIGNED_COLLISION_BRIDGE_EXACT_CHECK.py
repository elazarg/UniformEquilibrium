from fractions import Fraction as Q
class I:
 def __init__(self,a,b=None):self.a=Q(a);self.b=self.a if b is None else Q(b)
 def __add__(self,x):
  x=iv(x);return I(self.a+x.a,self.b+x.b)
 __radd__=__add__
 def __neg__(self):return I(-self.b,-self.a)
 def __sub__(self,x):return self+-iv(x)
 def __rsub__(self,x):return iv(x)+-self
 def __mul__(self,x):
  x=iv(x);v=[self.a*x.a,self.a*x.b,self.b*x.a,self.b*x.b];return I(min(v),max(v))
 __rmul__=__mul__
 def __truediv__(self,x):
  x=iv(x);assert x.a*x.b>0;return self*I(1/x.b,1/x.a)
 def __rtruediv__(self,x):return iv(x)/self
 def __pow__(self,n):
  if n==0:return I(1)
  if n==1:return self
  return self*self**(n-1)
 def bounds(self):return (float(self.a),float(self.b))
def iv(x):return x if isinstance(x,I) else I(x)
P=[-1668726734798132632,279128064680059185038,49232500736262112787450,1337222696480289357993259,7838727530168235775250281,5925636804644733974727250]
def pol(c,w):
 v=0
 for x in c[::-1]:v=v*w+x
 return v
# Exact arithmetic in Q[w]/(P); every inversion checks that its divisor is a unit.
def trim(a):
 a=list(a)
 while a and not a[-1]:a.pop()
 return a

def pa(a,b):return trim([(a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0) for i in range(max(len(a),len(b)))])
def pn(a):return [-x for x in a]
def pm(a,b):
 c=[Q(0)]*max(0,len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]+=x*y
 return trim(c)
def pd(a,b):
 a=trim(a);b=trim(b);assert b;q=[Q(0)]*max(0,len(a)-len(b)+1)
 while len(a)>=len(b):
  k=len(a)-len(b);v=a[-1]/b[-1];q[k]=v;a=pa(a,pn([Q(0)]*k+[v*x for x in b]))
 return trim(q),a
class K:
 def __init__(self,a):self.p=pd([Q(x) for x in a] if isinstance(a,list) else [Q(a)],[Q(x) for x in P])[1]
 def __add__(self,b):return K(pa(self.p,kv(b).p))
 __radd__=__add__
 def __neg__(self):return K(pn(self.p))
 def __sub__(self,b):return self+-kv(b)
 def __rsub__(self,b):return kv(b)+-self
 def __mul__(self,b):return K(pm(self.p,kv(b).p))
 __rmul__=__mul__
 def inv(self):
  a=[Q(x) for x in P];b=self.p;u=[];v=[Q(1)]
  while b:
   q,r=pd(a,b);a,b=b,r;u,v=v,pa(u,pn(pm(q,v)))
  assert len(a)==1 and a[0];return K([x/a[0] for x in u])
 def __truediv__(self,b):return self*kv(b).inv()
 def __rtruediv__(self,b):return kv(b)*self.inv()
 def __pow__(self,n):return K(1) if n==0 else self*self**(n-1)
def kv(x):return x if isinstance(x,K) else K(x)
def macro(w):
 y=w*0+Q(1,25);z=2*y/(101-106*y)
 E=-3*(2078141123214034*w**3-649791530287147*w**2-10839225840795*w-118826118826)/(19336*(w-1)*(3171813530*w**2+17299342307*w-87038467))
 T1=-100*z-100*w+211*z*w;T2=w*(3-y);T3=-z*(100-101*y)
 x=(101*z+97*w-200*z*w)/((1-z)*(1-w));E2=(2*y+4*w-3*y*w)/((1-y)*(1-w))
 T0=3*y-z+3*w-14*y*z-4*y*w-8*z*w+13*y*z*w+(1-y)*(1-z)*(1-w)*E
 c=T2/(2+T2);d=-T1/(101-T1)
 C0=3*c-d-14*c*d+(1-c)*(1-d)*T0;C1=-100*d;C3=-2*c+d-5*c*d+(1-c)*(1-d)*T3
 b=C0/(1+C0);B1=b+(1-b)*C1;B3=b+(1-b)*C3;a=B3/(1+B3);A1=2*a+(1-a)*B1;A2=2*a
 R=1-x/3;V0=(E-x)/R;V2=(E2+x/3)/R;h=V0/3
 # Q minus prescribed payoff for every quiet player at finite collision roots.
 Cquiet0=-13*c*d-C0;Cquiet3=-100*d+101*c*d-C3
 Tquiet0=-13*y*z-3*w-4*y*w-4*z*w+19*y*z*w-T0
 # Direct forced-Quit0 coefficients: singles y,z give0; w gives-3; yz gives-13; yw gives-7; zw gives-7; yzw gives-5.
 Bquiet1=-100*b-B1;Bquiet3=-100*b-B3
 return locals()
Z=[
[0,0,3,0,-1,0,-12,-13,3,-3,2,-7,-6,-7,-8,-5],
[0,2,0,-1,1,5,-100,6,-3,3,-100,8,9,-8,11,-9],
[0,2,-2,-10,0,-10,0,-9,-1,-5,-1,10,3,-3,2,8],
[0,-1,-2,-12,1,7,-6,11,0,1,0,-10,-100,Q(15,2),1,Q(21,2)]]
def stage(q,tail):
 weights=[]
 for mask in range(16):
  v=q[0]*0+1
  for i in range(4):v*=q[i] if mask>>i&1 else 1-q[i]
  weights.append(v)
 return [sum(weights[m]*Z[i][m] for m in range(16))+weights[0]*tail[i] for i in range(4)]
def same(a,b):assert all(not(kv(x)-kv(y)).p for x,y in zip(a,b))
def check_raw(k):
 E=[k['E'],-k['x'],k['E2'],0];T=[k['T0'],k['T1'],k['T2'],k['T3']];C=[k['C0'],k['C1'],0,k['C3']];B=[0,k['B1'],0,k['B3']];A=[0,k['A1'],k['A2'],0];V=[k['V0'],0,k['V2'],0]
 roots=[([0,k['y'],k['z'],k['w']],E,T,[1,2,3],{0:k['Tquiet0']}),([0,k['c'],k['d'],0],T,C,[1,2],{0:k['Cquiet0'],3:k['Cquiet3']}),([0,0,k['b'],0],C,B,[2],{0:0,1:k['Bquiet1'],3:k['Bquiet3']})]
 for q,tail,U,active,quiet in roots:
  q=[kv(x) for x in q];same(stage(q,tail),U)
  for i in active:
   force=q.copy();force[i]=K(1);same([stage(force,[0]*4)[i]],[U[i]])
  for i,gap in quiet.items():
   force=q.copy();force[i]=K(1);same([stage(force,[0]*4)[i]-U[i]],[gap])
 same(stage([k['a'],K(0),K(0),K(0)],B),A)
 same(stage([K(0),K(0),K(0),k['h']],A),V)
 same(stage([K(0),K(0),K(0),k['x']/3],V),E)
if __name__=='__main__':
 wl=Q(3544554,10**9);wh=Q(3544555,10**9)
 assert pol(P,wl)<0<pol(P,wh) and all(c>0 for c in P[1:])
 k=macro(K([0,1]));check_raw(k);assert not (k['A1']*(1-k['h'])-3*k['h']).p;assert not (k['A2']*(1-k['h'])-k['V2']-k['h']).p
 v=macro(I(wl,wh))
 w=v['w']
 for t in [241494*w-7049,3171813530*w*w+2287878149*w-19696111,3171813530*w*w+17299342307*w-87038467]:assert t.b<0
 for name in ['w','y','z','c','d','a','b','h']:assert 0<v[name].a and v[name].b<1
 for t in [v['B1'],v['E']-v['x'],v['E2']-Q(3,100)*v['x'],v['x'],3-v['x'],v['V0'],v['V2']-Q(7,25),Q(28,125)-v['h'],v['T0']-1,v['C0']-1,v['A1'],v['A2']]:assert t.a>0
 for name in ['Cquiet0','Cquiet3','Tquiet0','Bquiet1','Bquiet3']:assert v[name].b<0
 print('EXACT RATIONAL PASS: raw table, quintic root, macro closure, all bridge and wash guards')
