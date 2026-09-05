"""Exact rational certificate: one scaled top-hat block cannot certify 85%.
Uses assumed closed block moments only to supply a feasible three-atom law.
No assertion that these moments are the actual zero-matrix moments.
"""
from fractions import Fraction as Q
from collections import deque
ZERO=Q(0);ONE=Q(1);BTRIM=Q(3,40);DSTAR_LO=Q(13,10);TARGET=Q(23,20)
K_LO=Q(8,9);K_HI=Q(9,10) # 8/9 < 2/sqrt(5) < 9/10
assert K_LO*K_LO<Q(4,5)<K_HI*K_HI

def remaining_weights(a):
 w=[5*a/24,7*a/12,5*a/24];b=BTRIM
 for j in [2,1,0]:
  take=min(b,w[j]);w[j]-=take;b-=take
 return w

def interval_margin(al,ah,ml,mh):
 # D>= B+Jqq+2Jqr by nonnegative kernel; Jensen for B.
 Bl=ONE+al/(ONE-al)*(ml-ONE)**2
 Jl=ml*ml*al**3/3+max(ZERO,ONE-ah*mh)*ml*al*al/2
 Dl=max(DSTAR_LO,Bl+Jl)
 wl,wm,wh=remaining_weights(ah)
 yl=max(ZERO,mh*(ONE-K_LO*al)-ONE)
 ym=max(ZERO,mh-ONE)
 yh=max(ZERO,mh*(ONE+K_HI*ah)-ONE)
 Tu=wl*yl*yl+wm*ym*ym+wh*yh*yh
 return Dl-Tu-TARGET

queue=[(BTRIM,Q(1,2),ONE,ONE/BTRIM,0)];accepted=0;pruned=0;depth=0;minmargin=ONE;boxes=[]
while queue:
 al,ah,ml,mh,d=queue.pop()
 if al*ml>ONE:pruned+=1;continue
 margin=interval_margin(al,ah,ml,mh)
 if margin>0:
  accepted+=1;depth=max(depth,d);minmargin=min(minmargin,margin);boxes.append((al,ah,ml,mh));continue
 if d>40:raise RuntimeError(('unresolved',al,ah,ml,mh,float(margin)))
 # Split larger relative interval.
 if (ah-al)/(Q(1,2)-BTRIM)>(mh-ml)/(ONE/BTRIM-ONE):
  mid=(al+ah)/2;queue.extend([(al,mid,ml,mh,d+1),(mid,ah,ml,mh,d+1)])
 else:
  mid=(ml+mh)/2;queue.extend([(al,ah,ml,mid,d+1),(al,ah,mid,mh,d+1)])
print('Exact interval proof completed')
print('accepted boxes',accepted,'infeasible boxes',pruned,'max depth',depth)
print('minimum certified margin',minmargin,'=',float(minmargin))
# Omitted easy regions: a<=3/40 => all block modes removed; m<=1 =>
# full positive tail <= a^3/6 <=1/48, so D-tail >=13/10-1/48>23/20.
assert DSTAR_LO-Q(1,48)>TARGET
