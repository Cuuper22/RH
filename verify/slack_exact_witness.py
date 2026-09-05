"""Exact rational feasibility witness for the degree-eight tracial test."""
import itertools
import sympy as s
from ordered_polynomial_functional import flat_gram
mom = flat_gram(8)
def sw(w):return w.translate(str.maketrans('ab','ba'))
def ca(w):return min(x[i:]+x[:i] for x in [w,w[::-1],sw(w),sw(w)[::-1]] for i in range(len(x)))
def words(n):return [''.join(x) for x in itertools.product('ab',repeat=n)]
unknown={}
def val(w):
 if len(w)==1:return s.Rational(1,2)
 if len(set(w))==1:return s.Integer(0)
 key=ca(w)
 if sum(w[i]!=w[(i+1)%len(w)] for i in range(len(w)))==2:return s.Rational(mom[w.count('a')-1][w.count('b')-1])
 if key not in unknown:unknown[key]=s.Symbol('x_'+key)
 return unknown[key]
k=4
W=sum([words(j) for j in range(1,k+1)],[]);U=['']+sum([words(j) for j in range(1,k)],[]);Un=U[1:]
p=[(1,w) for w in words(3)]+[(-3,w) for w in words(2)]+[(2,w) for w in words(1)]
e=[(2,w) for w in words(1)]+[(-1,w) for w in words(2)]
f=[(s.Rational(-1,2),w) for w in words(1)]+[(s.Rational(1,2),w) for w in words(2)]
g=[(s.Rational(-3,2),w) for w in words(1)]+[(s.Rational(1,2),w) for w in words(2)]
GM=s.Matrix([[val(sw(x[::-1])+y) for y in W] for x in W])
def loc(poly,U):return s.Matrix([[sum(c*val(sw(x[::-1])+w+y) for c,w in poly) for y in U] for x in U])
LE=loc(e,U);LF=loc(f,U);LC=loc(g,Un)+s.Matrix([[val(sw(x[::-1])+y) for y in Un] for x in Un])
eqs=[sum(c*val(w+q) for c,w in p) for q in ['']+sum([words(j) for j in range(1,2*k-2)],[])]
xx=list(unknown.values());ss=dict(zip(xx,next(iter(s.linsolve(eqs,xx)))))
raw=[M.subs(ss) for M in [GM,LE,LF,LC]]
free=sorted(set().union(*(x.free_symbols for M in raw for x in M)),key=str)
xvals=[s.Rational(t,1000000) for t in [-5111,24632,164982,741260,639692,1156934]]
for bi,MM in enumerate(raw):
 M=MM.subs(dict(zip(free,xvals)));positives=0;zeros=0
 for j in range(M.rows):
  d=M[j,j]
  if d<0:raise ValueError(('negative pivot',bi,j,d))
  if d==0:
   assert all(M[i,j]==0 for i in range(j+1,M.rows)),(bi,j)
   zeros+=1;continue
  positives+=1
  for u in range(j+1,M.rows):
   for v in range(u,M.rows):
    M[v,u]=M[u,v]=M[u,v]-M[u,j]*M[v,j]/d
 print('EXACT_PSD',bi,'positive_pivots',positives,'zero_pivots',zeros,flush=True)
