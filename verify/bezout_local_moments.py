"""Ordinary numerical evaluation of Bui--Hall arXiv:2304.05178 Prop. 2.
Auxiliary derivatives extracted exactly as multiaffine coefficients; finite
Gauss quadrature integrates polynomial inputs. Not a proof certificate.
"""
import numpy as np
from numpy.polynomial.legendre import leggauss
from scipy.optimize import minimize_scalar

def cube(order, dim):
    z,w=leggauss(order);z=(z+1)/2;w=w/2
    ids=np.indices((order,)*dim).reshape(dim,-1)
    return z[ids], np.prod(w[ids],axis=0)

def integrated_pcoeff(poly, order=9):
    p=np.polynomial.Polynomial(poly)
    dp=p.deriv();ddp=p.deriv(2)
    (r,s,u,v),w=cube(order,4)
    t1=(1-r)*u;t4=(1-r)*v
    ans=np.zeros(256)
    for t2,t3 in [(r*s,r),(r,r*s)]:
        vals=[1-t1-t3,1-t2-t4,1-t1-t2,1-t3-t4]
        jac=r*(1-r)**2
        arr=[[p(x),dp(x),ddp(x)] for x in vals]
        for mask in range(256):
            q=w*jac
            for j in range(4):
                q=q*arr[j][((mask>>j)&1)+((mask>>(j+4))&1)]
            ans[mask]+=q.sum()
    return ans

def linmul(a,b):
    out=a*b[0]
    for j in range(8):
        ids=np.arange(256)
        lo=ids[(ids & (1<<j))==0]
        out[lo+(1<<j)]+=a[lo]*b[j+1]
    return out

def tensor(theta,poly,orders=(7,9)):
    us,w=cube(orders[0],4);u1,u2,u3,u4=us
    n=len(w)
    def constant(v):
        a=np.zeros((9,n));a[0]=v;return a
    sx=constant(0);sx[1:5]=1
    sz=constant(0);sz[5:9]=1
    e=[constant(0) for j in range(8)]
    for j in range(8):e[j][j+1]=1
    x1,x2,x3,x4,z1,z2,z3,z4=e
    one=constant(1)
    bx=one+theta*sx;bz=one+theta*sz
    c=constant(u1-u2)+theta*(-x1-x2+z1+z2+u1*sx-u2*sz)
    d=constant(u1-u2)+theta*(-x3-x4+z3+z4+u1*sx-u2*sz)
    rs=[constant(.5)+theta*(x1+x2)-u1*bx+u3*c,
        constant(.5)+theta*(z1+z2)-u2*bz-u3*c,
        constant(.5)+theta*(x3+x4)-u1*bx+u4*d,
        constant(.5)+theta*(z3+z4)-u2*bz-u4*d]
    pref=np.zeros((256,n));pref[0]=1
    for l in [bx,bz,c,d]:pref=linmul(pref,l)
    pc=integrated_pcoeff(poly,orders[1])[::-1]
    out={}
    for ks in [(0,0,0,0),(0,0,1,1),(1,1,1,1),(0,0,2,2),(1,1,2,2)]:
        a=pref.copy()
        for j,k in enumerate(ks):
            for _ in range(k):a=linmul(a,rs[j])
        sign=(-1)**(ks[2]+ks[3]+sum(ks)//2)
        out[ks]=sign*np.dot(pc, a@w)/(2*theta**4)
    return out

def clipping(theta,poly,ms):
    p=np.polynomial.Polynomial(poly)
    dp=p.deriv(); a=.5*p(1)**2+(dp*dp).integ()(1)/(6*theta)+theta*(p*p).integ()(1)
    m0,m01,m11,m02,m12=[ms[k] for k in [(0,0,0,0),(0,0,1,1),(1,1,1,1),(0,0,2,2),(1,1,2,2)]]
    def b(v):return m01+v*v*m11+np.sqrt((m0+v*v*m01)*(m02+v*v*m12))
    fit=minimize_scalar(lambda lv: -4*np.exp(lv)*a*a/b(np.exp(lv))+1,bounds=(-6,6),method='bounded')
    v=np.exp(fit.x);k=np.sqrt((m02+v*v*m12)/(m0+v*v*m01))
    return dict(a=a,v=v,k=k,b=b(v),simple_lower=-fit.fun)

if __name__=='__main__':
    import json,sys
    theta=float(sys.argv[1]) if len(sys.argv)>1 else .125
    poly=[0,0,1]
    ms=tensor(theta,poly)
    print(json.dumps({str(k):v for k,v in ms.items()},indent=2))
    print(clipping(theta,poly,ms))
    known=52*theta/1215+491/5040+563/(6300*theta)+659/(16200*theta**2)+8/(945*theta**3)+1/(1512*theta**4)
    print('published m0022 comparison',ms[(0,0,2,2)],known)
