"""Exact flat mixed Volterra moments and cosine quadrature. Research, not proof."""
from fractions import Fraction
from functools import lru_cache
from itertools import permutations
from math import comb, factorial, pi
import argparse
import json
from pathlib import Path
import numpy as np
from scipy.special import betaincinv
from scipy.stats import qmc
import sympy as sp


@lru_cache(None)
def logistic_moment(k):
    if k % 2:
        return Fraction(0)
    if k == 0:
        return Fraction(1)
    return Fraction((2**k - 2) * abs(sp.bernoulli(k)))


@lru_cache(None)
def D(a, b):
    """Integral over I of g^a conjugate(g)^b, g=(1+iY)/2."""
    ans = Fraction(0)
    for i in range(a + 1):
        for j in range(b + 1):
            if (i + j) % 2 == 0:
                ans += (comb(a, i) * comb(b, j)
                        * (-1)**(j + (i + j)//2)
                        * logistic_moment(i + j))
    return ans / 2**(a + b)


@lru_cache(None)
def C(m, n):
    """Integral over R of g^m conjugate(g)^n; m,n>=1."""
    return sum(((-1)**(m - 1 - j) * D(j, m + n - 1 - j)
                for j in range(m)), Fraction(0))


def flat_moment(m, n, width=Fraction(1)):
    val = C(m, n)
    for r in range(1, min(m, n) + 1):
        val += (comb(m, r) * comb(n, r) * factorial(r)
                * width**(2*r) * D(m-r, n-r) / factorial(2*r + 1))
    return width**(1-m-n) * val


def flat_gram(degree, width=Fraction(1)):
    return [[flat_moment(m, n, width) for n in range(1, degree + 1)]
            for m in range(1, degree + 1)]


def cosine_gram(degree, width=1.0, sobol_power=12, seed=1):
    """QMC of the exact finite functional. Includes the width-one limit."""
    beta = np.sqrt(2.0)
    norm = beta / (2*np.sin(beta*width/2))
    def u(x):
        return norm*np.cos(beta*x)
    nodes, weights = np.polynomial.legendre.leggauss(120)
    dens = u(nodes*width/2)
    matrix = np.array([
        [float(C(m,n))*np.dot(weights, dens**(m+n))*width/2
         for n in range(1,degree+1)]
        for m in range(1,degree+1)
    ])
    pieces = [matrix.copy()]
    for r in range(1, degree+1):
        q = qmc.Sobol(r+1, scramble=True, seed=seed+r).random_base2(sobol_power)
        remaining = np.ones(len(q))
        lengths = np.empty((len(q), r))
        for j in range(r):
            stick = betaincinv(2, 2*(r-j), q[:,j])
            lengths[:,j] = remaining*stick
            remaining *= 1-stick
        lengths *= width
        left = -width/2 + q[:,r]*width*remaining
        right = left + np.sum(lengths, axis=1)
        endpoint = np.sqrt(u(left)*u(right))
        sym = np.zeros((len(q), degree-r+1))
        for perm in permutations(range(r)):
            interior = left[:,None] + np.cumsum(lengths[:,perm],axis=1)[:,:-1]
            densities = np.column_stack((u(left), u(interior), u(right)))
            prefactor = endpoint*np.prod(densities[:,1:-1],axis=1)
            homogeneous = np.zeros((len(q),degree-r+1))
            homogeneous[:,0] = 1
            for column in densities.T:
                for k in range(1, degree-r+1):
                    homogeneous[:,k] += column*homogeneous[:,k-1]
            sym += prefactor[:,None]*homogeneous
        spatial = (sym.T @ sym)/len(q)
        spatial *= width**(2*r+1)/(factorial(r)*factorial(2*r+1))
        height = np.array([[float(D(a,b)) for b in range(degree-r+1)]
                           for a in range(degree-r+1)])
        piece = np.zeros_like(matrix)
        piece[r-1:,r-1:] = spatial*height
        matrix += piece
        pieces.append(piece)
    return matrix, pieces


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--degree",type=int,default=8)
    parser.add_argument("--cosine-degree",type=int,default=0)
    parser.add_argument("--sobol-power",type=int,default=12)
    parser.add_argument("--output",default="ordered_gram.json")
    args=parser.parse_args()
    exact=flat_gram(args.degree)
    result={"flat_width":1,"flat_gram_exact":[[str(v) for v in row] for row in exact],
            "flat_gram_float":[[float(v) for v in row] for row in exact]}
    if args.cosine_degree:
        first,pieces=cosine_gram(args.cosine_degree,sobol_power=args.sobol_power,seed=1)
        second,_=cosine_gram(args.cosine_degree,sobol_power=args.sobol_power,seed=193)
        result["cosine_gram_qmc"] = ((first+second)/2).tolist()
        result["cosine_scramble_difference"] = np.abs(first-second).tolist()
        result["cosine_pair_pieces_first_scramble"] = [v.tolist() for v in pieces]
    Path(args.output).write_text(json.dumps(result,indent=2)+"\n")
    print(args.output)
    print("flat degrees 1-4:",[[str(v) for v in row[:4]] for row in exact[:4]])
    if args.cosine_degree:
        print("cosine diagonal:",np.diag((first+second)/2))
        print("max scramble difference:",np.max(np.abs(first-second)))


if __name__=="__main__":
    main()
