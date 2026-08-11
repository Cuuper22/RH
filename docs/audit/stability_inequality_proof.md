# Stability inequality proof (verified)

## Statement

Let \(G,P,Q\) be finite Hermitian matrices of the same size and suppose

\[
 G=P+Q,\qquad P\succeq0,\qquad
 \operatorname{rank}P\le s,\qquad \operatorname{tr}P\le s,
\tag{1}
\]

\[
 n_+(Q)\le b,\qquad s+2b\le N,
\tag{2}
\]

and

\[
 \operatorname{tr}G=N,\qquad \lVert G\rVert_F^2\le DN.
\tag{3}
\]

Write eigenvalues in decreasing order.  Then

\[
 \boxed{
 \sum_{i>b}(\lambda_i(G)-1)_+^2
 \le s-(2-D)N.}
\tag{4}
\]

If \(C\) is any principal compression of \(G\), then the same right-hand
side bounds

\[
 \sum_{i>b}(\lambda_i(C)-1)_+^2.
\tag{5}
\]

## 1. Remove the free positive directions

Use the spectral positive and negative parts

\[
 Q=Q_+-Q_-,\qquad Q_+,Q_-\succeq0,\qquad Q_+Q_-=0,
\tag{6}
\]

and put

\[
 R=P-Q_-.
\tag{7}
\]

Since \(\operatorname{rank}Q_+=n_+(Q)\le b\) and \(G=R+Q_+\), the
rank-\(b\) form of Weyl interlacing gives

\[
 \lambda_{b+j}(G)\le\lambda_j(R).
\tag{8}
\]

The function \(x\mapsto(x-1)_+^2\) is increasing, hence

\[
 \sum_{i>b}(\lambda_i(G)-1)_+^2
 \le \sum_j(\lambda_j(R)-1)_+^2.
\tag{9}
\]

Moreover, \(R\preceq0\) on \((\operatorname{ran}P)^\perp\).  Therefore

\[
 n_+(R)\le\operatorname{rank}P\le s.
\tag{10}
\]

For any Hermitian \(R\) with eigenvalues \(r_j\),

\[
\begin{aligned}
 \sum_j(r_j-1)_+^2
 &\le \sum_j(r_j^2-2r_j)+n_+(R)\\
 &\le \lVert R\rVert_F^2-2\operatorname{tr}R+s.
\end{aligned}
\tag{11}
\]

To check the first line, add one unit for each positive eigenvalue.  For
\(0<r_j\le1\) the resulting contribution is \((1-r_j)^2\ge0\); for
\(r_j\le0\) it is \(r_j^2-2r_j\ge0\); and for \(r_j>1\) it equals the
left-hand contribution.

Combining (9) and (11),

\[
 \sum_{i>b}(\lambda_i(G)-1)_+^2
 \le \lVert R\rVert_F^2-2\operatorname{tr}R+s.
\tag{12}
\]

## 2. Exact rank--trace slack

Because \(Q_+Q_-=0\), expansion of \(G=P+Q_+-Q_-\) gives the exact identity

\[
\begin{aligned}
 &\lVert G\rVert_F^2-4\operatorname{tr}G+3s+4b
 -(\lVert R\rVert_F^2-2\operatorname{tr}R+s)\\
 &=\lVert Q_+\rVert_F^2-4\operatorname{tr}Q_++4b
   +2\operatorname{tr}(PQ_+)\\
 &\qquad +2\operatorname{tr}Q_-+2(s-\operatorname{tr}P).
\end{aligned}
\tag{13}
\]

Every term on the right is nonnegative:

- if \(q_1,\ldots,q_r>0\) are the positive eigenvalues of \(Q\), with
  \(r\le b\), then

  \[
   \lVert Q_+\rVert_F^2-4\operatorname{tr}Q_++4b
   =\sum_{j=1}^r(q_j-2)^2+4(b-r)\ge0;
  \tag{14}
  \]

- \(\operatorname{tr}(PQ_+)\ge0\) for positive-semidefinite \(P,Q_+\);
- \(\operatorname{tr}Q_-\ge0\); and
- \(s-\operatorname{tr}P\ge0\).

No commutativity of \(P\) and \(Q_+\) is used: positivity of the trace
follows from
\(\operatorname{tr}(PQ_+)=\operatorname{tr}(P^{1/2}Q_+P^{1/2})\).

Equations (12)--(14) imply

\[
 \sum_{i>b}(\lambda_i(G)-1)_+^2
 \le \lVert G\rVert_F^2-4\operatorname{tr}G+3s+4b.
\tag{15}
\]

## 3. Insert the trace budget

From \(s+2b\le N\),

\[
 4b\le2(N-s).
\tag{16}
\]

Using (3), (15), and (16),

\[
\begin{aligned}
 \sum_{i>b}(\lambda_i(G)-1)_+^2
 &\le DN-4N+3s+2(N-s)\\
 &=s-(2-D)N,
\end{aligned}
\tag{17}
\]

which is (4).

## 4. Principal compressions

If \(C\) is a principal compression of \(G\), Cauchy interlacing gives

\[
 \lambda_i(C)\le\lambda_i(G)
\tag{18}
\]

for every index occurring in \(C\).  Applying the same increasing function
\(x\mapsto(x-1)_+^2\) term by term proves (5).

## Audit conclusion

The stability inequality is algebraically valid under assumptions (1)--(3).
Its proof uses only spectral positive/negative parts, Weyl and Cauchy
interlacing, and the exact nonnegative slack (13).  It does not depend on the
R1a Gabor nesting construction.

## Machine verification

The argument is formalized in `RH/Zeta85/Stability.lean`.  The
headline `RH.Zeta85.stability_inequality` is equation (4);
`stability_inequality_isometricCompression` and
`stability_inequality_principalCompression` give equation (5).

The file proves the two interlacing inputs from threshold-count and rank
arguments rather than taking them as fields.  Its five public stability and
compression headlines have dependency output
`[propext, Classical.choice, Quot.sound]`, checked on every CI run by
`comparator/PrintAxioms/Stability.lean`.
