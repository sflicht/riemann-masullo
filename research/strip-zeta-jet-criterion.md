# A zeta-derivative criterion for the positive-width strip trace

This is a mathematical reduction for Masullo, Theorem 10.3.2.1(1), pp. 453–455, especially (10.3.2.7). It concerns the Riemann zeta component. It uses the project's existing necessary angle estimate and sufficient coordinate estimate. The argument below has not been formalized in Lean. [Issue #7241 and the component estimates](https://github.com/mccorvie/riemann-masullo/issues/7241#issuecomment-7126304685) · [Majorant in #7455](https://github.com/mccorvie/riemann-masullo/issues/7455)

## Statement

Take the trivial character of the norm-one idele classes of $\mathbf Q$, choose the trivial representative, set $a=1/2$, $\alpha=1$, and fix any Sobolev exponent $s>1$. In the ordinary zeta variable $u$, the strip is $-1/2\le\Re u\le 3/2$. Every nontrivial zeta zero is in its interior, so all its jets survive. Write $m_\rho$ for the multiplicity of a distinct nontrivial zero $\rho$ and $T_\rho=2+|\Im\rho|$.

For this component the following are equivalent.

1. For every homogeneous compact Bruhat test and every compact insertion, the complete zero-block series of #7241 is summable.
2. For every such test, the jet-norm majorant of #7455 is summable.
3. There are constants $c>0$ and $A\ge0$ such that, for every $\rho$,

$$
\frac{|\zeta^{(m_\rho)}(\rho)|}{m_\rho!}\ \ge\ c T_\rho^{-A}.
\tag{1}
$$

Neither zero simplicity nor a height-independent multiplicity bound is assumed in this equivalence. Condition (1) is an arithmetic hypothesis. Proving it is a separate problem.

## The two inputs from the trace problem

Use the radial variable $x=\log|g|$ and Mellin transform $f\mapsto \int f(x)e^{(u-1/2)x}\,dx$. Up to the fixed Haar scalar, the ambient squared norm integrates $|f(x)|^2 e^{2|x|}(1+x^2)^{s/2}$. The $k$th jet evaluates the $k$th derivative in $u$. The quotient has the induced norm. Write $\Lambda_{\rho,k}$ for the realized jet functional and $x_{\rho,k}$ for its biorthogonal vector.

- Statement 1, even restricted to rank-one insertions, gives $\|\Lambda_{\rho,0}\|\le C T_\rho^d\,\operatorname{dist}(\Lambda_{\rho,0},V_\rho)$, where $V_\rho$ is the closed span of the jets at *other* sites. [Polynomial angle estimate](https://github.com/mlyle/riemann-masullo/blob/094293aeeaf5b58f7b194e1e779aac4c330a6251/research/I314LineGaps.lean#L2476)
- Polynomial bounds for $\|\Lambda_{\rho,k}\|\|x_{\rho,k}\|$, uniform over $0\le k<m_\rho$, imply statement 2. The transform of a fixed test decays rapidly on the fixed Mellin circles, and the divisor count includes multiplicity. Statement 2 implies statement 1 for every bounded insertion. [Component majorant](https://github.com/mlyle/riemann-masullo/blob/5127c420c58c42dddacb86d87d941f88aea922e4/research/I314PositiveCoordinates.lean#L210) · [Upstream block estimate](https://github.com/mccorvie/riemann-masullo/blob/e48845bae927da9dbfdc0e82f2d67848b37bf333/RiemannMasullo/Ch10_TraceSpectral/Sec3_Isolated.lean#L69)

## Necessity: Jensen's formula counts the nearby jets

The norms of zeroth-order evaluations are uniformly bounded below. In log norm, a fixed nonnegative bump modulated by $e^{-i(\Im\rho)x}$ has bounded norm and evaluation bounded below for $0\le\Re\rho\le1$. Orthogonal projection off $V_\rho$ in the Hilbert dual therefore gives a quotient vector of norm $O(T_\rho^d)$ whose evaluation at $\rho$ is one and whose jets vanish at every other site. Lift it to a minimum-norm radial representative. Its Mellin transform $f_\rho$ satisfies $f_\rho(\rho)=1$ and vanishes to order at least $m_\nu$ at each $\nu\ne\rho$. Cauchy–Schwarz bounds $|f_\rho|$ by $O(T_\rho^d)$ throughout $|u-\rho|\le1/4$, since these disks have a uniform positive margin inside the Sobolev strip.

With $R=1/4$, Jensen's formula gives

$$
J_\rho=\sum_{0<|\nu-\rho|<R}m_\nu\log\frac{R}{|\nu-\rho|}
\ \ll\ \log T_\rho.
\tag{2}
$$

In fact (2) is equivalent to (1). The local product estimate for $\log|\zeta(u)|$ writes it as $\sum_{|\Im\nu-\Im u|\le1}m_\nu\log|u-\nu|+O(\log T_\rho)$ near $\rho$. Approach $\rho$ and subtract $m_\rho\log|u-\rho|$. Ties at the height cutoffs can only add bounded summands per zero. There are $O(\log T_\rho)$ zeros with multiplicity in this window. The terms outside the $R$-disk and the change of scale by $R$ thus cost $O(\log T_\rho)$ in total. Consequently

$$
\log\left|\frac{\zeta^{(m_\rho)}(\rho)}{m_\rho!}\right|
= -J_\rho+O(\log T_\rho).
$$

The standard estimates apply at large height; conjugation and the finitely many remaining zeros give the assertion for all $\rho$. [Titchmarsh, *The Theory of the Riemann Zeta-function*, Theorem 9.6(B)](https://sites.math.rutgers.edu/~zeilberg/EM18/TitchmarshZeta.pdf) · [Montgomery–Vaughan, Chapter 16, local formula](https://personal.science.psu.edu/rcv4/personal/Publications/MNTI/16.0_pp_397_418_Explicit_formulae.pdf)

## Sufficiency: interpolants for all derivative orders

Assume (1), hence (2). Put $P(u)=(u-1)\zeta(u)$, $m=m_\rho$, $v=u-\rho$ and $g_\rho(u)=P(u)/v^m$, with its removable value filled in. Let

$$
r=\tfrac14\min(1,\operatorname{dist}(\rho,\{\nu:\nu\ne\rho\})),
$$

where the set consists of the other distinct nontrivial zeros. Then $r^{-m}\le T_\rho^{O(1)}$. Indeed, when a nearest neighbour $\nu$ is closer than $R$, the sum (2) **at $\nu$** contains $m_\rho\log(R/|\nu-\rho|)$. The change of scale and the other case cost $O(m_\rho)=O(\log T_\rho)$. This use of the neighbour's estimate accounts for the multiplicity at the interpolation site itself.

On the unit disk about $\rho$, $|g_\rho|\le T_\rho^{O(1)}$ by the maximum principle on its circumference and polynomial growth of $P$ on a fixed vertical strip. On the disk of radius $2r$, $g_\rho$ is zero-free at large height. At the center, (1) gives $|g_\rho(\rho)|^{-1}\le T_\rho^{O(1)}$. Harnack's inequality for the positive harmonic function $\log(M/|g_\rho|)$, with $M$ a polynomial upper bound chosen strictly above the supremum, gives $\sup_{|v|\le r}|1/g_\rho(\rho+v)|\le T_\rho^{O(1)}$.

Choose a fixed large integer $L$ and let $q_\rho(u)=(1+v/4)^{-L}$. For $0\le k<m$, use the principal part at $\rho$ to define

$$
H_{\rho,k}(u)=P(u)q_\rho(u)\,
\operatorname{PP}_{u=\rho}\!\left(\frac{v^k}{k!\,P(u)q_\rho(u)}\right).
\tag{3}
$$

The principal part is a finite sum of $v^{-1},\ldots,v^{-(m-k)}$. Its coefficients are bounded by $T_\rho^{O(1)}/k!$ by Cauchy's formula on $|v|=r$ and the bound on $r^{-m}$. The constants and exponents here are independent of $k$ and $\rho$. At $\rho$, (3) equals $v^k/k!+O(v^m)$. At every other zero $\nu$, the factor $P$ gives all $m_\nu$ required vanishings.

On the two enlarged boundary lines $\Re u=-1,2$, $|v|\ge1$. The principal part is bounded there by $mT_\rho^{O(1)}/k!$. The damping factor supplies decay in $|\Im(u-\rho)|$. Taking $L$ greater by at least three than a polynomial growth exponent of $P$ on $[-1,2]$ yields
$$
|H_{\rho,k}(u)|\ \ll\ (1+|\Im(u-\rho)|)^{-2}\,T_\rho^{O(1)}/k!
$$
on both lines. The apparent pole at $\rho$ is removable, and the pole of $q_\rho$ is outside the enlarged strip. Fourier inversion on the center line, shifting the contour to each enlarged boundary and applying Plancherel, gives a radial representative with norm $T_\rho^{O(1)}/k!$ in the original Sobolev space. In detail, the enlarged lines control the two squared weights $e^{3x}$ and $e^{-3x}$, whose sum dominates $e^{2|x|}(1+x^2)^{s/2}$ for fixed $s$. The horizontal sides vanish in the contour shift by the same polynomial decay at large imaginary part.

The quotient class has exactly the prescribed derivative evaluations. Totality of the dual jets identifies it with $x_{\rho,k}$, up to the fixed normalization of radial Haar measure. Conversely, the uniform point-evaluation upper bound on the disks of radius $1/4$ and Cauchy's inequality give $\|\Lambda_{\rho,k}\|\ll 4^k k!$. The factorials cancel, and $4^k\le T_\rho^{O(1)}$ since $k<m_\rho=O(\log T_\rho)$. This proves the coordinate-product estimate from (1) and completes the equivalence.

For simple zeros, (1) becomes a polynomial lower bound for $|\zeta'(\rho)|$. In that case any polynomial upper bound for the discrete negative second moment $\sum_{0<\Im\rho\le T}|\zeta'(\rho)|^{-2}$ suffices. The Gonek–Hejhal prediction is much sharper. The general criterion above also covers a zero at which the first derivative vanishes. [Ng, discussion of the discrete negative moments](https://www.cs.uleth.ca/~nathanng/RESEARCH/mobius2b.pdf)

Prepared with Codex assistance.