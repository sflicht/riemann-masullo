# A zeta-derivative criterion for the positive-width strip trace

This is a mathematical reduction for Masullo, Theorem 10.3.2.1(1), pp. 453–455, especially (10.3.2.7). It concerns the Riemann zeta component. It uses the project's existing necessary angle estimate and sufficient coordinate estimate. Under (1), the fork constructs [radial witnesses for ordinary zeta](StripZetaCardinal.lean) and [physical witnesses for the rational trivial character](StripRationalChart.lean). The latter pairs with every admitted ambient jet and gives a height-uniform distance bound for each chosen jet at height at least two. The [finite Gram estimate](StripGramEstimate.lean) bounds the coordinate at every ordinate, uniformly in the finite block. For this component, the [Mellin-weighted sum over all retained jets](StripRationalTrace.lean) now satisfies the uniform bound in #7455 under (1). The arithmetic lower bound in (1) remains open. [Issue #7241 and the component estimates](https://github.com/mccorvie/riemann-masullo/issues/7241#issuecomment-7126304685) · [Majorant in #7455](https://github.com/mccorvie/riemann-masullo/issues/7455)

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

The standard estimates apply at large height; conjugation and the finitely many remaining zeros give the assertion for all $\rho$. [Titchmarsh, *The Theory of the Riemann Zeta-function*, Theorem 9.6(B)](https://sites.math.rutgers.edu/~zeilberg/EM18/TitchmarshZeta.pdf) · [Montgomery–Vaughan, local formula](https://personal.science.psu.edu/rcv4/personal/Publications/MNTI/16.0_pp_397_418_Explicit_formulae.pdf)

## Bounds for isolated zeros

For some fixed $A>0$, the simple zeros satisfying
$$
|\zeta'(\rho)|\ge (2+|\Im\rho|)^{-A}
$$
have lower limiting proportion at least $13/20$ among all positive-height nontrivial zeros counted with multiplicity. This follows from Lamzouri's unconditional isolation theorem, Titchmarsh's local product formula, and the Riemann–von Mangoldt count. The finite packing and derivative estimates in the deduction are proved in Lean. The asymptotic theorems are inputs from the literature. [Lamzouri, Theorem 1.1, especially (1.5)](https://arxiv.org/abs/2610.26841) · [Titchmarsh, Chapter IX](https://sites.math.rutgers.edu/~zeilberg/EM18/TitchmarshZeta.pdf) · [Finite packing and derivative estimates](StripZetaIsolated.lean)

Put $R=1/4$. Let $S$ be a finite set of zeros such that every center's ordinate differs from the ordinate of every other zero site by at least $\delta>0$. Write $Z$ for the set of zeros in the closed quarter-disks around these centers, with each center omitted from its own disk. Then
$$
\sum_{\rho\in S} J_\rho
\le \frac{2R}{\delta}\sum_{\nu\in Z} m_\nu .
$$

Fix a source zero $\nu$ and look at the centers to which it contributes. Within distance $r$ there are at most $r/\delta$ on either side of its ordinate. The first is at least $\delta$ away and the rest have successive gaps at least $\delta$. Complex distance dominates ordinate distance, so the bound also covers off-line sources. Integrating $2r/\delta$ against $dr/r$ up to $R$ gives a total charge of at most $2R/\delta$ per unit of source multiplicity. Interchanging the finite sums proves the inequality.

For the density deduction, choose $c>0$ so that Lamzouri's lower limiting isolated proportion is $p>13/20$. Take his isolated ordinates between $\sqrt X$ and $X$, with $\delta=2\pi c/\log X$. These zeros are simple, and deleting the lower ordinates costs $o(N(X))$. Their source multiplicity is at most $N(X+1)\sim N(X)$. For fixed $K>0$, at most $(1+o(1))N(X)/(4\pi cK)$ centers can have $J_\rho>K\log X$. Choose $K$ so that $1/(4\pi cK)<p-13/20$. By the local product estimate above, all the remaining centers satisfy $\log|\zeta'(\rho)|\ge -(K+D)\log X$ for a fixed $D>0$. Since $\Im\rho\ge\sqrt X$, one exponent $A=2(K+D)$ works in terms of the zero's own height. The conclusion concerns the coefficient on this subfamily. The finite Gram estimate in #7455 still requires control across the full component.

## Gram bounds at simple zeros

For $F=\mathbf Q$, $a=1/2$, $\alpha=1$, and the trivial representative, fix $s\ge0$. Let $u_\rho$ be the zeroth jet at an ordinary simple zero $\rho$ of height at least two. Write $Q_\rho(S)$ for its norm times its finite Gram coordinate in a finite set $S$ of ambient jets. There is a constant $C_s$ such that
$$
Q_\rho(S)\,|\zeta'(\rho)|\le C_s(10+|\Im\rho|)^4 .
$$
The set $S$ may include arbitrary jets at other characters or at repeated zeros. Each ordinary simple zero in the critical strip corresponds to a rational spectral site with exactly one retained jet. [Coordinate estimate and site identification](StripSimpleGram.lean)

To construct the separating functional, use the local variable $v$ around the selected zero. Set $F_\rho(v)=(\rho+v-1)\zeta(\rho+v)/(1+v/4)^7$ with the pole removed, and use the interpolant
$$
H_\rho(v)=\frac{F_\rho(v)}{v F_\rho'(0)},\qquad H_\rho(0)=1 .
$$
All other zeros retain their full orders. On the lines used for Mellin inversion, $|v|\ge1$. The established envelope for $F_\rho$ costs a fifth power of height. Since $F_\rho'(0)=(\rho-1)\zeta'(\rho)$ and $10+|\Im\rho|\le6|\rho-1|$ at these heights, the physical witness costs only a fourth power times $1/|\zeta'(\rho)|$.

Two finite-sum estimates follow in Lean. First, the Mellin-weighted sum in (10.3.2.7) stays uniformly bounded when each simple high row is weighted by $|\zeta'(\rho)|$, across all such rows. Second, the original row weights suffice on the subfamily where $|\zeta'(\rho)|\ge b(2+|\Im\rho|)^{-A}$. The second result and the density argument above give the original bound restricted to a set of lower limiting proportion at least $13/20$ among the positive-height nontrivial zeros. Both sums are uniform in the finite selection, the circle samples and the entire ambient Gram block. The pointwise and finite-sum implications are formalized. The density input uses the external results cited above. The unrestricted sum with the manuscript's weights remains open. [Finite-sum theorems](StripSimpleGram.lean)

## Uniform reduction to a shrinking disk

For $L=\log(2+|\Im\rho|)\ge2$, put $r_0=L^{-2}$ and define $J_\rho(r)=\sum_{0<|\nu-\rho|<r}m_\nu\log(r/|\nu-\rho|)$. Suppose the multiplicity count of other zeros inside distance $r$ is at most $C(rL+L/\log L)$ for $r_0\le r\le1/4$. Integrating over these radii gives
$$
J_\rho(1/4)\le J_\rho(r_0)+(9/4)CL .
$$

The count follows under RH from the Riemann–von Mangoldt formula and the bound for $S(t)$. The mean of $\log|\zeta|$ on the quarter-circle is at least $-BL$ unconditionally by the fixed-window form of Titchmarsh 9.6(B). In that formula one can take all zeros with $|\Im\nu-\Im\rho|\le 2$, since changing the height window only changes $O(L)$ bounded logarithms. The circle mean of each $\log|z-\nu|$ is at least $-\log 4$, including when $\nu$ lies on the circle. [Carneiro–Chandee–Milinovich, Theorem 1](https://arxiv.org/abs/1309.1526) · [Lean reduction](StripZetaClustering.lean)

The Lean proof uses Jensen's exact identity at the center with its full multiplicity. If $J_\rho(r_0)\le EL$, it yields $\log|a_\rho|\ge-(B+9C/4+E)L$. In particular, if at most $M$ units of neighboring multiplicity occur in the tiny disk and each neighbor is at distance at least $T^{-K}$, one can take $E=MK$, with $T=2+|\Im\rho|$. An empty tiny disk gives $E=0$. If this cost bound holds at all sufficiently high zeros, finite compactness absorbs the lower heights and supplies exactly the coefficient hypothesis of the rational Gram theorem. The uniform tiny-cost bound is open.

## Sufficiency: interpolants for all derivative orders

Assume (1), hence (2). Put $P(u)=(u-1)\zeta(u)$ with its removable value $P(1)=1$, $m=m_\rho$, $v=u-\rho$ and $g_\rho(u)=P(u)/v^m$, with its removable value filled in. Let

$$
r=\tfrac14\min(1,\operatorname{dist}(\rho,\{\nu:\nu\ne\rho\})),
$$

where the set consists of the other distinct nontrivial zeros. Then $r^{-m}\le T_\rho^{O(1)}$. Indeed, when a nearest neighbour $\nu$ is closer than $R$, the sum (2) **at $\nu$** contains $m_\rho\log(R/|\nu-\rho|)$. The change of scale and the other case cost $O(m_\rho)=O(\log T_\rho)$. This use of the neighbour's estimate accounts for the multiplicity at the interpolation site itself.

The Lean proof gives an explicit radius without choosing a nearest neighbor. Suppose $|\Im\rho|\ge 2$, $M$ bounds $|P|$ on $|u-\rho|=2$, and $B>0$ bounds the first nonzero normalized zeta coefficient from below at each zero in $|u-\rho|\le 1$. Removing the pole multiplies that coefficient by $u-1$, whose modulus is at least one throughout the disk. Cauchy's inequality at the center gives $B\,2^m\le M$. At a different zero $\nu$ of order $n$, the two-zero estimate gives

$$
B\le \left|\frac{P^{(n)}(\nu)}{n!}\right|\le M\left(\frac{|\nu-\rho|}{2}\right)^m.
$$

Consequently $r=(B/M)^{1/m}$ satisfies $2r\le1$, the open disk $|u-\rho|<2r$ contains no other zero, and $r^{-m}=M/B$. The fourth-order Euler–Maclaurin formula gives $|P(u)|\le C(8+|\Im u|)^5$ on $-2\le\Re u\le3$ unconditionally. For a coefficient bound $b(2+|\Im\nu|)^{-A}$ one may therefore choose $r$ with $r^{-m}=(C/b)(10+|\Im\rho|)^{A+5}$. The constants are uniform in $\rho$, $m$, and the damping degree. [Radius and pole-removal proofs](StripZetaRadius.lean) · [Vertical growth and polynomial isolation](StripZetaGrowth.lean)

On the unit disk about $\rho$, $|g_\rho|\le T_\rho^{O(1)}$ by the maximum principle on its circumference and polynomial growth of $P$ on a fixed vertical strip. On the disk of radius $2r$, $g_\rho$ is zero-free at large height. At the center, (1) gives $|g_\rho(\rho)|^{-1}\le T_\rho^{O(1)}$. Harnack's inequality for the positive harmonic function $\log(M/|g_\rho|)$, with $M$ a polynomial upper bound chosen strictly above the supremum, gives $\sup_{|v|\le r}|1/g_\rho(\rho+v)|\le T_\rho^{O(1)}$.

Choose a fixed large integer $L$ and let $q_\rho(u)=(1+v/4)^{-L}$. For $0\le k<m$, use the principal part at $\rho$ to define

$$
H_{\rho,k}(u)=P(u)q_\rho(u)\,
\operatorname{PP}_{u=\rho}\!\left(\frac{v^k}{k!\,P(u)q_\rho(u)}\right).
\tag{3}
$$

The principal part is a finite sum of $v^{-1},\ldots,v^{-(m-k)}$. Its coefficients are bounded by $T_\rho^{O(1)}/k!$ by Cauchy's formula on $|v|=r$ and the bound on $r^{-m}$. The constants and exponents here are independent of $k$ and $\rho$. At $\rho$, (3) equals $v^k/k!+O(v^m)$. At every other zero $\nu$, the factor $P$ gives all $m_\nu$ required vanishings.

More explicitly, in centered coordinates write $F(v)=P(\rho+v)q_\rho(\rho+v)$ and $a_m=F^{(m)}(0)/m!$. Suppose $0<2r\le1$, the punctured disk of radius $2r$ is free of zeros of $F$, and $U$ bounds $|F|$ on the unit circle with $U>|a_m|$. Then for $|v|\ge1$ in the domain of $F$, the Lean theorem [`exists_cardinal_interpolant`](StripJetInterpolation.lean) gives all the prescribed jets and

$$
|H_{\rho,k}(\rho+v)|\le\frac{m-k}{k!}\,\frac{U^2}{|a_m|^3 r^m}\,|F(v)|.
$$

The half-radius estimate used here is $|1/g(v)|\le U^2/|g(0)|^3$ for $g(v)=F(v)/v^m$ and $|v|\le r$. It follows by applying Borel–Carathéodory to a holomorphic function with real part $\log|g|$ and subtracting its value at zero.

Degree $L=7$ suffices in (3). For $-1\le\Re u\le2$ and $0\le\Re\rho\le1$, the fifth-power growth bound and $1+|\Im(u-\rho)|\le 8|1+(u-\rho)/4|$ yield
$$
|P(u)q_\rho(u)|\le C\,(8+|\Im\rho|)^5/(1+(\Im(u-\rho))^2).
$$
On the boundary lines $\Re u=-1,2$ one has $|u-\rho|\ge1$, so the exterior estimate for (3) preserves this translated decay with a polynomial height factor divided by $k!$. Both estimates are proved on the fork. [Damped strip envelope](StripZetaGrowth.lean) · [Interpolation estimate](StripJetInterpolation.lean)

The apparent pole at $\rho$ is removable, and the pole of $q_\rho$ is outside the enlarged strip. The radial estimate can be proved directly by absolute Mellin inversion. Set $z=u-1/2$ and $a=\rho-1/2$. Suppose the interpolant on the two lines $\Re z=\pm 3/2$ is bounded by $K/(1+(\Im z-\Im a)^2)$. Each line has absolute integral at most $\pi K$, independent of the height of the zero. Shift the inverse contour to the right line for $x\ge0$ and the left line for $x<0$. With the inverse normalization $1/(2\pi)$, the resulting continuous representative satisfies

$$
|p(x)|\le (K/2)e^{-3|x|/2},\qquad
\|p\|_{L^2(e^{2|x|}(1+x^2)^{s/2}\,dx)}^2
\le \frac{K^2}{4}\int_{\mathbf R}(1+x^2)^{s/2}e^{-|x|}\,dx.
$$

The last integral is finite for every real $s$. The Mellin integral $\int_{\mathbf R} e^{zx}p(x)\,dx$ converges absolutely and recovers the interpolant throughout $|\Re z|<3/2$, hence recovers its prescribed derivatives and vanishing orders. The [combined Lean theorem](StripRadialRealization.lean) starts from the damped divisor itself: if its exterior bound is $C/(1+(\Im z-\Im a)^2)$ on the enlarged strip at $|z-a|\ge1$, it gives this conclusion with $K=C(m-k)U^2/(k!\,|a_m|^3r^m)$. The auxiliary decay bound used to justify the contour shift may depend on the values inside the unit disk; it does not enter the norm estimate.

For the rational chart with trivial representative, the functional equation and zero-free right half-plane put each admitted site strictly inside the critical strip. There the completed Hecke order agrees with the analytic order of ordinary zeta. The [physical witness theorem](StripRationalChart.lean) combines this identification with the Haar-normalized lift. Its norm carries the same inverse factorial as the radial estimate, and its Kronecker pairing includes low jets and the other angular characters.

For the finite Gram estimate write $H=10+|\Im\rho|$. At a real offset $|b|\le 1/2$ the squared jet norm is bounded by a fixed Haar scalar times
$$
\int_{\mathbf R}|x|^{2k} e^{-|x|}\,dx=2(2k)!\le 2(2^k k!)^2.
$$
The physical witness bound cancels $k!$. At height at least two, $2^k\le 2^m\le r^{-m}\ll H^{A+5}$, so $\|u_i\|\sqrt{\operatorname{Re}(G_S^{-1})_{ii}}\ll H^{6A+30}$ uniformly in the finite block $S$. For the finitely many lower jets the existing individual interpolants give a single constant for a fixed basepoint choice. The finite block may contain jets on any angular component. [Finite Gram estimate](StripGramEstimate.lean) · [Upstream Gram comparison](https://github.com/mccorvie/riemann-masullo/pull/7484)

The [weighted finite-sum theorem](StripRationalTrace.lean) uses the circle of radius $2\exp((4+s)/2)$ prescribed in §10.3.2. On these circles the Mellin transform of a compact Bruhat test has a uniform bound of order $H^{-6A-32}$. Multiplying by the coordinate bound and summing the retained orders costs at most a constant times $m_\rho/(1+|\Im\rho|)^2$ per site. The project's quadratic zero-count estimate sums this last weight. This proves the implication from (1) to the rational trivial-component finite Gram inequality for every $s\ge0$, with one constant for all finite sets and all circle samples. The general Hecke case and an unconditional bound for the first coefficient remain open.

The quotient class has exactly the prescribed derivative evaluations. Totality of the dual jets identifies it with $x_{\rho,k}$, up to the fixed normalization of radial Haar measure. Conversely, the uniform point-evaluation upper bound on the disks of radius $1/4$ and Cauchy's inequality give $\|\Lambda_{\rho,k}\|\ll 4^k k!$. The factorials cancel, and $4^k\le T_\rho^{O(1)}$ since $k<m_\rho=O(\log T_\rho)$. This proves the coordinate-product estimate from (1) and completes the equivalence.

For simple zeros, (1) becomes a polynomial lower bound for $|\zeta'(\rho)|$. In that case any polynomial upper bound for the discrete negative second moment $\sum_{0<\Im\rho\le T}|\zeta'(\rho)|^{-2}$ suffices. The Gonek–Hejhal prediction is much sharper. The general criterion above also covers a zero at which the first derivative vanishes. [Ng, discussion of the discrete negative moments](https://www.cs.uleth.ca/~nathanng/RESEARCH/mobius2b.pdf)

## Checking the Lean results

From the root of the fork, build the imported project modules and check the research files in dependency order.

```sh
lake build $(awk '$1 == "import" && $2 !~ /^research[.]/ {print $2}' research/Strip*.lean | sort -u)
research_out=.lake/build/lib/lean/research
mkdir -p "$research_out"
for name in StripJetInterpolation StripRadialRealization StripPhysicalPairing StripZetaRadius StripZetaGrowth StripZetaCardinal StripRationalChart StripGramEstimate StripRationalTrace StripZetaClustering StripZetaIsolated StripSimpleGram
do
  lake env lean -DmaxSynthPendingDepth=3 -DautoImplicit=false -DrelaxedAutoImplicit=false -DwarningAsError=true -o "$research_out/$name.olean" "research/$name.lean" || exit 1
done
```

The fourth-order block estimate adapts Thomas Lince’s corrected trapezoid proof. [Project attribution](../RiemannMasullo/External/ATTRIBUTION.md)

Prepared with Codex assistance.
