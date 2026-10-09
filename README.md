# Infinitely Many Closed Geodesic Images on Reversible Finsler Spheres

The closed-geodesic problem for reversible Finsler spheres asks for the following assertion.

> [!NOTE]
> **Theorem (Infinitely many closed geodesic images).**
>
> For every integer $n\ge 3$, every smooth, strongly convex, reversible Finsler metric on the standard sphere $S^n$ has infinitely many geometrically distinct prime closed geodesics.

Smoothness is required off the zero section. Geometric distinctness means distinct images in $S^n$; iteration, a change of starting point, and reversal do not produce additional images. No curvature or nondegeneracy assumption is imposed.

This repository presents a proposed proof of this assertion for submission to **Formal Conjectures**. A proof sketch follows; the [PDF manuscript](PDF/reversible-finsler-spheres.pdf) contains the detailed proof.

## Proof sketch

### 1. Obtain one filling bound for every degree

Let $\Lambda=H^1(S^1,S^n)$, let $M$ be the constant loops, and set

$$
E_F(\gamma)=\int_0^1F(\gamma(t),\dot\gamma(t))^2\,dt,
\qquad X_a=\{\sqrt{E_F}<a\}.
$$

All homology and cohomology groups have coefficients in $\mathbb F_2$. The first target is a constant $D>0$, independent of both the degree $q$ and the cut $a$, such that

$$
\ker\bigl(H_q(X_a,M)\to H_q(\Lambda,M)\bigr)
=\ker\bigl(H_q(X_a,M)\to H_q(X_{a+D},M)\bigr).
$$

Arclength normalization preserves length and does not increase energy. Strong convexity supplies continuity in the strong $H^1$ topology, including loops with stationary intervals. Shortening finite-dimensional families first gives filling bounds in each fixed degree.

A cut operation lowers an arbitrary high degree to one of finitely many low degrees. Joining back with a sphere-product class restores the removed length up to a fixed additive constant. For a globally null cycle $x$, the filling is the four-term chain

$$
B_x=\mu(W,S)+\mu(V,x)+H+U_0,
\qquad \partial B_x=x.
$$

Here $W$ fills the cut of $x$, $V$ corrects the cut of $S$ to the constant-loop unit, and $H,U_0$ are the interchange and unit homotopies. The length bounds are fixed before the small joining rotations are chosen, giving a common additive filling constant.

### 2. Locate the reflection-equivariant classes

Let $R=C_2$ act by reversal, and write

$$
A_a^q=H^q(X_a,M),\qquad B_a^q=H_R^q(X_a,M).
$$

The global reflection group has a basis

$$
\{w^kX_m,\;ew^kX_m:m\ge1,\ 0\le k\le n-1\},
\qquad |X_m|=(2m-1)(n-1),
$$

where $|w|=1$, $e$ is the degree-$n$ evaluation class, and $w^nB_\infty=0$.

The filling bound identifies the image of $A_{a+D}^q\to A_a^q$ with the global ordinary image. In the natural Gysin sequence, a transfer correction then gives the kernel descent

$$
K_{a+D}^q\subset wK_a^{q-1},
\qquad K_a^q=\ker(B_\infty^q\to B_a^q),
$$

whenever the corresponding ordinary restriction is injective. Iterating this descent and its vanishing counterpart, then using ordinary resonance, gives constants $\alpha>0$ and $\mathcal C$ such that, for $q\ge2n+1$,

$$
B_\infty^q\to B_a^q
\quad\text{is}\quad
\begin{cases}
\text{injective},&q<\alpha a-\mathcal C,\\
\text{zero},&q>\alpha a+\mathcal C.
\end{cases}
$$

### 3. Bound the classes that do not come from the full loop space

Assume that there are only finitely many prime geodesic images. Their iterates have uniformly bounded local total ranks and uniformly bounded index-support widths. Finite polygon models and one common descending flow retain the actual restriction and connecting maps, including at degenerate critical levels.

Compare the cut $2a$ with its half-translation fixed locus, identified with $X_a$. For each degree cutoff, retain two successive low-degree image deficits, the image above the cutoff, and the restriction kernel. Their sum $\Phi_j(a)$ satisfies

$$
\sum_{j\ge1}\Phi_j(a)\le C(1+a).
$$

Away from local index windows, exactness makes this four-term quantity nonincreasing at a crossing. Inside the windows, the uniform local ranks bound its increase.

A nonzero extra class in a long degree gap propagates through a long string of powers of $w$. Its actual ambient lifts would contribute quadratically in $a$ to the displayed sum, contradicting the linear bound. The remaining bounded-width bands are controlled by local ranks and the filling bound. Consequently

$$
T(a)=\sum_q\dim\operatorname{coker}(B_\infty^q\to B_a^q)
$$

is bounded independently of the regular cut $a$.

### 4. Compare a cut with its double

The $O(2)$-equivariant group at a finite cut is a finitely generated module over $\mathbb F_2[U]$, where $|U|=2$. Its free rank is the total reflection rank at the half cut. If $t$ is the number of torsion generators, the Gysin sequences give

$$
\dim B_{2a}^*=\dim B_a^*+2t.
$$

Odd-stage bottom classes have global $U$-torsion lifts; even-stage bottoms and their evaluation-cup partners have global lifts as well. Counting their actual images gives

$$
T(2a)\ge T(a).
$$

Equality requires every visible odd-stage bottom to have a visible evaluation-cup partner, independent modulo the bottom images in its degree.

### 5. Use the first appearance of an odd bottom

Choose a regular interval $I$ on which the bounded integer $T$ attains its maximum. Doubling forces the same maximum at every regular point of $2^kI$. Hence the equality condition holds throughout those expanded intervals for $k\ge1$.

The odd bottom degrees form the progression

$$
(4r+1)(n-1),\qquad r\ge0.
$$

For sufficiently large $k$, the detection bounds provide an odd bottom $\xi$ that is zero near the lower end of $2^kI$ and nonzero near its upper end. At its first nonzero crossing, exactness makes $\xi$ come from the local relative group.

Choose a point outside the finite union of prime geodesic images. The local neighborhoods evaluate into the punctured sphere, so cup product with $e$ vanishes on the crossing. Immediately after it,

$$
\xi\ne0,\qquad e\xi=0.
$$

This contradicts the doubling equality condition. Therefore the set of prime closed geodesic images is infinite.

## Detailed manuscript

- [PDF manuscript](PDF/reversible-finsler-spheres.pdf)

Public draft 1, 9 October 2026.
