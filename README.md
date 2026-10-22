# Closed geodesics on spheres: OpenAI's theorem and reversible Finsler variants

[![Exact FC target and Comparator](https://github.com/KitaKen1/reversible-finsler-spheres/actions/workflows/fc-target.yml/badge.svg?branch=main)](https://github.com/KitaKen1/reversible-finsler-spheres/actions/workflows/fc-target.yml)

OpenAI proves the following sphere case of the closed-geodesic infinitude
problem in [Infinitely many closed geodesic images on every Riemannian sphere
(24 September 2026)](https://github.com/openai/math/blob/main/preprints/Infinitely-many-closed-geodesic-images-on-every-Riemannian-sphere-September-24-2026/paper.pdf),
catalogue entry 345 [OAI26].

> **Statement 1 — OpenAI's Riemannian sphere theorem.** For every integer
> $n \ge 2$, every smooth Riemannian metric on the standard sphere $S^n$ has
> infinitely many geometrically distinct prime closed geodesics.

This repository claims Statement 2 below as a natural generalization of
Statement 1 to reversible Finsler metrics for all $n \ge 2$. Statement 2 implies
Statement 1, since Riemannian metrics are a special case of reversible Finsler
metrics.

> **Statement 2 — Reversible Finsler variant, all dimensions at least two.**
> For every integer $n \ge 2$, every smooth, strongly convex, reversible
> Finsler metric on the standard sphere $S^n$ has infinitely many
> geometrically distinct prime closed geodesics.

For $n = 2$, this was proved by
[De Philippis, Marini, Mazzucchelli and Suhr (2022)](https://arxiv.org/abs/2002.00415)
[DPMMS22]. For $n \ge 3$, this repository provides a
[Lean proof](lean/FCExactSolution.lean). Together, these two cases give Statement 2
for all $n \ge 2$. The table compares the hypotheses, conclusion and proof
coverage of the two statements side by side.

| Aspect | Statement 1 — OpenAI | Statement 2 — This repository |
| --- | --- | --- |
| Underlying space | Standard sphere $S^n$ | Standard sphere $S^n$ |
| Dimension | $n \ge 2$ | $n \ge 2$ |
| Metric | Smooth Riemannian metric | Smooth, strongly convex Finsler metric |
| Squared norm on each tangent space | Quadratic: $F(x,v)^2 = g_x(v,v)$ | May be nonquadratic |
| Reversibility, $F(x,-v)=F(x,v)$ | Automatic | Required |
| Curvature, bumpiness or nondegeneracy assumptions | None | None |
| Conclusion | Infinitely many geometrically distinct prime closed geodesics | Infinitely many geometrically distinct prime closed geodesics |
| Proof supplied or cited | OpenAI paper [OAI26] for $n \ge 2$ | $n = 2$: [DPMMS22]; $n \ge 3$: this repository |
| Local Lean proof | FC statement only | $n \ge 3$: [FCExactSolution.lean](lean/FCExactSolution.lean); $n = 2$: FC statement only |

The two main contributions are:

1. **Formal Conjectures style statements.**
   [FClikelean/](FClikelean/) contains the definitions and four theorem
   statements: Statements 1 and 2, and the $n = 2$ and $n \ge 3$ reversible
   Finsler specializations.
2. **The full Lean proof for $n \ge 3$.**
   [FillRel.lean](lean/Finsler/Residual/FillRel.lean) proves the final sphere
   infinitude theorems. [FCExactSolution.lean](lean/FCExactSolution.lean) proves
   the exact mathematical $n \ge 3$ target from the single-file FC submission.

## Formal Conjectures like targets

### FClikelean

The submission is one file,
[ReversibleFinslerSpheres.lean](FClikelean/ReversibleFinslerSpheres.lean), with
three definitions, one metric structure and two type abbreviations. It uses
FC's standard `public import FormalConjecturesUtil`; no project-specific helper
module or copied utility implementation is part of the submission.

The four statements are OpenAI's Riemannian result, the all-dimensional
reversible Finsler variant, the n = 2 literature theorem, and the n ≥ 3 variant.
All carry the official `@[category research solved, AMS 53]` metadata and
intentional `sorry` bodies. The separate Lean proof covers n ≥ 3.
**The n = 2 case is supplied by [DPMMS22] and is outside the local Lean proof
scope.** No all-dimensional Lean proof or literature axiom is claimed.

[FCImplications.lean](lean/FCImplications.lean) proves that the Finsler statement
implies the Riemannian statement and that the n ≥ 3 proof combines with an
explicit n = 2 hypothesis. The independent
[correspondence proof](verification/FCDefinitionCorrespondence.lean) identifies
the compact variational definitions with the proof target's Euler–Lagrange
image set. The earlier partial two-sphere work is retained as
[historical research](verification/DIMENSION-TWO.md).

The Riemannian statement adds `IsRiemannian F`: on each actual tangent fiber,
$F(x,v)^2=g_x(v,v)$ for a symmetric positive-definite bilinear form $g_x$.
For all four statements, Finsler smoothness is required off the zero section,
strong convexity means that the fiberwise Hessian of $\tfrac12 F^2$ is positive
definite there, and reversibility means $F(x,-v)=F(x,v)$.

Geometric distinctness means **different images in the sphere**. Iteration,
a change of starting point and reversal contribute no new image. Prime
geodesics have least positive period one, without a prescribed length or speed.
The [formal problem](PROBLEM.md) records these conventions; the
[FC guide](FClikelean/README.md) lists the four declarations.
The independent FC draft has not been accepted upstream by Formal Conjectures.
The FC check targets Lean `v4.33.1`; the separate proof and correspondence
checks use `v4.35.0-rc3`. See the [FC guide](FClikelean/README.md).

### Comparator target

[FCExactChallenge.lean](lean/FCExactChallenge.lean) copies the mathematical
definitions and the complete $n \ge 3$ theorem type from the standalone FC
submission. [FCExactSolution.lean](lean/FCExactSolution.lean) proves that same
target, `ReversibleFinslerSpheres.infinitely_many_prime_closed_geodesics`.
[The generator](scripts/generate-fc-target.py) checks the extraction against
the canonical FC source. Only metadata imports/attributes and the other three theorem statements are
omitted. The module system and public visibility are retained. The definitions,
metric conditions, stationarity condition and conclusion are unchanged.
The reference has one intentional placeholder; the solution imports neither
that reference nor any of the FC placeholder theorems.
[comparator-fc.json](lean/comparator-fc.json) selects this exact target, and
[FCExactAudit.lean](lean/FCExactAudit.lean) rejects every transitive axiom except
`propext`, `Classical.choice` and `Quot.sound`.
See [verification status](verification/STATUS.md) for measured results and scope.

The earlier coordinate formulation is also retained:
[Challenge.lean](lean/Challenge.lean) supplies two reference statements, and
[FCSolution.lean](lean/FCSolution.lean) proves them. The primary target is
[`ReversibleFinslerSphereFC.infinitely_many_prime_closed_geodesics`](lean/FCSolution.lean).
It covers the $n \ge 3$ case of Statement 2 (FC Statement 4), counting images
of regular smooth prime solutions of the coordinate Euler–Lagrange equation.
The auxiliary theorem `ReversibleFinslerSphereFC.variational_form` gives the
equivalent energy-stationary formulation.

Both are derived from the final project theorems in
[`Finsler/Residual/FillRel.lean`](lean/Finsler/Residual/FillRel.lean):
`Finsler.UFFillRel.ordinary_sphere_assertion` and
`Finsler.UFFillRel.reversible_sphere_assertion`.
Their complete statements quantify over every metric; there is no outstanding
filling, resonance or finite-geodesic hypothesis in the exported targets.
The [statement correspondence](verification/STATEMENT-CORRESPONDENCE.md)
matches the natural-language clauses with the formal definitions and targets.

## Mathematical explanation (AI generated)

Here is a proof sketch of the $n \ge 3$ reversible Finsler case, with links to
the main lemmas. Fix a metric $F$, put $m=n-1\ge2$, and work over
$\mathbb F_2$. Let $\Lambda=H^1(S^1,S^n)$ and identify $M=S^n$ with the constant
loops. Write

```math
E_F(\gamma)=\int_0^1 F(\gamma,\dot\gamma)^2\,dt,
\qquad X_a=\{\gamma:\sqrt{E_F(\gamma)}\lt a\},
\qquad L_a=\{\gamma:\mathrm{length}_F(\gamma)\lt a\}.
```

We use positive levels, so $M\subset X_a$. Reversibility makes loop reversal
$R\gamma(t)=\gamma(-t)$ an involution of these pairs. Suppose, for a
contradiction, that there are only finitely many prime geodesic images. Every
nonconstant critical loop is an iterate of one of them. Consequently, the
critical lengths form a locally finite set with at most $O(a)$ elements below
$a$. We use a set $\mathcal C$ of critical levels closed under doubling;
a *regular cut* is a positive number outside $\mathcal C$.

**1. Obtain a common spectral rate with bounded error.** The loop-space
construction supplies indexed homology and Goresky–Hingston cohomology towers

```math
\Theta_r\in H_{n+2(r+1)m}(\Lambda),
\qquad \eta_r\in H^{(2r+1)m}(\Lambda),\qquad r\ge0.
```

Let $\tau_r$ be the infimum of the length levels carrying $\Theta_r$, and let
$\ell_r$ be the supremum of the levels on which $\eta_r$ restricts to zero.
The product and cutting identities give a common positive rate $\beta$, with
$\ell_r/(r+1)\to\beta$, $\ell_r\le(r+1)\beta$ and the fixed-shift estimate
$\ell_r\le\tau_r\le\ell_{r+1}$. In particular, $\tau_r\le(r+2)\beta$.

The finiteness assumption improves this asymptotic statement to a uniform
error bound. Local index estimates give a finite set of slopes $S$ and a
constant $A$ such that, for some $s_r\in S$,

```math
\big|(2r+1)m-s_r\ell_r\big|\le A.
```

Dividing by $\ell_r$ shows $s_r\to\alpha:=2m/\beta$. A convergent sequence in
a finite set is eventually constant. Enlarging a constant to cover the first
finitely many terms therefore gives

```math
(r+1)\beta-C\le\ell_r\le\tau_r\le(r+2)\beta,
\qquad 0\le\tau_r-\ell_r\le\beta+C.
```

This bounded difference is what makes the later length loss independent of
the power $r$. See [GHSlope.lean](lean/Finsler/Residual/GHSlope.lean), especially
`SlopeRate.exact_rate` and `GHSlope.gh_exact_rate`, and
[NativeThetaGHCommonRate.lean](lean/Finsler/Loop/NativeThetaGHCommonRate.lean).

**2. Turn the high-power unit identity into uniform filling.** Choose a
cocycle representing $\eta_r$ that vanishes below $L_r=\ell_r-\tfrac12$,
and a lift $S_r$ of $\Theta_r$ carried below $s_r=\tau_r+\tfrac12$.
For a fixed positive slack $\varepsilon$, the associated cutting operation
$c_r$ lowers degree by $2(r+1)m$ and takes length $a$ to at most
$a-L_r+3\varepsilon$. The high-power unit identity identifies the global
image of $c_r(S_r)$ with the constant-loop fundamental class
$1=[M]\in H_n(\Lambda)$.

Moreover, $s_r-L_r\le\beta+C+1$. Thus all these cut classes lie in a single
bounded sublevel. Finite-dimensionality at a regular bounded sublevel lets
one choose a single larger level $B_*$ where every $c_r(S_r)$ agrees with
the filtered unit. This supplies a unit identity at a level independent of $r$.

If a class $x\in H_q(L_a)$ dies in $H_q(\Lambda)$, its cut also dies globally.
In high degrees, choose the power so that either its remaining length is
bounded or its remaining degree lies in a fixed finite window. Bounded-level
filling and the local crossing estimates then kill the cut with uniform cost.
The filtered cut–join identity gives, after mapping all terms to a common
sublevel,

```math
x=1*x=(c_rS_r)*x=(c_rx)*S_r=0.
```

Here $*$ is the loop product, of degree $-n$. For low degrees, first multiply
by a sufficiently high $S_r$, apply the high-degree result, and use the
filtered product–cut identity to recover $x$. The result is a constant
$D\ge0$, independent of $a$, $q$ and $x$, such that

```math
x\in\ker\big(H_q(L_a)\longrightarrow H_q(\Lambda)\big)
\quad\Longrightarrow\quad
x\longmapsto0\text{ in }H_q(L_{a+D}).
```

The filtered unit construction is in
[UFData.lean](lean/Finsler/Residual/UFData.lean); the displayed four-term
identity is `UFCore.kill` in [UFCore.lean](lean/Finsler/Residual/UFCore.lean).
[UFHigh.lean](lean/Finsler/Residual/UFHigh.lean) handles the two high-degree
cases, and `UFLow.uf_all` in [UFLow.lean](lean/Finsler/Residual/UFLow.lean)
extends the bound to every degree.

**3. Pass to relative cohomology and establish resonance bands.** The
length–energy comparison transfers uniform filling to $X_a$. Over a field,
the image of a dual linear map is the annihilator of its kernel. Hence a
cohomology class on $X_b$, with $b\ge a+D$, restricts on $X_a$ to a global
class. To obtain the relative version, use the retraction
$X_a\to M$, $\gamma\mapsto\gamma(0)$. The long exact sequence of the pair
then makes $H^q(X_a,M)\to H^q(X_a)$ injective. A global absolute lift of a
relative class vanishes on $M$, so it lifts to $H^q(\Lambda,M)$; injectivity
identifies its restriction with the desired relative class. Thus, for large
enough $a$ and $b\ge a+D$,

```math
\mathrm{im}\big(H^q(X_b,M)\to H^q(X_a,M)\big)
=\mathrm{im}\big(H^q(\Lambda,M)\to H^q(X_a,M)\big).
```

The spectral estimates also apply to the finitely many residue families
generating ordinary loop-space cohomology. GH multiplication supplies the
vanishing bound; products with near-optimal $\Theta$ representatives supply
dual homology classes for the nonvanishing bound. Consequently, for constants
$c_1,a_0$ and all $a\ge a_0$, ordinary restriction
$r_a^q:H^q(\Lambda,M)\to H^q(X_a,M)$ satisfies

```math
\begin{aligned}
c_1\lt q\lt \alpha a-c_1&\quad\Longrightarrow\quad r_a^q\text{ is injective},\\
q\gt \alpha a+c_1&\quad\Longrightarrow\quad r_a^q=0.
\end{aligned}
```

These are the precise filling and resonance hypotheses assembled in
[FillRel.lean](lean/Finsler/Residual/FillRel.lean). The duality argument is in
[FillAbs.lean](lean/Finsler/Residual/FillAbs.lean), and the full ordinary
resonance estimate is in [FullHRAbs.lean](lean/Finsler/Residual/FullHRAbs.lean)
and [HRBridge.lean](lean/Finsler/Residual/HRBridge.lean).

**4. Compute the reflection classes and locate their detection windows.** Put
$B^q=H_R^q(\Lambda,M)$ and $B_a^q=H_R^q(X_a,M)$, where $H_R$ denotes Borel
cohomology for reversal, and let $\rho_a^q:B^q\to B_a^q$ be restriction.
Let $w\in H^1(B\mathbb Z_2;\mathbb F_2)$ be the equivariant parameter, and
let $e=\mathrm{ev}_0^*[S^n]^*$ be the degree-$n$ evaluation class.

The round-sphere computation, which determines the topology of the full loop
space independently of $F$, gives $w^nB^*=0$ and spanning bottom and top
classes $b_q,t_q$ in each degree. For a distinguished set $\mathcal O$ of
odd-stage bottom degrees,

```math
t_{q+n}=e\smile b_q\quad(q\in\mathcal O),
\qquad q_j=(4j+1)(n-1)\in\mathcal O,
\qquad b_{q_j}\ne0.
```

The stage label is odd; the integer $q_j$ need not be odd. Every bottom class,
and every top class outside the displayed pairing, lifts to the equivariant
cohomology for reversal and half-period translation. The odd-stage bottom
lifts are annihilated by a fixed power of $U=v(v+w)$,
where $v$ is the parameter for the second involution. These lift properties
will enter the doubling count.

The Gysin sequence, uniform relative filling and $w$-nilpotence transfer the
ordinary resonance bands to the reflection groups. After enlarging the margin,
there are $C'\gt 0$ and $q_0$ such that, for $q\ge q_0$ and $a\gt 0$,

```math
q\lt \alpha a-C'\ \Longrightarrow\ \rho_a^q\text{ is injective},
\qquad
q\gt \alpha a+C'\ \Longrightarrow\ \rho_a^q=0.
```

See `RoundYTop.stage13` and `RoundYTop.basis_w_nil` in
[RoundYTop.lean](lean/Finsler/Geometry/RoundYTop.lean), and
[GlobalDetection.lean](lean/Finsler/Topology/GlobalDetection.lean).

**5. Bound the classes at a cut that do not extend globally.** At a regular
cut define the nonnegative integer

```math
T(a)=\sum_q\dim_{\mathbb F_2}\mathrm{coker}(\rho_a^q).
```

The sum is finite. Local index estimates confine changes in ordinary
cohomology to fixed-width bands around finitely many lines $q=sa$.
Filling and the Gysin sequence imply that, away from these bands, either
$B_a^q=0$ or multiplication by $w$ is bijective on the cokernels throughout
a degree interval $[g_0,g_0+14t]$ with $t\ge\delta a$, for a fixed $\delta\gt 0$.

A nonzero cokernel class in such an interval would therefore generate a long
nonzero $w$-string. The rank-counting lemma for this string gives

```math
2t^2\le K_0N_F(2a),\qquad N_F(2a)\le K_1(1+2a),
```

where $N_F(2a)$ counts critical levels up to $2a$ and $K_0,K_1$ are independent
of $a,t$. The first inequality comes from summing the changes of the
equivariant rank counts across critical levels: each crossing affects only
boundedly many degree cutoffs and contributes a bounded amount. Its detailed
form is `GapBound.gap_bound` in [GapBound.lean](lean/Finsler/Topology/GapBound.lean).
Since $t\ge\delta a$, its quadratic left side exceeds its linear right side
for large $a$. Thus the cokernels vanish outside the fixed-width bands.

There are uniformly boundedly many band degrees, and the local crossing
rank estimates bound each remaining cokernel. It follows that $T(a)\le B$
for a constant $B$. Curve shortening makes $T$ constant between critical
levels; local finiteness extends the bound to all positive regular cuts.
See [ComparisonRank.lean](lean/Finsler/Topology/ComparisonRank.lean) and
[DefectBound.lean](lean/Finsler/Topology/DefectBound.lean).

**6. Use doubling to force evaluation-cup partners.** For $q\in\mathcal O$,
let $\varepsilon_q(a)$ be $1$ when $\rho_a^q(b_q)\ne0$, and $0$ otherwise.
Let $p_q(a)$ be $1$ when $\rho_a^{q+n}(t_{q+n})$ is independent of the
restricted bottom class in degree $q+n$, and $0$ otherwise. The identity
$t_{q+n}=e\smile b_q$ gives $0\le p_q(a)\le\varepsilon_q(a)$.

Half-period translation fixes the doubled loops: its fixed set in $X_a$
identifies with $X_{a/2}$. The Gysin rank identities for this action, together
with the global lifts and their $U$-torsion, give the doubling inequality

```math
T(a)-T(a/2)\ \ge\!
\sum_{q\in\mathcal O}\big(\varepsilon_q(a)-p_q(a)\big)\ \ge0
```

at every regular cut $a$; only finitely many summands are nonzero.
In particular, equality $T(a)=T(a/2)$ forces
$p_q(a)=\varepsilon_q(a)$ for every label. Every visible odd-stage bottom
then has an independent, and hence nonzero, evaluation-cup partner.
The geometric rank identities are assembled in
[DoublingBudget.lean](lean/Finsler/Topology/DoublingBudget.lean) and
[BasisBudget.lean](lean/Finsler/Topology/BasisBudget.lean); their equality
consequence is `PartnerRank.equality_forces_partner` in
[PartnerRank.lean](lean/Finsler/Algebra/PartnerRank.lean).

**7. Force a new bottom class to appear where its partner must vanish.**
Since $T$ is bounded and integer-valued, it attains a maximum at some regular
cut. Choose a small critical-level-free interval $[u,v]$ around that cut.
Doubling monotonicity and maximality imply that $T$ stays maximal at every
regular point of $2^k[u,v]$. For $k\ge1$, therefore,
$T(x)=T(x/2)$ throughout the regular points of that interval.

The degrees $q_j=(4j+1)(n-1)$ have fixed spacing, while the width of
$2^k[u,v]$ tends to infinity. For large $k$, choose $q=q_j\ge q_0$ and regular
cuts $a\lt b$ in that interval with

```math
\alpha a+C'\lt q\lt \alpha b-C'.
```

Detection gives $\rho_a^q(b_q)=0$ and $\rho_b^q(b_q)\ne0$. There are only
finitely many critical levels between $a$ and $b$, so some single crossing
$[a',b']$ is the first at which this class appears. Exactness for the triple
$M\subset X_{a'}\subset X_{b'}$ lifts $\rho_{b'}^q(b_q)$ to a class in
$H_R^q(X_{b'},X_{a'})$.

Choose a point of $S^n$ outside the finitely many geodesic images. It has
positive distance from all of them. Curve-shortening localization represents
the single crossing near its critical loops, where evaluation avoids that
point. The sphere's top class restricts to zero on the punctured sphere, so
$e$ acts as zero on this relative crossing group. Naturality then gives

```math
e\smile\rho_{b'}^q(b_q)=0.
```

Thus $\varepsilon_q(b')=1$ but $p_q(b')=0$, contradicting the equality case
of doubling on the maximal-defect interval. This disproves finiteness of
the prime geodesic images. The crossing vanishing is
`EndgameCritical.crossE_zero_of_finite` in
[EndgameCritical.lean](lean/Finsler/Topology/EndgameCritical.lean); the
maximal-interval and first-crossing argument is
`EndgameAssembly.false_of_inputs` in
[EndgameAssembly.lean](lean/Finsler/Topology/EndgameAssembly.lean).

Finally, [FillRel.lean](lean/Finsler/Residual/FillRel.lean) assembles these
lemmas into the sphere assertion. The variational and coordinate
Euler–Lagrange formulations are equivalent by
[OrdinaryGeodesic.lean](lean/Finsler/Geometry/OrdinaryGeodesic.lean), with the
same curves, prime periods and images, yielding the stated theorem.

The [earlier manuscript](PDF/reversible-finsler-spheres.pdf), dated 9 October
2026, is retained as historical supporting material. It has not been audited
line by line against the current Lean snapshot; see [PDF/README.md](PDF/README.md).

## Files

| Directory | Lean version | Purpose |
| --- | --- | --- |
| [lean/](lean/) | `v4.35.0-rc3` | Canonical $n \ge 3$ proof, Challenge and FC implications; historical two-sphere research retained. |
| [leanWithoutComparator/](leanWithoutComparator/) | `v4.35.0-rc3` | The same proof for browsing and building without Comparator. |
| [FClikelean/](FClikelean/) | FC `v4.33.1` | One submission file, minimal definitions and four statements using the existing FC environment. |
| [lean/comparator/](lean/comparator/) | `v4.35.0-rc3` | Checker pins, comparison scripts and reproduction guide. |
| [.github/workflows/](.github/workflows/) | GitHub-hosted Linux | Prepared build, statement checks, axiom audit and Comparator workflow. |
| [verification/](verification/) | — | Local receipts, logs, source hashes and statement correspondence. |
| [PDF/](PDF/) | — | Earlier manuscript and its supplied timestamp file. |

The 2,056 shared source files in the two proof projects are byte-for-byte
identical. [proof-source-manifest.json](verification/proof-source-manifest.json)
pins the proof sources, and [PUBLICATION-MANIFEST.json](PUBLICATION-MANIFEST.json)
seals the publication files.

This is the v188 source tree with a proof-only memory reduction in
`NativeSequentialSuffixMiddle.common_eq`, recorded in the
[memory regression receipt](verification/local/native-suffix-memory-receipt.json).
The definitions and public statements are unchanged. Earlier comments in unchanged proof
files sometimes call the assertion “unproved”; those comments predate
`FillRel.lean`. The entry points and verification records describe this snapshot.

## Verification

### Lean execution results

The local checks used Lean `v4.35.0-rc3` and an existing build whose source
files match this snapshot. Both publication proof entry points, their axiom
audits and their specification checks compiled separately. These local checks
reused existing project artifacts. The separate public Linux CI built the
project from source with no restored project cache, as recorded below.

The two public targets and two final project theorems use only
`[propext, Classical.choice, Quot.sound]`, as checked by
[FCAudit.lean](lean/FCAudit.lean) in both proof variants. The source scan found
no proof placeholders or project axiom declarations outside the two intended
Challenge placeholders and four FC statement placeholders.

All four FC declarations and their genuine upstream attributes elaborated in
the cross-version correspondence check. It expands only the standard FC import
into the official attribute module and the used Mathlib modules; the mathematical
body is unchanged. The original file also passed the separate
[FC v4.33.1 check](verification/local/fc-upstream-receipt.json) using the full
standard import and matching dependency pins. The author’s original copyright
header is retained and triggers FC’s header-style warning; this is not a claim
of warning-free upstream CI. The
[FC readback](verification/FCStatementReadback.lean) checked their complete
types and read back the category and AMS tags in a search path containing only
Mathlib dependencies and FC modules. The separate
[definition correspondence](verification/FCDefinitionCorrespondence.lean) proved
metric equivalence, equality of geodesic image sets, equivalence of the assertions
and round-metric nonvacuity. Its eight transitive axiom audits passed. The separate
[implication audit](verification/FCImplicationsReadback.lean) checked the six
new specialization/implication proofs and their transitive axioms, all within
`[propext, Classical.choice, Quot.sound]`. This audit imports the proved
solution, not the FC statement file.
See the [local verification record](verification/local/receipt.json),
[four-statement receipt](verification/local/fc-four-statements-receipt.json)
and [detailed status](verification/STATUS.md).

The historical [two-sphere audit](verification/TwoSphereReadback.lean) checks
288 arithmetic, repeated-family, connector, pause-removal, explicit
filling, local-class, excision, polygon-to-loop comparison, local splitting
and maximal-disk construction, spectral coordinates, actual phase charts and
transverse Hessian splitting, actual transverse iteration and reduced-maximum
transport along stable odd progressions, actual point-critical homology injections
and the stable-base construction for zero mean index, local deformations,
iteration isomorphisms, bounded-chain-index vanishing, actual zero-mean
index vanishing and positive-index growth, original-period rotation without
changing the base geodesic, invariant local detectors and mapping-torus
fibre injections, homological extraction
and conditional geometric theorems in both proof
variants. Its [receipt](verification/local/two-sphere-receipt.json) records
the exact source hashes and compilation results. None of these declarations
imports an FC placeholder or asserts the remaining geometric construction.

### Lean Comparator check

The exact n ≥ 3 FC target passed the full
[public `main` CI run](https://github.com/KitaKen1/reversible-finsler-spheres/actions/runs/39703676590)
on **22 October 2026 at 05:30 UTC (14:30 JST)**, testing code commit
`be3aaf6949fd931d61aef749ed59207fc6ef21a6`. The run used the unmodified pinned
upstream Comparator CLI and real Linux `landrun`. Target/definition comparison,
transitive axiom checks and built-in Lean kernel replay all passed. The
[archived public log](verification/ci/39703676590/fc-target-comparator.log) reports
`Lean default kernel accepts the solution` and `Your solution is okay!`.
The [receipt](verification/ci/39703676590/receipt.json) records the tested code
commit, immutable checker pins, artifact digest and source/log hashes.
The project was built from source with no restored project cache; pinned
dependency caches were used. The source-build step took 4 h 4 min 45 s, and the
combined Comparator/post-audit step took 15 min 51 s. These are step durations,
not a kernel-only measurement. The
[earlier private sandbox result](verification/ci/39700419746/receipt.json)
is retained as historical evidence.

The current local macOS run passed all nine C-output entry compilations, both
exports and the upstream target/axiom comparison; its built-in kernel replay
reached the unchanged 600-second limit. That timeout is retained in the
[local receipt](verification/local/fc-target-comparator-receipt.json) separately
from the hosted success. The earlier wrappers' successful local replay is
preserved as historical evidence. No independent kernel implementation was run.
See [verification status](verification/STATUS.md) and the
[Comparator guide](lean/comparator/README.md) for the exact scope and commands.

The solution imports neither the reference nor the FC draft. The fixed
definitions have no holes, and `definition_names` in
[comparator-fc.json](lean/comparator-fc.json) is empty. The permitted transitive
axioms are `propext`, `Classical.choice` and `Quot.sound`.

### Statement correspondence

The [definition review](verification/STATEMENT-CORRESPONDENCE.md) checks the
English problem against the formal target. The 26 executable specification
checks in each proof variant cover the sphere, metric conditions, geodesic
equation, prime period, images, variational formulation, nonvacuity and complete
theorem quantifiers.

The prose correspondence is a local AI-assisted mathematical review, rather
than a machine theorem about natural language or an independent human sign-off.

## AI usage disclosure

This formalization, mathematical exploration, proof development, and documentation were produced by Kenta Kitamura with assistance from ChatGPT and OpenAI Codex using GPT-6 Astra and GPT-6.1 sol, and Claude Code using Claude Opus 5.5.

## Sources

- **[OAI26]** OpenAI, *Infinitely many closed geodesic images on every Riemannian
  sphere*, OpenAI Math Release preprint, 24 September 2026, catalogue entry 345.
  [Paper and source](https://github.com/openai/math/tree/main/preprints/Infinitely-many-closed-geodesic-images-on-every-Riemannian-sphere-September-24-2026).
- **[DPMMS22]** G. De Philippis, M. Marini, M. Mazzucchelli and S. Suhr,
  *Closed geodesics on reversible Finsler 2-spheres*, Journal of Fixed Point
  Theory and Applications 24 (2022), Paper No. 19.
  [arXiv:2002.00415](https://arxiv.org/abs/2002.00415).
- [Mathlib](https://github.com/leanprover-community/mathlib4) — Lean mathematical library.
- [Tau Ceti](https://github.com/TauCetiProject/TauCeti) — Lean dependency.
- [Lean Pool](https://github.com/Vilin97/lean-pool) — Lean dependency.
- [Lean Comparator](https://github.com/leanprover/comparator) — theorem and definition comparison tool.
- [Formal Conjectures contribution guide](https://github.com/google-deepmind/formal-conjectures/blob/main/CONTRIBUTING.md) — module layout, standard utility import, definitions and metadata conventions.
- [entropic-rogers-shephard](https://github.com/KitaKen1/entropic-rogers-shephard) — repository structure reference.
- [infinity-laplacian-bounded-forcing](https://github.com/KitaKen1/infinity-laplacian-bounded-forcing) — statement presentation reference.
- [Apache 2.0 license](LICENSE) — project license.

## Appendix: timeline (AI generated)

| Date | Contributor | Contribution |
| --- | --- | --- |
| 2022 | De Philippis, Marini, Mazzucchelli and Suhr | Proved the reversible Finsler $S^2$ case [DPMMS22]. |
| 24 September 2026 | OpenAI | Presented the Riemannian sphere result for $n \ge 2$, Statement 1 [OAI26]. |
| 21 October 2026 | This repository | Reduced the FC submission to three definitions and four statements; n = 2 is supplied by the literature. |
| 19 October 2026 | This repository | Packaged the $n \ge 3$ reversible Finsler Lean proof, four FC-style statements and local verification records. |

OpenAI's preprint supplies the Riemannian sphere result and the reference
framework for the higher-dimensional development. Statement 2 combines the
cited $n = 2$ result with this repository's $n \ge 3$ proof. Its all-dimensional
Lean declaration remains statement-only.

## Appendix: Verification by Lean Comparator on GitHub CI runner

### CI status

The [exact-target workflow](.github/workflows/fc-target.yml) verifies the n ≥ 3
FC target on public `main` in
[GitHub Actions](https://github.com/KitaKen1/reversible-finsler-spheres/actions/workflows/fc-target.yml).
It builds the proof from source, checks its transitive axioms and runs the
unmodified pinned Comparator CLI with built-in kernel replay.
[Run 39703676590](https://github.com/KitaKen1/reversible-finsler-spheres/actions/runs/39703676590)
passed all steps on 22 October 2026 at 05:30 UTC (14:30 JST). The broader historical
[workflow](.github/workflows/verification.yml) remains available for manual dispatch.

### Logs and archives

The exact-target workflow retains build and Comparator logs for 90 days.
The [successful public run's build, Comparator and axiom logs](verification/ci/39703676590/)
are committed here with a [source-hashed receipt](verification/ci/39703676590/receipt.json).
The downloaded artifact ZIP matched GitHub's SHA-256 digest before extraction.
The [earlier successful sandbox logs](verification/ci/39700419746/) remain
available. Additional evidence is in the [local log collection](verification/local/),
with outcomes and hashes recorded in the
[receipt](verification/local/receipt.json) and
[FC receipt](verification/local/fc-four-statements-receipt.json).

### Reproduce the verification

Install [elan](https://github.com/leanprover/elan). From this repository:

```bash
python3 scripts/check-package.py
python3 scripts/fetch-target-cache.py --project lean
python3 scripts/build-serial.py --project lean FCExactChallenge
python3 scripts/build-serial.py --project lean --warm-target Finsler.Residual.FillRel FCExactSolution FCExactAudit
```

The serial builder compiles the local import closure one module at a time,
with 4 GiB per Lean process and two Lean threads. A normal
`cd lean && lake build` also builds the solution, but may schedule more
concurrent work. Dependency caches are fetched for the selected imports. The
separate FC metadata/readback check can be run with
`python3 scripts/check-fc-statements.py --fc-source /path/to/formal-conjectures`;
it reuses the build and removes its temporary output directory.

For the version without Comparator:

```bash
python3 scripts/fetch-target-cache.py --project leanWithoutComparator FCExactSolution FCExactAudit
python3 scripts/build-serial.py --project leanWithoutComparator FCExactSolution FCExactAudit
```

Each Lean directory can be copied out as a standalone project. Its pinned
`lake-manifest.json` and `lean-toolchain` must stay with it. There are 2,055
`Finsler/` modules in each snapshot; the default target builds the solution's
import closure rather than every historical module.

On Linux, after building the reference and solution and installing Go 1.25
or newer, run the exact FC Comparator path from the repository root:

```bash
bash lean/comparator/install-tools.sh
bash lean/comparator/run-fc-check.sh
```

See the [verification guide](lean/comparator/README.md) for pinned tools,
the Linux sandbox and the local incremental route. These commands reproduce
checks; the recorded results are those in [verification/STATUS.md](verification/STATUS.md).
