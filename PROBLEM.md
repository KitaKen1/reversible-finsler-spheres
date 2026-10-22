# Problem statement and conventions

For every integer **n ≥ 3**, every **smooth, strongly convex, reversible Finsler
metric** on the standard sphere **Sⁿ** has **infinitely many geometrically
distinct prime closed geodesics**.

The sphere is the unit sphere in Euclidean (n + 1)-space, equipped with its
standard smooth structure and actual tangent bundle.

A metric is a continuous function F on that tangent bundle, smooth off the
zero section, zero at zero, positive on nonzero tangent vectors, positively
homogeneous of degree one and reversible: F(x, −v) = F(x, v). The fiberwise
Hessian of ½F² is positive definite at every nonzero vector. These are fields
of `Finsler.Geometry.ReversibleMetric`, not extra assumptions on the theorem.

A closed geodesic is a smooth curve γ : ℝ → Sⁿ of period 1, with nowhere-zero
velocity, satisfying the actual coordinate Euler–Lagrange equation for F² in
every sphere chart where the curve is in that chart. Multiplication of the
Lagrangian by the positive constant ½ does not change the equation.
The equivalent variational formulation is stationarity of
E(γ) = ∫₀¹ F(γ(t), γ̇(t))² dt under every smooth periodic variation.

“Prime” means that the normalized period 1 is the least positive period.
“Geometrically distinct” means the subsets range(γ) ⊆ Sⁿ are distinct.
The theorem asserts that this **set of subsets** is infinite; it does not
count parameterizations, reverse orientations or positive iterates as
different images.

The normalized period does not prescribe the length or speed as 1.
No curvature condition, genericity, bumpiness or nondegeneracy condition
appears in the statement. The proof entry points export the n ≥ 3 result.
The separate [FC-style presentation](FClikelean/README.md) also states the
Riemannian n ≥ 2, reversible Finsler n ≥ 2 and reversible Finsler n = 2 results;
those three statements have no local Lean proof in this package.

Formal statement: [FCSolution.lean](lean/FCSolution.lean).
Definition-by-definition review: [correspondence](verification/STATEMENT-CORRESPONDENCE.md).

