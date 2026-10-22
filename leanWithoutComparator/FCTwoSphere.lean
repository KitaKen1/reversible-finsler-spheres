import FCTargetDefinitions
import HingstonArithmetic
import HingstonBlocks
import HingstonPause
import SurfaceMinimax
import Finsler.Geometry.CriticalLevels
import Finsler.Topology.AvoidPoint

/-!
# The length-spectrum step for the two-sphere proof

The bounded-gap and odd-iterate cases of DPMMS Lemma 5.5 are proved here for the actual geodesic
and image definitions. The approximation hypothesis is not assumed as an
axiom, and is not yet established for arbitrary reversible Finsler two-spheres.
The remaining geometric work must produce these closed geodesics, or handle
the other branches of the surface argument.
-/

namespace ReversibleFinslerSphereFC

/-- The point-covering branch of the surface argument: if every point lies on
some closed geodesic, the prime image set is not even countable. This uses the
existing theorem that a countable family of smooth geodesic images misses a
point in dimension at least two. -/
theorem prime_images_not_countable_of_geodesic_cover {n : ℕ}
    (F : Finsler.Geometry.ReversibleMetric n) (hn : 2 ≤ n)
    (hcover : ∀ p : Finsler.SphereGeometry.Sphere n,
      ∃ g : Finsler.Geodesics.ClosedGeodesic F, ∃ t : ℝ, g.loop t = p) :
    ¬ (PrimeClosedGeodesicImages F).Countable := by
  rw [primeClosedGeodesicImages_eq, ← Finsler.OrdinaryGeodesics.variational_primeImages_eq]
  intro hcount
  obtain ⟨p, hp⟩ := Finsler.AvoidPoint.exists_point_not_mem_closedGeodesic F hn hcount
  obtain ⟨g, t, ht⟩ := hcover p
  exact hp g t ht

/-- In particular, the point-covering conclusion in the small simple-length
spectrum cases of DPMMS yields the exact FC infinitude target. -/
theorem infinite_prime_images_of_geodesic_cover {n : ℕ}
    (F : Finsler.Geometry.ReversibleMetric n) (hn : 2 ≤ n)
    (hcover : ∀ p : Finsler.SphereGeometry.Sphere n,
      ∃ g : Finsler.Geodesics.ClosedGeodesic F, ∃ t : ℝ, g.loop t = p) :
    (PrimeClosedGeodesicImages F).Infinite := by
  intro hfin
  exact prime_images_not_countable_of_geodesic_cover F hn hcover hfin.countable

/-- Closed geodesics with lengths just above sufficiently large multiples of a
positive length, indexed by a set with bounded gaps, force infinitely many
prime images.

This is DPMMS Lemma 5.5 with forward bounded gaps, and applies in any dimension.
The geodesics are actual regular stationary loops; the conclusion uses the
same coordinate Euler--Lagrange image set as the FC statements. -/
theorem infinite_prime_images_of_dense_length_approximation {n : ℕ}
    (F : Finsler.Geometry.ReversibleMetric n) (l : ℝ) (hl : 0 < l)
    (K : Set ℕ) (D : ℕ)
    (hK : ∀ N : ℕ, ∃ m ∈ K, N ≤ m ∧ m ≤ N + D)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ m ∈ K, M ≤ m →
      ∃ g : Finsler.Geodesics.ClosedGeodesic F,
        (m : ℝ) * l < Real.sqrt (Finsler.LoopEnergy.energy F g.loop) ∧
        Real.sqrt (Finsler.LoopEnergy.energy F g.loop) ≤ (m : ℝ) * l + ε) :
    (PrimeClosedGeodesicImages F).Infinite := by
  classical
  rw [primeClosedGeodesicImages_eq, ← Finsler.OrdinaryGeodesics.variational_primeImages_eq]
  by_contra h
  have hfin : (Finsler.Geodesics.primeImages F).Finite := Set.not_infinite.mp h
  have hlevels := Finsler.CriticalLevels.primeLevels_finite F hfin
  let normalized := (fun x : ℝ => x / l) '' Finsler.CriticalLevels.primeLevels F
  have hnfin : normalized.Finite := hlevels.image _
  have hnpos : ∀ x ∈ hnfin.toFinset, 0 < x := by
    intro x hx
    rcases hnfin.mem_toFinset.mp hx with ⟨y, hy, rfl⟩
    exact div_pos (Finsler.CriticalLevels.primeLevels_pos F hy) hl
  apply Finsler.TwoSphere.Arithmetic.finite_spectrum_not_dense_approximated
    hnfin.toFinset hnpos K D hK
  intro ε hε
  obtain ⟨M, hM⟩ := happrox (ε * l) (mul_pos hε hl)
  refine ⟨M, fun m hmK hm => ?_⟩
  obtain ⟨g, hg, hg'⟩ := hM m hmK hm
  obtain ⟨δ, a, _, hprime, hit, _⟩ := Finsler.Geodesics.exists_prime_representative g
  let L := Real.sqrt (Finsler.LoopEnergy.energy F δ.loop)
  have hL : L ∈ Finsler.CriticalLevels.primeLevels F := ⟨δ, hprime, rfl⟩
  have he : Real.sqrt (Finsler.LoopEnergy.energy F g.loop) = (a : ℝ) * L := by
    rw [← hit, Finsler.LoopEnergy.energy_iterate, Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq (Nat.cast_nonneg a)]
  refine ⟨L / l, hnfin.mem_toFinset.mpr ⟨L, hL, rfl⟩, a, ?_, ?_⟩
  · rw [← mul_div_assoc]
    exact (lt_div_iff₀ hl).mpr (by simpa only [he] using hg)
  · rw [← mul_div_assoc]
    apply (div_le_iff₀ hl).mpr
    rw [he] at hg'
    nlinarith

/-- The odd-iterate specialization used in the Hingston branch of the surface
argument. The length-production hypothesis remains an explicit input. -/
theorem infinite_prime_images_of_odd_length_approximation {n : ℕ}
    (F : Finsler.Geometry.ReversibleMetric n) (l : ℝ) (hl : 0 < l)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ m : ℕ, M ≤ m → Odd m →
      ∃ g : Finsler.Geodesics.ClosedGeodesic F,
        (m : ℝ) * l < Real.sqrt (Finsler.LoopEnergy.energy F g.loop) ∧
        Real.sqrt (Finsler.LoopEnergy.energy F g.loop) ≤ (m : ℝ) * l + ε) :
    (PrimeClosedGeodesicImages F).Infinite := by
  apply infinite_prime_images_of_dense_length_approximation F l hl {m | Odd m} 1
  · intro N
    refine ⟨2 * (N / 2) + 1, ⟨N / 2, by omega⟩, ?_, ?_⟩ <;> omega
  · intro ε hε
    obtain ⟨M, hM⟩ := happrox ε hε
    exact ⟨M, fun m hmK hm => hM m hm hmK⟩

/-- The topological form of the odd-iterate criterion. For arbitrarily small
positive length errors, suppose a nonzero relative homology class dies between
two cuts strictly above each sufficiently large odd multiple of a fixed
positive length. Birkhoff descent produces the nearby closed geodesics, and
the finite-spectrum arithmetic gives infinitely many prime images.

The remaining surface construction must provide these homology classes and
their fillings. `SurfaceMinimax.not_injective_of_disk_filling` reduces this
to a nonzero local disk class extending through a higher-dimensional disk.
No existence of a closed geodesic is assumed in the input of this theorem. -/
theorem infinite_prime_images_of_odd_homology_death {n : ℕ}
    (F : Finsler.Geometry.ReversibleMetric n) (hn : 1 ≤ n)
    (K : Type) [Field K] (l : ℝ) (hl : 0 < l)
    (hdeath : ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ m : ℕ, M ≤ m → Odd m →
      ∃ (a b : ℝ) (hma : (m : ℝ) * l < a) (hab : a ≤ b),
        b ≤ (m : ℝ) * l + ε ∧ ∃ q : ℕ,
          ¬ Function.Injective
            (Finsler.SurfaceMinimax.inclusion F K hma.le hab q)) :
    (PrimeClosedGeodesicImages F).Infinite := by
  apply infinite_prime_images_of_odd_length_approximation F l hl
  intro ε hε
  obtain ⟨M, hM⟩ := hdeath ε hε
  refine ⟨M, fun m hm hodd => ?_⟩
  obtain ⟨a, b, hma, hab, hb, q, hq⟩ := hM m hm hodd
  have ha : 0 < a := (mul_nonneg (Nat.cast_nonneg m) hl.le).trans_lt hma
  obtain ⟨g, hlo, hhi⟩ := Finsler.SurfaceMinimax.exists_geodesic_of_not_injective
    F hn K ha hma.le hab q hq
  exact ⟨g, hma.trans_le hlo, hhi.trans hb⟩

end ReversibleFinslerSphereFC
