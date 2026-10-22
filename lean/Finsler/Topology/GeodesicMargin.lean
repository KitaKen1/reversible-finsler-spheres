module

public import Finsler.Topology.AvoidPoint

/-! A point at positive distance from all closed geodesics. The image of a smooth loop is
compact. If there are only finitely many prime closed geodesic images, a point of the sphere on
no closed geodesic has positive distance from each image, hence a positive distance ρ from all
of them; every tangent critical loop of positive energy is a closed geodesic, so it stays at
distance at least ρ from the point. -/

@[expose] public section

namespace Finsler.GeodesicMargin

open Finsler.SphereGeometry Finsler.Loops Finsler.Geometry Finsler.Geodesics
open Finsler.IntervalSobolev Finsler.SobolevEnergy Finsler.SmoothSobolev
open Finsler.SobolevCurveVariation
open Set

noncomputable section

variable {n : ℕ}

/-- The image of a smooth loop is compact. -/
theorem image_isCompact (γ : SmoothLoop n) : IsCompact (Finsler.Loops.image γ) := by
  have h : Finsler.Loops.image γ = γ.curve '' Icc (0 : ℝ) (0 + 1) :=
    (γ.periodic.image_Icc one_pos 0).symm
  rw [h]
  exact isCompact_Icc.image γ.smooth.continuous

/-- With finitely many prime closed geodesic images, some point of the sphere has a positive
distance from every tangent critical loop of positive energy. -/
theorem exists_margin (F : ReversibleMetric n) (hn : 2 ≤ n) (hfin : (primeImages F).Finite) :
    ∃ (p : Sphere n) (ρ : ℝ), 0 < ρ ∧ ∀ u : SphereLoop n, TangentCritical F u →
      0 < energy F u → ∀ t : ClosedInterval,
        ρ ≤ ‖(sphereRepresentative u t : Ambient n) - (p : Ambient n)‖ := by
  obtain ⟨p, hp⟩ := Finsler.AvoidPoint.exists_point_not_mem_closedGeodesic F hn hfin.countable
  have hpos : ∀ s ∈ primeImages F, 0 < Metric.infDist p s := by
    rintro s ⟨γ, _, rfl⟩
    have hcl : IsClosed (Finsler.Loops.image γ.loop) := (image_isCompact γ.loop).isClosed
    have hne : (Finsler.Loops.image γ.loop).Nonempty := ⟨γ.loop 0, 0, rfl⟩
    have hnot : p ∉ Finsler.Loops.image γ.loop := by
      rintro ⟨t, ht⟩
      exact hp γ t ht
    exact (hcl.notMem_iff_infDist_pos hne).mp hnot
  obtain ⟨ρ, hρ, hle⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ∀ s ∈ primeImages F, ρ ≤ Metric.infDist p s := by
    by_cases hne : (primeImages F).Nonempty
    · obtain ⟨s₀, hs₀, hmin⟩ := Set.exists_min_image (primeImages F)
        (fun s => Metric.infDist p s) hfin hne
      exact ⟨Metric.infDist p s₀, hpos s₀ hs₀, hmin⟩
    · exact ⟨1, one_pos, fun s hs => absurd ⟨s, hs⟩ hne⟩
  refine ⟨p, ρ, hρ, fun u hu hE t => ?_⟩
  obtain ⟨g, rfl⟩ :=
    (Finsler.SobolevGeodesicCritical.tangentCritical_iff_closedGeodesic F u hE).mp hu
  rw [sphereRepresentative_ofSmooth]
  have hmem : Finsler.Loops.image g.loop ∈ primeImages F := by
    rw [← Finsler.Geodesics.closedImages_eq_primeImages]
    exact ⟨g, rfl⟩
  have h1 := hle _ hmem
  have h2 : Metric.infDist p (Finsler.Loops.image g.loop) ≤ dist p (g.loop t) :=
    Metric.infDist_le_dist_of_mem ⟨t, rfl⟩
  have h3 : dist p (g.loop t) = ‖((g.loop t : Sphere n) : Ambient n) - (p : Ambient n)‖ := by
    rw [Subtype.dist_eq, dist_comm, dist_eq_norm]
  linarith

end

end Finsler.GeodesicMargin
