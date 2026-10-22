module

public import Finsler.Geometry.PolygonSampling

/-! Refinement of polygons. The refinement of a short polygon with N vertices is the polygon
with r N vertices obtained by sampling its broken geodesic at r N points; forgetting all but
every r-th vertex of a polygon with r N vertices gives a polygon with N vertices. Forgetting
after refining gives back the polygon. The polygon energy of the coarse polygon is at most the
polygon energy of a short fine polygon (the samples of a loop have at most its energy), and
refinement preserves the polygon energy when the refined polygon is short. Thus the polygon
energy with N vertices is the minimum of the polygon energy with r N vertices over the inserted
vertices. No differentiability is used in this file. -/

@[expose] public section

namespace Finsler.PolygonRefine

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.SobolevSpherePath
open Finsler.SobolevEnergy Finsler.PolygonLoop Finsler.PolygonCritical Finsler.PolygonBasics
open Finsler.PolygonSampling
open Finsler.SphereDistance (minEnergy)
open MeasureTheory Set Filter
open scoped Topology

noncomputable section

variable {n : ℕ} (r N : ℕ)

/-- Forgetting all but every r-th vertex. -/
def coarse {α : Type*} (q' : ZMod (r * N) → α) : ZMod N → α :=
  fun j => q' ((r * j.val : ℕ) : ZMod (r * N))

variable [NeZero r] [NeZero N]

/-- The sample time of the vertex r j of the fine grid is the sample time of the vertex j of the
coarse grid. -/
theorem sampleTime_mul (j : ZMod N) :
    sampleTime (r * N) ((r * j.val : ℕ) : ZMod (r * N)) = sampleTime N j := by
  have hj : j.val < N := ZMod.val_lt j
  have hr : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have hlt : r * j.val < r * N := Nat.mul_lt_mul_of_pos_left hj hr
  apply Subtype.ext
  change (((r * j.val : ℕ) : ZMod (r * N)).val : ℝ) / ((r * N : ℕ) : ℝ) = (j.val : ℝ) / (N : ℝ)
  rw [ZMod.val_natCast_of_lt hlt]
  have hr' : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  push_cast
  field_simp

/-- Forgetting vertices of the samples of a loop gives its samples on the coarse grid. -/
theorem coarse_samplePoly (u : SphereLoop n) :
    coarse r N (samplePoly (r * N) u) = samplePoly N u := by
  funext j
  change sphereRepresentative u (sampleTime (r * N) ((r * j.val : ℕ) : ZMod (r * N))) =
    sphereRepresentative u (sampleTime N j)
  rw [sampleTime_mul]

section Segments

variable (F : ReversibleMetric n) {δ : ℝ} {sc sv : Sphere n → Sphere n → ℝ → Ambient n}
  (hseg : ∀ P Q : Sphere n, ‖(Q : Ambient n) - P‖ < δ →
    (∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (sc P Q) (sv P Q t) t) ∧
    ContinuousOn (sv P Q) (Icc 0 1) ∧ sc P Q 0 = P ∧ sc P Q 1 = Q ∧
    (∀ t, ‖sc P Q t‖ = 1) ∧
    ∫ t in (0 : ℝ)..1, Finsler.AmbientLagrangian.lagrangian F (sc P Q t, sv P Q t) =
      minEnergy F P Q)

/-- The refinement of a short polygon: the samples of its broken geodesic at r N points. -/
def refine {q : ZMod N → Sphere n} (hq : ShortPolygon δ q) : ZMod (r * N) → Sphere n :=
  samplePoly (r * N) (polySphereLoop F hseg hq)

/-- Forgetting the inserted vertices of the refinement gives back the polygon. -/
theorem coarse_refine {q : ZMod N → Sphere n} (hq : ShortPolygon δ q) :
    coarse r N (refine r N F hseg hq) = q := by
  rw [refine, coarse_samplePoly, samplePoly_polySphereLoop F hseg hq]

include hseg in
/-- The polygon energy of the coarse polygon is at most the polygon energy of a short fine
polygon. -/
theorem polyEnergy_coarse_le {q' : ZMod (r * N) → Sphere n} (hq' : ShortPolygon δ q') :
    polyEnergy F N (fun j => ((coarse r N q' j : Sphere n) : Ambient n)) ≤
      polyEnergy F (r * N) (fun i => (q' i : Ambient n)) := by
  have h := polyEnergy_sample_le F (N := N) (polySphereLoop F hseg hq')
  have e : (fun j => ((coarse r N q' j : Sphere n) : Ambient n)) =
      sampleN N (polySphereLoop F hseg hq') := by
    rw [← samplePoly_coe, ← coarse_samplePoly r N, samplePoly_polySphereLoop F hseg hq']
  rw [polyEnergy_polySphereLoop F hseg hq', e]
  exact h

/-- **Refinement preserves the polygon energy**, if the refined polygon is short. -/
theorem polyEnergy_refine {q : ZMod N → Sphere n} (hq : ShortPolygon δ q)
    (hR : ShortPolygon δ (refine r N F hseg hq)) :
    polyEnergy F (r * N) (fun i => (refine r N F hseg hq i : Ambient n)) =
      polyEnergy F N (fun j => (q j : Ambient n)) := by
  apply le_antisymm
  · rw [polyEnergy_polySphereLoop F hseg hq]
    exact polyEnergy_sample_le F (polySphereLoop F hseg hq)
  · have h := polyEnergy_coarse_le r N F hseg hR
    rwa [coarse_refine] at h

end Segments

end

end Finsler.PolygonRefine
