module

public import Finsler.Loop.ContinuousSegmentFamily

/-! Use the existing actual broken-geodesic construction on ALL short
polygons, with no H1-energy hypothesis on the source family. Its
strong H1 continuity, vertices, energy and constants are verified. -/

@[expose] public section
namespace Finsler.ShortPolygonH1Model
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.PolygonModel Finsler.PolygonLoop Finsler.PolygonCritical
open Finsler.SobolevCircleRepresentative Finsler.PiecewiseC1
open Finsler.SobolevEnergy
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

abbrev polygons {n : ℕ} {F : ReversibleMetric n} (S : SegmentData F) (N : ℕ) :=
  {q : ZMod N → Sphere n // ShortPolygon S.δ q}

def broken {n : ℕ} {F : ReversibleMetric n} (S : SegmentData F) (N : ℕ) [NeZero N]
    (q : polygons S N) : SphereLoop n := polySphereLoop F S.seg q.property

theorem broken_continuous {n : ℕ} {F : ReversibleMetric n} (S : SegmentData F) (N : ℕ) [NeZero N] :
    Continuous (broken S N) := by
  rw [(sphereLoop_data_isometry n).isEmbedding.continuous_iff]
  apply continuous_iff_continuousAt.mpr
  intro q₀
  have h := (brokenGeodesic_continuousAt F S.seg S.unif N q₀.property).comp
    (continuous_subtype_val.continuousAt (x := q₀))
  refine h.congr (Filter.Eventually.of_forall fun q => ?_)
  exact brokenGeodesic_of_short F S.seg N q.property

theorem sample_broken {n : ℕ} {F : ReversibleMetric n} (S : SegmentData F) (N : ℕ) [NeZero N]
    (q : polygons S N) : PolygonSampling.samplePoly N (broken S N q) = q.val :=
  PolygonSampling.samplePoly_polySphereLoop F S.seg q.property

theorem energy_broken {n : ℕ} {F : ReversibleMetric n} (S : SegmentData F) (N : ℕ) [NeZero N]
    (q : polygons S N) :
    SobolevEnergy.energy F (broken S N q) = polyEnergy F N (fun i => (q.val i : Ambient n)) :=
  (polyEnergy_polySphereLoop F S.seg q.property).symm

def constantPolygon {n : ℕ} {F : ReversibleMetric n} (S : SegmentData F) (N : ℕ) (P : Sphere n) :
    polygons S N := ⟨fun _ => P, by intro i; change ‖(P : Ambient n) - P‖ < S.δ; simpa using S.pos⟩

theorem broken_constant {n : ℕ} {F : ReversibleMetric n} (S : SegmentData F) (N : ℕ) [NeZero N]
    (hconst : ∀ P : Sphere n, ∀ t, S.sc P P t = P) (P : Sphere n) :
    broken S N (constantPolygon S N P) = constantSphereLoop P := by
  apply sphereLoop_eq_of_representative_eq
  intro t
  rw [sphereRepresentative_constantSphereLoop]
  apply Subtype.ext
  change continuousRepresentative (polyLoop F S.seg (constantPolygon S N P).property) t = (P : Ambient n)
  rw [representative_polyLoop F S.seg (constantPolygon S N P).property t.property]
  exact hconst P (pieceLoc N t)

end
end Finsler.ShortPolygonH1Model
