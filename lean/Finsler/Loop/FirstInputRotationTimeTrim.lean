module

public import Finsler.Loop.FirstInputRotationFullTime
public import Finsler.Loop.ClosedCapCollarPrism
public import Finsler.Topology.FirstHalfThomNaturality

/-! A genuine full-to-interior slide on the rotating cut cylinder.
One collar is chosen from the original compact alpha family, before
every later join tube and rotation. -/

@[expose] public section
namespace Finsler.FirstInputRotationTimeTrim

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier
open Finsler.FirstInputRotationCutCylinder

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 800000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {n : ℕ}
  (α : C(P, SphereLoop n)) (β : C(Q, SphereLoop n)) (R : ℝ)
  (a : ℝ) (ha : 0 < a) (ha1 : a < 1 / 2)

def trimMap : cylinder α β R ⟶ cylinder α β R :=
  TopCat.ofHom ⟨fun z => (InteriorTimeSlide.trimTime a ha.le ha1.le z.1, z.2),
    ((InteriorTimeSlide.trimTime a ha.le ha1.le).continuous.comp continuous_fst).prodMk continuous_snd⟩

def slideHomotopy : TopCat.Homotopy (𝟙 (cylinder α β R)) (trimMap α β R a ha ha1) where
  toFun z := (InteriorTimeSlide.slide a ha.le ha1.le (z.1, z.2.1), z.2.2)
  continuous_toFun := ((InteriorTimeSlide.slide a ha.le ha1.le).continuous.comp
    (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk (continuous_snd.comp continuous_snd)
  map_zero_left z := Prod.ext (InteriorTimeSlide.slide_zero a ha.le ha1.le z.1) rfl
  map_one_left z := Prod.ext (InteriorTimeSlide.slide_one a ha.le ha1.le z.1) rfl

def sideHomotopy (t : ClosedInterval) :=
  (slideHomotopy α β R a ha ha1).comp (TopCat.Homotopy.refl (AnnularTimeTrim.slice (input α β R) t))

def rotationSlice (s : _root_.unitInterval) :
    TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R) ⟶ cylinder α β R :=
  TopCat.ofHom ⟨fun z => (z.1, (s, z.2)), by fun_prop⟩

theorem exists_uniform_collar [CompactSpace P] {δ : ℝ} (hδ : 0 < δ) :
    ∃ (a : ℝ) (ha : 0 < a) (ha1 : a < 1 / 2),
      ∀ (R : ℝ) (s : _root_.unitInterval) (x : input α β R),
        sideHomotopy α β R a ha ha1 0 (s, x) ∈ collar α β R δ ∧
        sideHomotopy α β R a ha ha1 1 (s, x) ∈ collar α β R δ := by
  obtain ⟨a, ha, ha1, hzero, hone⟩ := InteriorTimeSlide.family_slide_sides_small α hδ
  refine ⟨a, ha, ha1, ?_⟩
  intro R s x
  exact ⟨hzero s x.2.val.1, hone s x.2.val.1⟩

theorem trim_endpoint_collar {δ : ℝ} (t : ClosedInterval)
    (hs : ∀ s x, sideHomotopy α β R a ha ha1 t (s, x) ∈ collar α β R δ)
    (x : input α β R) :
    (AnnularTimeTrim.slice (input α β R) t ≫ trimMap α β R a ha ha1) x ∈ collar α β R δ := by
  have hh := hs 1 x
  change distance n (InteriorTimeSlide.slide a ha.le ha1.le (1, t), α x.2.val.1) ≤ δ at hh
  rw [InteriorTimeSlide.slide_one] at hh
  exact hh

theorem rotation_one_parameters (hR : R ≤ 1 / 2) :
    (rotationSlice α β R 1 ≫ trimMap α β R a ha ha1) ≫
      reorder α β R ≫ FirstInputRotationAmbientCover.ambientEvaluation α β R hR =
        TopCat.ofHom (FirstHalfInteriorFamily.firstParameters
          (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha ha1) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  change (InteriorTimeSlide.trimTime a ha.le ha1.le z.1,
    FirstInputRotationFamily.family α β R (hR.trans_lt (by norm_num)) (1, z.2)) = _
  rw [FirstInputRotationFamily.family_one]
  rfl

end
end Finsler.FirstInputRotationTimeTrim
