module

public import Finsler.Topology.DiagonalAvoidanceCocycle
public import Finsler.Topology.SupportedCap
public import Finsler.Geometry.RotorHomotopy

/-! The actual diagonal class restricts to zero on a closed small tube
around the diagonal. The two projections are homotopic by the existing
continuous rotor path. The homotopy is in the sphere, so no unproved
deformation retraction of the closed tube is needed. -/

@[expose] public section
namespace Finsler.NearDiagonalCohomology

open CategoryTheory SphereOddDegree
open Finsler.SphereGeometry Finsler.CochainComparison Finsler.BorelEvaluation
open Finsler.DiagonalCohomology Finsler.NearbyRotor Finsler.RotorHomotopy
open Set

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

local instance (n : ℕ) : CompactSpace (Sphere n) :=
  isCompact_iff_compactSpace.mp (isCompact_sphere (0 : Ambient n) 1)

local instance (n : ℕ) : CompactSpace (product n) :=
  inferInstanceAs (CompactSpace (Sphere n × Sphere n))

def near (n : ℕ) (δ : ℝ) : Set (product n) :=
  {z | ‖(z.2 : Ambient n) - z.1‖ ≤ δ}

theorem near_closed (n : ℕ) (δ : ℝ) : IsClosed (near n δ) :=
  isClosed_le (((continuous_subtype_val.comp continuous_snd).sub
    (continuous_subtype_val.comp continuous_fst)).norm) continuous_const

theorem near_compact (n : ℕ) (δ : ℝ) : IsCompact (near n δ) := (near_closed n δ).isCompact

def inclusion (n : ℕ) (δ : ℝ) : TopCat.of (near n δ) ⟶ product n :=
  SupportedCap.subspaceMap (product n) (near n δ)

def first (n : ℕ) (δ : ℝ) : TopCat.of (near n δ) ⟶ sphere n := inclusion n δ ≫ prFirst n
def second (n : ℕ) (δ : ℝ) : TopCat.of (near n δ) ⟶ sphere n := inclusion n δ ≫ prSecond n

def slide (n : ℕ) (δ : ℝ) (s : _root_.unitInterval) (z : near n δ) : Sphere n :=
  ⟨path s (z.val.1 : Ambient n) (z.val.2 : Ambient n) (z.val.1 : Ambient n), by
    have h := (path s (z.val.1 : Ambient n) (z.val.2 : Ambient n)).norm_map (z.val.1 : Ambient n)
    rw [DiagonalGeometry.sphere_norm] at h
    simpa using h⟩

theorem continuous_slide (n : ℕ) {δ : ℝ} (hδ : δ ≤ 1) :
    Continuous (fun z : _root_.unitInterval × near n δ => slide n δ z.1 z.2) := by
  have hx : Continuous (fun z : _root_.unitInterval × near n δ => (z.2.val.1 : Ambient n)) :=
    continuous_subtype_val.comp (continuous_fst.comp (continuous_subtype_val.comp continuous_snd))
  have hy : Continuous (fun z : _root_.unitInterval × near n δ => (z.2.val.2 : Ambient n)) :=
    continuous_subtype_val.comp (continuous_snd.comp (continuous_subtype_val.comp continuous_snd))
  have hp := continuous_fst.prodMk (hx.prodMk hy)
  have hc := path_operator_continuousOn.comp_continuous hp (fun z => by
    refine ⟨DiagonalGeometry.sphere_norm _, DiagonalGeometry.sphere_norm _, ?_⟩
    change dist (z.2.val.2 : Ambient n) (z.2.val.1 : Ambient n) ≤ 1
    rw [dist_eq_norm]
    exact z.2.property.trans hδ)
  exact (hc.clm_apply hx).subtype_mk _

theorem slide_zero (n : ℕ) (δ : ℝ) (z : near n δ) : slide n δ 0 z = first n δ z := by
  apply Subtype.ext
  change path 0 (z.val.1 : Ambient n) (z.val.2 : Ambient n) (z.val.1 : Ambient n) = _
  rw [path_zero]
  rfl

theorem slide_one (n : ℕ) (δ : ℝ) (z : near n δ) : slide n δ 1 z = second n δ z := by
  apply Subtype.ext
  change path 1 (z.val.1 : Ambient n) (z.val.2 : Ambient n) (z.val.1 : Ambient n) = _
  rw [path_one]
  exact rotor_map ((DiagonalGeometry.sphere_norm z.val.1).trans (DiagonalGeometry.sphere_norm z.val.2).symm)

def homotopy (n : ℕ) {δ : ℝ} (hδ : δ ≤ 1) : TopCat.Homotopy (first n δ) (second n δ) where
  toFun z := slide n δ z.1 z.2
  continuous_toFun := continuous_slide n hδ
  map_zero_left z := slide_zero n δ z
  map_one_left z := slide_one n δ z

theorem restriction_zero (n : ℕ) (hn : 1 ≤ n) {δ : ℝ} (hδ : δ ≤ 1) :
    (cohPullback (inclusion n δ) n).hom (ambientClass n hn) = 0 := by
  have he := DiagonalCohomology.homotopy_pullback (homotopy n hδ) n (SphereTopClass.topClass n hn)
  change (cohPullback (inclusion n δ) n).hom
    ((cohPullback (prFirst n) n).hom (SphereTopClass.topClass n hn) +
      (cohPullback (prSecond n) n).hom (SphereTopClass.topClass n hn)) = 0
  rw [map_add, ← Cup.pullback_comp, ← Cup.pullback_comp]
  change (cohPullback (first n δ) n).hom (SphereTopClass.topClass n hn) +
    (cohPullback (second n δ) n).hom (SphereTopClass.topClass n hn) = 0
  rw [he]
  let a := (cohPullback (second n δ) n).hom (SphereTopClass.topClass n hn)
  change a + a = 0
  calc
    _ = ((1 : ZMod 2) + 1) • a := by rw [add_smul, one_smul]
    _ = 0 := by rw [show (1 : ZMod 2) + 1 = 0 from by decide, zero_smul]

end
end Finsler.NearDiagonalCohomology
