module

public import Finsler.Analysis.H1AffineRestrictionContinuity
public import Finsler.Analysis.H1LoopJoin
public import Finsler.Analysis.H1FiberBase

/-! Actual two-loop splitting on the exact self-coincidence locus, including endpoints.
An open-neighborhood extension and the specified Thom self-cut remain separate. -/

@[expose] public section

namespace Finsler.H1SelfSplit

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.SobolevAffine Finsler.SobolevSpherePath Finsler.H1LoopJoin Finsler.H1FiberBase
open Finsler.H1AffineRestrictionContinuity Finsler.SobolevEnergy Set
open Finsler.CompactH1Alignment
open scoped Topology

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 600000

def coincidence (n : ℕ) : Set (ClosedInterval × SphereLoop n) :=
  {z | point z.2 = sphereRepresentative z.2 z.1}

def left {n : ℕ} (z : coincidence n) : SphereLoop n := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have ht : (z.val.1 : ℝ) ∈ Icc (0 : ℝ) 1 := z.val.1.property
  let v := restrict (z.val.2.data : Space n) h0 ht ht.1
  have hv : v ∈ periodicSubmodule n := by
    apply (mem_periodicSubmodule_iff v).mpr
    change continuousRepresentative v 1 = continuousRepresentative v 0
    exact (representative_restrict_one (z.val.2.data : Space n) h0 ht ht.1).trans
      ((congrArg Subtype.val z.property.symm).trans
        (representative_restrict_zero (z.val.2.data : Space n) h0 ht ht.1).symm)
  exact ⟨⟨v, hv⟩, fun τ => restrict_mem (sphereLoop_mem z.val.2) h0 ht ht.1 τ τ.property⟩

def right {n : ℕ} (z : coincidence n) : SphereLoop n := by
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have ht : (z.val.1 : ℝ) ∈ Icc (0 : ℝ) 1 := z.val.1.property
  let v := restrict (z.val.2.data : Space n) ht h1 ht.2
  have hv : v ∈ periodicSubmodule n := by
    apply (mem_periodicSubmodule_iff v).mpr
    change continuousRepresentative v 1 = continuousRepresentative v 0
    exact (representative_restrict_one (z.val.2.data : Space n) ht h1 ht.2).trans
      ((periodic_trace z.val.2).trans ((congrArg Subtype.val z.property).trans
        (representative_restrict_zero (z.val.2.data : Space n) ht h1 ht.2).symm))
  exact ⟨⟨v, hv⟩, fun τ => restrict_mem (sphereLoop_mem z.val.2) ht h1 ht.2 τ τ.property⟩

theorem representative_left {n : ℕ} (z : coincidence n) (τ : ClosedInterval) :
    continuousRepresentative ((left z).data : Space n) τ =
      continuousRepresentative (z.val.2.data : Space n) (aff 0 z.val.1 τ) :=
  representative_restrict (z.val.2.data : Space n) (by norm_num) z.val.1.property
    z.val.1.property.1 τ.property

theorem representative_right {n : ℕ} (z : coincidence n) (τ : ClosedInterval) :
    continuousRepresentative ((right z).data : Space n) τ =
      continuousRepresentative (z.val.2.data : Space n) (aff z.val.1 1 τ) :=
  representative_restrict (z.val.2.data : Space n) z.val.1.property (by norm_num)
    z.val.1.property.2 τ.property

theorem continuous_left {n : ℕ} : Continuous (left : coincidence n → SphereLoop n) := by
  have ht : Continuous (fun z : coincidence n => z.val.1) := continuous_fst.comp continuous_subtype_val
  have hu : Continuous (fun z : coincidence n => (z.val.2.data : Space n)) :=
    (sphereLoop_data_isometry n).continuous.comp (continuous_snd.comp continuous_subtype_val)
  have hp : Continuous (fun z : coincidence n =>
      ((⟨(0, z.val.1), z.val.1.property.1⟩ : Intervals), (z.val.2.data : Space n))) :=
    ((continuous_const.prodMk ht).subtype_mk _).prodMk hu
  have hd := H1AffineRestrictionContinuity.continuous_restriction.comp hp
  apply continuous_iff_continuousAt.mpr
  intro z
  apply sphereLoop_tendsto_iff.mpr
  exact hd.continuousAt

theorem continuous_right {n : ℕ} : Continuous (right : coincidence n → SphereLoop n) := by
  have ht : Continuous (fun z : coincidence n => z.val.1) := continuous_fst.comp continuous_subtype_val
  have hu : Continuous (fun z : coincidence n => (z.val.2.data : Space n)) :=
    (sphereLoop_data_isometry n).continuous.comp (continuous_snd.comp continuous_subtype_val)
  have hp : Continuous (fun z : coincidence n =>
      ((⟨(z.val.1, 1), z.val.1.property.2⟩ : Intervals), (z.val.2.data : Space n))) :=
    ((ht.prodMk continuous_const).subtype_mk _).prodMk hu
  have hd := H1AffineRestrictionContinuity.continuous_restriction.comp hp
  apply continuous_iff_continuousAt.mpr
  intro z
  apply sphereLoop_tendsto_iff.mpr
  exact hd.continuousAt

theorem basepoint_left {n : ℕ} (z : coincidence n) : basepoint (left z) = basepoint z.val.2 :=
  representative_restrict_zero (z.val.2.data : Space n) (by norm_num)
    z.val.1.property z.val.1.property.1

theorem basepoint_right {n : ℕ} (z : coincidence n) : basepoint (right z) = basepoint z.val.2 := by
  change continuousRepresentative ((right z).data : Space n) 0 = _
  exact (representative_restrict_zero (z.val.2.data : Space n) z.val.1.property
    (by norm_num) z.val.1.property.2).trans (congrArg Subtype.val z.property.symm)

theorem energy_left_le {n : ℕ} (F : ReversibleMetric n) (z : coincidence n) :
    SobolevEnergy.energy F (left z) ≤ (z.val.1 : ℝ) * SobolevEnergy.energy F z.val.2 := by
  have he := pathEnergy_restrict_loop_le F z.val.2 (by norm_num) z.val.1.property z.val.1.property.1
  calc
    _ = pathEnergy F (restrict (z.val.2.data : Space n) (by norm_num)
        z.val.1.property z.val.1.property.1) := (pathEnergy_sphereLoop F (left z)).symm
    _ ≤ ((z.val.1 : ℝ) - 0) * SobolevEnergy.energy F z.val.2 := he
    _ = _ := by rw [sub_zero]

theorem energy_right_le {n : ℕ} (F : ReversibleMetric n) (z : coincidence n) :
    SobolevEnergy.energy F (right z) ≤ (1 - (z.val.1 : ℝ)) * SobolevEnergy.energy F z.val.2 :=
  pathEnergy_restrict_loop_le F z.val.2 z.val.1.property (by norm_num) z.val.1.property.2

theorem left_zero {n : ℕ} (u : SphereLoop n) :
    left (⟨(0, u), rfl⟩ : coincidence n) = constantSphereLoop (point u) := by
  apply SobolevEnergy.sphereLoop_eq_of_representative_eq
  intro τ
  apply Subtype.ext
  change continuousRepresentative ((left (⟨(0, u), rfl⟩ : coincidence n)).data : Space n) τ =
    continuousRepresentative (constantData (point u : Ambient n)) τ
  rw [representative_left, continuousRepresentative_constantData _ τ.property]
  simp [aff, point, sphereRepresentative]

theorem right_zero {n : ℕ} (u : SphereLoop n) : right (⟨(0, u), rfl⟩ : coincidence n) = u := by
  apply SobolevEnergy.sphereLoop_eq_of_representative_eq
  intro τ
  apply Subtype.ext
  rw [show (sphereRepresentative (right (⟨(0, u), rfl⟩ : coincidence n)) τ : Ambient n) =
    continuousRepresentative ((right (⟨(0, u), rfl⟩ : coincidence n)).data : Space n) τ from rfl,
    representative_right]
  simp [aff, sphereRepresentative]

theorem left_one {n : ℕ} (u : SphereLoop n) :
    left (⟨(1, u), (sphereRepresentative_endpoints u).symm⟩ : coincidence n) = u := by
  apply SobolevEnergy.sphereLoop_eq_of_representative_eq
  intro τ
  apply Subtype.ext
  change continuousRepresentative
    ((left (⟨(1, u), (sphereRepresentative_endpoints u).symm⟩ : coincidence n)).data : Space n) τ = _
  rw [representative_left]
  simp [aff, sphereRepresentative]

theorem right_one {n : ℕ} (u : SphereLoop n) :
    right (⟨(1, u), (sphereRepresentative_endpoints u).symm⟩ : coincidence n) =
      constantSphereLoop (point u) := by
  apply SobolevEnergy.sphereLoop_eq_of_representative_eq
  intro τ
  apply Subtype.ext
  change continuousRepresentative
    ((right (⟨(1, u), (sphereRepresentative_endpoints u).symm⟩ : coincidence n)).data : Space n) τ =
      continuousRepresentative (constantData (point u : Ambient n)) τ
  rw [representative_right, continuousRepresentative_constantData _ τ.property]
  simpa [aff, point, sphereRepresentative, basepoint] using periodic_trace u

end
end Finsler.H1SelfSplit
