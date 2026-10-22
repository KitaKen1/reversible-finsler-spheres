module

public import Finsler.Analysis.IntervalH1HalfRoot

/-! Genuine strong-H¹ homeomorphism between sphere loops and their actual
half-period rotation fixed subset. Its inverse is the certified weak root,
whose continuity follows from the distance lower bound for double iteration. -/

@[expose] public section

namespace Finsler.SobolevHalfRoot

open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.SobolevEnergy
open Finsler.SobolevCircleRepresentative Finsler.SobolevCircleAction
open Finsler.SobolevIteration Finsler.CircleLpTransfer
open Finsler.Geometry Finsler.SobolevReflectionAction Set
open scoped Topology NNReal

noncomputable section

theorem halfFixed_realMap_periodic {n : ℕ} (u : HalfFixed n) :
    Function.Periodic (realMap u.val.data) (1 / 2) := by
  intro t
  have h := (fixed_phase_iff_circleMap u.val halfPhase).mp u.property (t : Phase)
  have hv := congrArg (fun x : Sphere n => (x : Ambient n)) h
  change circleMap u.val.data (((t + 1 / 2 : ℝ) : Phase)) = circleMap u.val.data (t : Phase)
  have hc : ((t + 1 / 2 : ℝ) : Phase) = halfPhase + (t : Phase) := by
    simp only [AddCircle.coe_add, halfPhase]
    exact add_comm _ _
  exact (congrArg (fun x : Phase => circleMap u.val.data x) hc).trans
    (by simpa only [sphereCircleMap_val] using hv)

theorem root_realMap_periodic {n : ℕ} (u : HalfFixed n) :
    Function.Periodic (fun t => realMap u.val.data ((1 / 2 : ℝ) * t)) 1 := by
  intro t
  have h := halfFixed_realMap_periodic u ((1 / 2 : ℝ) * t)
  change realMap u.val.data ((1 / 2 : ℝ) * (t + 1)) = _
  convert h using 1
  congr 1
  ring

theorem realMap_rootSphere {n : ℕ} (u : HalfFixed n) (t : ℝ) :
    realMap (rootSphere u).data t = realMap u.val.data ((1 / 2 : ℝ) * t) := by
  have ht : Int.fract t ∈ Icc (0 : ℝ) 1 := ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩
  have hl : realMap (rootSphere u).data (Int.fract t) = realMap (rootSphere u).data t := by
    simpa only [Int.fract, mul_one] using
      (realMap_periodic (rootSphere u).data).sub_int_mul_eq (x := t) ⌊t⌋
  have hr : realMap u.val.data ((1 / 2 : ℝ) * Int.fract t) =
      realMap u.val.data ((1 / 2 : ℝ) * t) := by
    simpa only [Int.fract, mul_one] using (root_realMap_periodic u).sub_int_mul_eq (x := t) ⌊t⌋
  rw [← hl, ← hr, realMap_eqOn (rootSphere u).data ht]
  exact representative_rootData u.val.data ht

def doubleSphere {n : ℕ} (u : SphereLoop n) : HalfFixed n :=
  ⟨iterateSphere u 2 (by norm_num), doubleSphere_fixed_half u⟩

theorem doubleSphere_val {n : ℕ} (u : SphereLoop n) :
    (doubleSphere u : SphereLoop n) = iterateSphere u 2 (by norm_num) := rfl

theorem double_rootSphere {n : ℕ} (u : HalfFixed n) : doubleSphere (rootSphere u) = u := by
  apply Subtype.ext
  apply sphereLoop_eq_of_representative_eq
  intro t
  apply Subtype.ext
  change continuousRepresentative (iterateData (rootSphere u).data 2 (by norm_num)) t =
    continuousRepresentative (u.val.data : Space n) t
  rw [representative_iterateData (rootSphere u).data 2 (by norm_num) t.property, realMap_rootSphere]
  have hm : (1 / 2 : ℝ) * ((2 : ℕ) : ℝ) * (t : ℝ) = (t : ℝ) := by norm_num
  rw [← mul_assoc, hm, realMap_eqOn u.val.data t.property]

theorem root_doubleSphere {n : ℕ} (u : SphereLoop n) : rootSphere (doubleSphere u) = u := by
  apply iterateSphere_injective n 2 (by norm_num)
  exact congrArg Subtype.val (double_rootSphere (doubleSphere u))

theorem halfFixedSet_eq_range (n : ℕ) :
    halfFixedSet n = Set.range (fun u : SphereLoop n => iterateSphere u 2 (by norm_num)) := by
  ext u
  constructor
  · intro hu
    exact ⟨rootSphere ⟨u, hu⟩, congrArg Subtype.val (double_rootSphere ⟨u, hu⟩)⟩
  · rintro ⟨v, rfl⟩
    exact doubleSphere_fixed_half v

theorem rootSphere_lipschitz (n : ℕ) : LipschitzWith 1 (rootSphere (n := n)) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  have h := dist_le_iterateSphere (rootSphere u) (rootSphere v) 2 (by norm_num)
  have hu := congrArg Subtype.val (double_rootSphere u)
  have hv := congrArg Subtype.val (double_rootSphere v)
  change iterateSphere (rootSphere u) 2 (by norm_num) = u.val at hu
  change iterateSphere (rootSphere v) 2 (by norm_num) = v.val at hv
  rw [hu, hv] at h
  simpa only [NNReal.coe_one, one_mul, Subtype.dist_eq] using h

theorem rootSphere_continuous (n : ℕ) : Continuous (rootSphere (n := n)) :=
  (rootSphere_lipschitz n).continuous

theorem doubleSphere_lipschitz (n : ℕ) : LipschitzWith 2 (doubleSphere (n := n)) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  exact (iterateSphere_lipschitz n 2 (by norm_num)).dist_le_mul u v

theorem doubleSphere_continuous (n : ℕ) : Continuous (doubleSphere (n := n)) :=
  (doubleSphere_lipschitz n).continuous

def halfFixedHomeomorph (n : ℕ) : SphereLoop n ≃ₜ HalfFixed n where
  toFun := doubleSphere
  invFun := rootSphere
  left_inv := root_doubleSphere
  right_inv := double_rootSphere
  continuous_toFun := doubleSphere_continuous n
  continuous_invFun := rootSphere_continuous n

theorem halfFixedHomeomorph_apply {n : ℕ} (u : SphereLoop n) :
    halfFixedHomeomorph n u = doubleSphere u := rfl

theorem halfFixedHomeomorph_symm_apply {n : ℕ} (u : HalfFixed n) :
    (halfFixedHomeomorph n).symm u = rootSphere u := rfl

theorem energy_rootSphere {n : ℕ} (F : ReversibleMetric n) (u : HalfFixed n) :
    energy F (rootSphere u) = energy F u.val / 4 := by
  have h := energy_doubleSphere F (rootSphere u)
  have hu := congrArg Subtype.val (double_rootSphere u)
  change iterateSphere (rootSphere u) 2 (by norm_num) = u.val at hu
  rw [hu] at h
  linarith

theorem sqrt_energy_rootSphere {n : ℕ} (F : ReversibleMetric n) (u : HalfFixed n) :
    Real.sqrt (energy F (rootSphere u)) = Real.sqrt (energy F u.val) / 2 := by
  have h := sqrt_energy_iterateSphere F (rootSphere u) 2 (by norm_num)
  have hu := congrArg Subtype.val (double_rootSphere u)
  change iterateSphere (rootSphere u) 2 (by norm_num) = u.val at hu
  rw [hu] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith

theorem sphereImage_rootSphere {n : ℕ} (u : HalfFixed n) :
    Finsler.SobolevReverse.sphereImage (rootSphere u) = Finsler.SobolevReverse.sphereImage u.val := by
  have hu := congrArg Subtype.val (double_rootSphere u)
  change iterateSphere (rootSphere u) 2 (by norm_num) = u.val at hu
  exact (sphereImage_iterateSphere (rootSphere u) 2 (by norm_num)).symm.trans
    (congrArg Finsler.SobolevReverse.sphereImage hu)

end

end Finsler.SobolevHalfRoot
