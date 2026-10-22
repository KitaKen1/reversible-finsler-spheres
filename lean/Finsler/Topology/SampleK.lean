module

public import Finsler.Topology.PolygonLoopPairs
public import Finsler.Topology.PolygonLensK
public import Finsler.Topology.BorelLocalK

/-! Sampling as a K-equivariant map of crossing pairs. For polygons with 2M vertices the rotation
of loops by one half is the rotation of the samples by M vertices, and sampling commutes with the
reversal. So the sampling map of a crossing pair (t_b, t_a) of loops to the crossing pair of the
polygons of energy below b², a² commutes with the reversal and the half rotation on the loops and
with the reversal and the rotation by M of the vertices on the polygons. Since it is bijective on
actual relative cohomology for all large numbers of vertices (`PolygonLoopPairs`), it is bijective
on the K-Borel cohomology of the crossing pairs (comparison principle): the K-Borel crossing
groups of the loop space are those of the polygon models. -/

@[expose] public section

namespace Finsler.SampleK

open CategoryTheory Set
open Finsler.Geometry Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.SobolevReverse
open Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop Finsler.BorelIterate
open Finsler.BorelK Finsler.BorelCoverK Finsler.BorelLocalK Finsler.AvoidPoint
open Finsler.PolygonLoop Finsler.PolygonSampling Finsler.PolygonModel Finsler.PolygonLoopPairs
open Finsler.PolygonDescent Finsler.PolygonDescentK Finsler.PolygonLensK Finsler.InvPairs
open Finsler.FlowLens Finsler.PairTriple Finsler.LocalCoverK

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {n : ℕ}

/-- The rotation by M of the vertices of polygons with 2M vertices has order two. -/
theorem half_shift (M : ℕ) : (M : ZMod (2 * M)) + (M : ZMod (2 * M)) = 0 := by
  rw [← Nat.cast_add, ← two_mul, ZMod.natCast_self]

theorem iterate_rotatePolygon {N : ℕ} (k : ℕ) (q : ZMod N → Sphere n) :
    rotatePolygon^[k] q = rotPoly (k : ZMod N) q := by
  induction k generalizing q with
  | zero =>
    funext i
    change q i = q (i + ((0 : ℕ) : ZMod N))
    rw [Nat.cast_zero, add_zero]
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih]
    funext i
    change q (i + (k : ZMod N) + 1) = q (i + ((k + 1 : ℕ) : ZMod N))
    push_cast
    rw [add_assoc]

/-- Sampling with 2M vertices takes the half rotation of loops to the rotation by M. -/
theorem sample_half {M : ℕ} [NeZero M] (u : SphereLoop n) :
    samplePoly (2 * M) (half +ᵥ u) = rotPoly (M : ZMod (2 * M)) (samplePoly (2 * M) u) := by
  have h := sample_rotate_nat (N := 2 * M) M u
  have e : ((((M : ℕ) : ℝ) / ((2 * M : ℕ) : ℝ) : ℝ) : Finsler.SobolevCircleRepresentative.Circle) =
      half := by
    have hM : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
    congr 1
    push_cast
    field_simp
  rw [e] at h
  rw [h, iterate_rotatePolygon]

variable {F : ReversibleMetric n} {M : ℕ} [NeZero M] {a b : ℝ}

/-- The K-action on polygons with 2M vertices: reversal and rotation by M. -/
abbrev kPoly (n M : ℕ) : KAct (Poly n (2 * M)) := polyK n (2 * M) (half_shift M)

theorem inv_subPoly (c : ℝ) : Inv (kPoly n M) (sub (energy F (2 * M)) c) :=
  Finsler.LensK.inv_sub (kPoly n M) (energy_reversePolygon F) (energy_rotPoly F _) c

/-- The sampling map of crossing pairs. -/
abbrev samplePair (ha : 0 < a) (hab : a ≤ b) :
    pairOf (lev_mono F hab) ⟶ pairOf (sub_sq_mono (F := F) (N := 2 * M) hab ha) :=
  pairMapX (lev_mono F hab) (sub_sq_mono (F := F) (N := 2 * M) hab ha)
    (sampleMap (F := F) (N := 2 * M) (ha.trans_le hab))
    (fun u hu => (polyEnergy_samplePoly_le (F := F) (N := 2 * M) (u : SphereLoop n)).trans_lt
      ((mem_lev_iff ha _).mp hu))

theorem samplePair_rev (ha : 0 < a) (hab : a ≤ b) :
    samplePair (M := M) ha hab ≫ restrictPair (kPoly n M).ρ (sub_sq_mono hab ha)
        (inv_subPoly (a ^ 2)).ρ_mem (inv_subPoly (b ^ 2)).ρ_mem =
      revSub (lev_mono F hab) (kInv_lev F a).rev_mem (kInv_lev F b).rev_mem ≫
        samplePair (M := M) ha hab := by
  ext x
  · exact Subtype.ext (sample_reverse (N := 2 * M) _).symm
  · exact Subtype.ext (sample_reverse (N := 2 * M) _).symm

theorem samplePair_half (ha : 0 < a) (hab : a ≤ b) :
    samplePair (M := M) ha hab ≫ restrictPair (kPoly n M).σ (sub_sq_mono hab ha)
        (inv_subPoly (a ^ 2)).σ_mem (inv_subPoly (b ^ 2)).σ_mem =
      halfSub (lev_mono F hab) (kInv_lev F a).half_mem (kInv_lev F b).half_mem ≫
        samplePair (M := M) ha hab := by
  ext x
  · exact Subtype.ext (sample_half _).symm
  · exact Subtype.ext (sample_half _).symm

/-- Sampling as a map of K-Borel cochains from the polygon crossing pair to the loop crossing
pair. -/
def sampleHom (ha : 0 < a) (hab : a ≤ b) :
    CommHom (gCommuting (kPoly n M) (sub_sq_mono (F := F) hab ha) (inv_subPoly (a ^ 2))
      (inv_subPoly (b ^ 2))) (kCommuting (lev_mono F hab) (kInv_lev F a) (kInv_lev F b)) :=
  BorelInvariance.commHom (revSub_sq (lev_mono F hab) (kInv_lev F a).rev_mem (kInv_lev F b).rev_mem)
    (restrictPair_sq (kPoly n M).ρ (kPoly n M).ρρ (sub_sq_mono hab ha) (inv_subPoly (a ^ 2)).ρ_mem
      (inv_subPoly (b ^ 2)).ρ_mem)
    (samplePair ha hab) (samplePair_rev ha hab)
    (halfSub_sq (lev_mono F hab) (kInv_lev F a).half_mem (kInv_lev F b).half_mem)
    (restrictPair_sq (kPoly n M).σ (kPoly n M).σσ (sub_sq_mono hab ha) (inv_subPoly (a ^ 2)).σ_mem
      (inv_subPoly (b ^ 2)).σ_mem)
    (halfSub_rev (lev_mono F hab) (kInv_lev F a).rev_mem (kInv_lev F b).rev_mem
      (kInv_lev F a).half_mem (kInv_lev F b).half_mem)
    (restrictPair_comm (kPoly n M).ρ (kPoly n M).σ (kPoly n M).ρσ (sub_sq_mono hab ha)
      (inv_subPoly (a ^ 2)).ρ_mem (inv_subPoly (b ^ 2)).ρ_mem (inv_subPoly (a ^ 2)).σ_mem
      (inv_subPoly (b ^ 2)).σ_mem)
    (samplePair_half ha hab)

/-- **The K-Borel crossing groups of the loop space are those of the polygon models.** For every
level A, for all large M and cuts 0 < a ≤ b ≤ A, sampling with 2M vertices is bijective on the
K-Borel cohomology of the crossing pairs. -/
theorem exists_HK_sample_bijective (F : ReversibleMetric n) (hn : 1 ≤ n) (A : ℝ) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ [NeZero M] {a b : ℝ} (ha : 0 < a) (hab : a ≤ b), b ≤ A →
      ∀ q : ℕ, Function.Bijective (HRmap (borelHom (sampleHom (F := F) (M := M) ha hab)) q) := by
  obtain ⟨N₀, hN₀⟩ := exists_sample_bijective F hn A
  refine ⟨N₀, fun M hM _ a b ha hab hbA q => ?_⟩
  have hN : N₀ ≤ 2 * M := le_trans hM (by omega)
  exact BorelInvariance.bijective_iterated _ _ _ _ _ _ _ _ _
    (fun k => Finsler.LensK.nativePull_bijective_of_Hmap _ k
      (hN₀ (2 * M) hN ha hab hbA k)) q

end

end Finsler.SampleK
