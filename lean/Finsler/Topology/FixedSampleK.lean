module

public import Finsler.Topology.SampleK

/-! Sampling of the loops fixed by the half rotation. For polygons with 2M vertices the rotation of
loops by one half is the rotation by M vertices of the samples, and the broken geodesics and the
straightening homotopy commute with it too (`PolygonModel`). So sampling maps the loops of t_b
fixed by the half rotation to the polygons of energy below b² fixed by the rotation by M, the
broken geodesic maps these back to fixed loops, and the straightening homotopy keeps fixed loops.
The argument for the crossing pairs (`PolygonLoopPairs`) therefore applies to the fixed crossing
pairs: sampling is bijective on their actual relative cohomology for all large M, hence on their
reflection Borel and K-Borel cohomology (comparison principle). -/

@[expose] public section

namespace Finsler.FixedSampleK

open CategoryTheory Set
open Finsler.Geometry Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.SobolevReverse
open Finsler.SobolevEnergy Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop
open Finsler.BorelIterate Finsler.BorelK Finsler.BorelCoverK Finsler.BorelLocalK
open Finsler.PolygonLoop Finsler.PolygonSampling Finsler.PolygonModel Finsler.PolygonLoopPairs
open Finsler.PolygonDescent Finsler.PolygonDescentK Finsler.PolygonLensK Finsler.InvPairs
open Finsler.FlowLens Finsler.PairTriple Finsler.LocalCoverK Finsler.SampleK
open Finsler.BorelFixed Finsler.CutPotential Finsler.BorelComparison Finsler.AvoidPoint

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {n : ℕ} {F : ReversibleMetric n} {A : ℝ} {M : ℕ} [NeZero M]

/-- The polygons with 2M vertices fixed by the rotation by M. -/
def fixP (n M : ℕ) : Set (Poly n (2 * M)) := {q | rotPoly (M : ZMod (2 * M)) q = q}

omit [NeZero M] in
theorem inv_fixP : Inv (kPoly n M) (fixP n M) where
  ρ_mem q hq := by
    change rotPoly (M : ZMod (2 * M)) (reversePolygon q) = reversePolygon q
    rw [← reversePolygon_rotPoly (half_shift M)]
    exact congrArg reversePolygon hq
  σ_mem q hq := by
    change rotPoly (M : ZMod (2 * M)) (rotPoly (M : ZMod (2 * M)) q) = rotPoly (M : ZMod (2 * M)) q
    rw [hq, hq]

/-- The fixed polygons of energy below c. -/
abbrev fixSub (F : ReversibleMetric n) (M : ℕ) (c : ℝ) : Set (Poly n (2 * M)) :=
  sub (energy F (2 * M)) c ∩ fixP n M

theorem inv_fixSub (c : ℝ) : Inv (kPoly n M) (fixSub F M c) := inv_inter (inv_subPoly c) inv_fixP

omit [NeZero M] in
theorem fixSub_mono {a b : ℝ} (hab : a ≤ b) (ha : 0 < a) :
    fixSub F M (a ^ 2) ⊆ fixSub F M (b ^ 2) :=
  fun _ hq => ⟨sub_sq_mono hab ha hq.1, hq.2⟩

/-- Samples of a loop fixed by the half rotation are fixed by the rotation by M. -/
theorem sample_fixed {u : SphereLoop n} (hu : half +ᵥ u = u) :
    samplePoly (2 * M) u ∈ fixP n M := by
  change rotPoly (M : ZMod (2 * M)) (samplePoly (2 * M) u) = samplePoly (2 * M) u
  rw [← sample_half, hu]

theorem circle_half :
    ((((M : ℕ) : ℝ) / ((2 * M : ℕ) : ℝ) : ℝ) : Finsler.SobolevCircleRepresentative.Circle) =
      half := by
  have hM : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
  congr 1
  push_cast
  field_simp

variable (P : PolygonModelData F A (2 * M))

/-- The broken geodesic of a fixed short polygon is fixed by the half rotation. -/
theorem broken_fixed (q : {q : ZMod (2 * M) → Sphere n // ShortPolygon P.δ q})
    (hq : q.1 ∈ fixP n M) : half +ᵥ broken P q = broken P q := by
  have h := broken_rotate_nat P M q
  have e : (rotateShort P)^[M] q = q := by
    apply Subtype.ext
    have : ∀ k (r : {q : ZMod (2 * M) → Sphere n // ShortPolygon P.δ q}),
        ((rotateShort P)^[k] r).1 = rotatePolygon^[k] r.1 := by
      intro k
      induction k with
      | zero => intro r; rfl
      | succ k ih =>
        intro r
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
        rfl
    rw [this, iterate_rotatePolygon]
    exact hq
  rw [e, circle_half] at h
  exact h.symm

/-- The straightening homotopy keeps the loops fixed by the half rotation. -/
theorem deform_fixed (p : ℝ × SphereLoop n) (hp : half +ᵥ p.2 = p.2) :
    half +ᵥ deform P p = deform P p := by
  have h := deform_rotate_nat P M p
  rw [circle_half, hp] at h
  exact h.symm

variable {a b : ℝ}

/-- Sampling on the fixed loops below b. -/
def sampleFix (hb : 0 < b) : C(fixLev F b, fixSub F M (b ^ 2)) :=
  ⟨fun u => ⟨samplePoly (2 * M) (u : SphereLoop n),
      (polyEnergy_samplePoly_le (F := F) (N := 2 * M) (u : SphereLoop n)).trans_lt
        ((mem_lev_iff hb _).mp ((mem_fixLev_iff F b _).mp u.2).1),
      sample_fixed ((mem_fixLev_iff F b _).mp u.2).2⟩,
    ((samplePoly_continuous (2 * M)).comp continuous_subtype_val).subtype_mk _⟩

variable (hshort : ∀ q : ZMod (2 * M) → Sphere n, energy F (2 * M) q < b ^ 2 →
  ShortPolygon P.δ q)

/-- The broken geodesic on the fixed polygons of energy below b². -/
def brokenFix (hb : 0 < b) : C(fixSub F M (b ^ 2), fixLev F b) :=
  ⟨fun q => ⟨broken P ⟨(q : ZMod (2 * M) → Sphere n), hshort _ q.2.1⟩,
      (mem_fixLev_iff F b _).mpr ⟨(mem_lev_iff hb _).mpr (by
        rw [energy_broken]
        exact q.2.1), broken_fixed P ⟨(q : ZMod (2 * M) → Sphere n), hshort _ q.2.1⟩ q.2.2⟩⟩,
    ((broken_continuous P).comp (continuous_subtype_val.subtype_mk _)).subtype_mk _⟩

theorem sample_brokenFix (hb : 0 < b) :
    (sampleFix (F := F) (M := M) hb).comp (brokenFix P hshort hb) =
      ContinuousMap.id (fixSub F M (b ^ 2)) := by
  refine ContinuousMap.ext fun q => Subtype.ext ?_
  exact sample_broken P ⟨(q : ZMod (2 * M) → Sphere n), hshort _ q.2.1⟩

/-- The straightening homotopy on the fixed loops. -/
def straightenFix (hb : 0 < b) (hbA : b ≤ A) :
    ((brokenFix P hshort hb).comp (sampleFix (F := F) (M := M) hb)).Homotopy
      (ContinuousMap.id (fixLev F b)) where
  toFun p := ⟨deform P (1 - (p.1 : ℝ), (p.2 : SphereLoop n)), (mem_fixLev_iff F b _).mpr
    ⟨(mem_lev_iff hb _).mpr
      ((energy_deform_le P (p := (1 - (p.1 : ℝ), (p.2 : SphereLoop n)))
        ⟨⟨sub_nonneg.mpr p.1.2.2, sub_le_self 1 p.1.2.1⟩,
          ((mem_lev_iff hb _).mp ((mem_fixLev_iff F b _).mp p.2.2).1).trans_le
            (pow_le_pow_left₀ hb.le hbA 2)⟩).trans_lt
        ((mem_lev_iff hb _).mp ((mem_fixLev_iff F b _).mp p.2.2).1)),
      deform_fixed P _ ((mem_fixLev_iff F b _).mp p.2.2).2⟩⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    have hmap : Continuous fun p : _root_.unitInterval × fixLev F b =>
        ((1 - (p.1 : ℝ), (p.2 : SphereLoop n)) : ℝ × SphereLoop n) :=
      (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).prodMk
        (continuous_subtype_val.comp continuous_snd)
    refine (deform_continuousOn P).comp_continuous hmap fun p => ?_
    exact ⟨⟨sub_nonneg.mpr p.1.2.2, sub_le_self 1 p.1.2.1⟩,
      ((mem_lev_iff hb _).mp ((mem_fixLev_iff F b _).mp p.2.2).1).trans_le
        (pow_le_pow_left₀ hb.le hbA 2)⟩
  map_zero_left u := by
    apply Subtype.ext
    have hu : SobolevEnergy.energy F (u : SphereLoop n) < A ^ 2 :=
      ((mem_lev_iff hb _).mp ((mem_fixLev_iff F b _).mp u.2).1).trans_le
        (pow_le_pow_left₀ hb.le hbA 2)
    change deform P (1 - ((0 : _root_.unitInterval) : ℝ), (u : SphereLoop n)) =
      broken P ⟨samplePoly (2 * M) (u : SphereLoop n), _⟩
    rw [show ((0 : _root_.unitInterval) : ℝ) = 0 from rfl, sub_zero, deform_one P hu]
  map_one_left u := by
    apply Subtype.ext
    have hu : SobolevEnergy.energy F (u : SphereLoop n) < A ^ 2 :=
      ((mem_lev_iff hb _).mp ((mem_fixLev_iff F b _).mp u.2).1).trans_le
        (pow_le_pow_left₀ hb.le hbA 2)
    change deform P (1 - ((1 : _root_.unitInterval) : ℝ), (u : SphereLoop n)) = (u : SphereLoop n)
    rw [show ((1 : _root_.unitInterval) : ℝ) = 1 from rfl, sub_self, deform_zero P hu]

include hshort in
/-- **Sampling of fixed loops is bijective on the cohomology of the fixed crossing pairs.** -/
theorem fixed_sample_bijective (ha : 0 < a) (hab : a ≤ b) (hbA : b ≤ A) (k : ℕ) :
    Function.Bijective (Hmap (trivHom (pairMapX (fixLev_mono F hab)
      (fixSub_mono (F := F) (M := M) hab ha) (sampleFix (F := F) (M := M) (ha.trans_le hab))
      (fun u hu => ⟨(polyEnergy_samplePoly_le (F := F) (N := 2 * M) (u : SphereLoop n)).trans_lt
        ((mem_lev_iff ha _).mp ((mem_fixLev_iff F a _).mp hu).1),
        sample_fixed ((mem_fixLev_iff F a _).mp hu).2⟩))) k) := by
  have hb : 0 < b := ha.trans_le hab
  refine bijective_Hmap_of_section (fixLev_mono F hab) (fixSub_mono hab ha)
    (sampleFix (F := F) (M := M) hb) (brokenFix P hshort hb) _ ?_
    (sample_brokenFix P hshort hb) (straightenFix P hshort hb hbA) ?_ k
  · intro q hq
    refine (mem_fixLev_iff F a _).mpr ⟨(mem_lev_iff ha _).mpr ?_,
      broken_fixed P ⟨(q : ZMod (2 * M) → Sphere n), hshort _ q.2.1⟩ q.2.2⟩
    change SobolevEnergy.energy F (broken P ⟨(q : ZMod (2 * M) → Sphere n), hshort _ q.2.1⟩) < a ^ 2
    rw [energy_broken]
    exact hq.1
  · intro τ u hu
    refine (mem_fixLev_iff F a _).mpr ⟨(mem_lev_iff ha _).mpr ?_,
      deform_fixed P _ ((mem_fixLev_iff F a _).mp hu).2⟩
    have huA : SobolevEnergy.energy F (u : SphereLoop n) < A ^ 2 :=
      ((mem_lev_iff hb _).mp ((mem_fixLev_iff F b _).mp u.2).1).trans_le
        (pow_le_pow_left₀ hb.le hbA 2)
    exact (energy_deform_le P (p := (1 - (τ : ℝ), (u : SphereLoop n)))
      ⟨⟨sub_nonneg.mpr τ.2.2, sub_le_self 1 τ.2.1⟩, huA⟩).trans_lt
        ((mem_lev_iff ha _).mp ((mem_fixLev_iff F a _).mp hu).1)

include hshort in
theorem fixed_sample_nativePull (ha : 0 < a) (hab : a ≤ b) (hbA : b ≤ A) (k : ℕ) :
    Function.Bijective (nativePull (pairMapX (fixLev_mono F hab)
      (fixSub_mono (F := F) (M := M) hab ha) (sampleFix (F := F) (M := M) (ha.trans_le hab))
      (fun u hu => ⟨(polyEnergy_samplePoly_le (F := F) (N := 2 * M) (u : SphereLoop n)).trans_lt
        ((mem_lev_iff ha _).mp ((mem_fixLev_iff F a _).mp hu).1),
        sample_fixed ((mem_fixLev_iff F a _).mp hu).2⟩)) k) :=
  Finsler.LensK.nativePull_bijective_of_Hmap _ k (fixed_sample_bijective P hshort ha hab hbA k)

section K

variable {F : ReversibleMetric n} {M : ℕ} [NeZero M] {a b : ℝ}

/-- Sampling of fixed loops as a map of the fixed crossing pairs. -/
abbrev samplePairFix (ha : 0 < a) (hab : a ≤ b) :
    pairOf (fixLev_mono F hab) ⟶ pairOf (fixSub_mono (F := F) (M := M) hab ha) :=
  pairMapX (fixLev_mono F hab) (fixSub_mono (F := F) (M := M) hab ha)
    (sampleFix (F := F) (M := M) (ha.trans_le hab))
    (fun u hu => ⟨(polyEnergy_samplePoly_le (F := F) (N := 2 * M) (u : SphereLoop n)).trans_lt
      ((mem_lev_iff ha _).mp ((mem_fixLev_iff F a _).mp hu).1),
      sample_fixed ((mem_fixLev_iff F a _).mp hu).2⟩)

theorem samplePairFix_rev (ha : 0 < a) (hab : a ≤ b) :
    samplePairFix (M := M) ha hab ≫ restrictPair (kPoly n M).ρ (fixSub_mono hab ha)
        (inv_fixSub (a ^ 2)).ρ_mem (inv_fixSub (b ^ 2)).ρ_mem =
      revSub (fixLev_mono F hab) (kInv_fixLev F a).rev_mem (kInv_fixLev F b).rev_mem ≫
        samplePairFix (M := M) ha hab := by
  ext x
  · exact Subtype.ext (sample_reverse (N := 2 * M) _).symm
  · exact Subtype.ext (sample_reverse (N := 2 * M) _).symm

theorem samplePairFix_half (ha : 0 < a) (hab : a ≤ b) :
    samplePairFix (M := M) ha hab ≫ restrictPair (kPoly n M).σ (fixSub_mono hab ha)
        (inv_fixSub (a ^ 2)).σ_mem (inv_fixSub (b ^ 2)).σ_mem =
      halfSub (fixLev_mono F hab) (kInv_fixLev F a).half_mem (kInv_fixLev F b).half_mem ≫
        samplePairFix (M := M) ha hab := by
  ext x
  · exact Subtype.ext (sample_half _).symm
  · exact Subtype.ext (sample_half _).symm

/-- Sampling of fixed loops as a map of K-Borel cochains from the fixed polygon crossing pair to
the fixed loop crossing pair. -/
def sampleFixHom (ha : 0 < a) (hab : a ≤ b) :
    CommHom (gCommuting (kPoly n M) (fixSub_mono (F := F) hab ha) (inv_fixSub (a ^ 2))
      (inv_fixSub (b ^ 2))) (kCommuting (fixLev_mono F hab) (kInv_fixLev F a) (kInv_fixLev F b)) :=
  BorelInvariance.commHom
    (revSub_sq (fixLev_mono F hab) (kInv_fixLev F a).rev_mem (kInv_fixLev F b).rev_mem)
    (restrictPair_sq (kPoly n M).ρ (kPoly n M).ρρ (fixSub_mono hab ha) (inv_fixSub (a ^ 2)).ρ_mem
      (inv_fixSub (b ^ 2)).ρ_mem)
    (samplePairFix ha hab) (samplePairFix_rev ha hab)
    (halfSub_sq (fixLev_mono F hab) (kInv_fixLev F a).half_mem (kInv_fixLev F b).half_mem)
    (restrictPair_sq (kPoly n M).σ (kPoly n M).σσ (fixSub_mono hab ha) (inv_fixSub (a ^ 2)).σ_mem
      (inv_fixSub (b ^ 2)).σ_mem)
    (halfSub_rev (fixLev_mono F hab) (kInv_fixLev F a).rev_mem (kInv_fixLev F b).rev_mem
      (kInv_fixLev F a).half_mem (kInv_fixLev F b).half_mem)
    (restrictPair_comm (kPoly n M).ρ (kPoly n M).σ (kPoly n M).ρσ (fixSub_mono hab ha)
      (inv_fixSub (a ^ 2)).ρ_mem (inv_fixSub (b ^ 2)).ρ_mem (inv_fixSub (a ^ 2)).σ_mem
      (inv_fixSub (b ^ 2)).σ_mem)
    (samplePairFix_half ha hab)

/-- **The fixed crossing groups of the loop space are those of the fixed polygon models.** For
every level A, for all large M and cuts 0 < a ≤ b ≤ A, sampling of fixed loops with 2M vertices
is bijective on the K-Borel and the reflection Borel cohomology of the fixed crossing pairs. -/
theorem exists_fixed_sample_bijective (F : ReversibleMetric n) (hn : 1 ≤ n) (A : ℝ) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ [NeZero M] {a b : ℝ} (ha : 0 < a) (hab : a ≤ b), b ≤ A →
      (∀ q : ℕ, Function.Bijective (HRmap (borelHom (sampleFixHom (F := F) (M := M) ha hab)) q)) ∧
      (∀ q : ℕ, Function.Bijective (HRmap (sampleFixHom (F := F) (M := M) ha hab).φ q)) := by
  obtain ⟨S⟩ := exists_segmentData F
  obtain ⟨N₁, hN₁⟩ := exists_sample_spacing F (δ := S.δ) (a := A) S.pos
  obtain ⟨c, hc, hedge⟩ := Finsler.PolygonEnergyGlobal.exists_edge_bound F hn
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt (A ^ 2 / (c * S.δ ^ 2))
  refine ⟨max N₁ N₂, fun M hM _ a b ha hab hbA => ?_⟩
  have hN : max N₁ N₂ ≤ 2 * M := le_trans hM (by omega)
  have hNpos : 0 < 2 * M := by have := NeZero.ne M; omega
  let P : PolygonModelData F A (2 * M) :=
    PolygonModelData.mk S fun u hu s t hs ht hst =>
      hN₁ (2 * M) ((le_max_left _ _).trans hN) hNpos u hu s t hs ht hst
  have hNR : A ^ 2 / (c * S.δ ^ 2) < ((2 * M : ℕ) : ℝ) :=
    hN₂.trans_le (Nat.cast_le.mpr ((le_max_right _ _).trans hN))
  have hshort : ∀ q : ZMod (2 * M) → Sphere n, energy F (2 * M) q < b ^ 2 →
      ShortPolygon P.δ q := fun q hq =>
    short_of_energy_lt hc S.pos hedge hbA (ha.le.trans hab) hNR q hq
  have hnat := fun k => fixed_sample_nativePull P hshort ha hab hbA k
  exact ⟨fun q => BorelInvariance.bijective_iterated _ _ _ _ _ _ _ _ _ hnat q,
    fun q => BorelInvariance.bijective_HRmap
      (revSub_sq (fixLev_mono F hab) (kInv_fixLev F a).rev_mem (kInv_fixLev F b).rev_mem)
      (restrictPair_sq (kPoly n M).ρ (kPoly n M).ρρ (fixSub_mono hab ha) (inv_fixSub (a ^ 2)).ρ_mem
        (inv_fixSub (b ^ 2)).ρ_mem)
      (samplePairFix ha hab) (samplePairFix_rev ha hab) hnat q⟩

end K

end

end Finsler.FixedSampleK
