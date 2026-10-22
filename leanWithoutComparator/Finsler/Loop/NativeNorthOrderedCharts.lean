module

public import Finsler.Loop.NativeGlobalTimeSquare

/-! ACTUAL forward and wrapped DISTINCT-leg northern cells in the
ORIGINAL global cut-time/rotation square. Their maps agree EXACTLY
with the original independent native cut (north-rescaled), or its
actual complement, including all endpoints. No cell sum is assumed. -/
@[expose] public section
namespace Finsler.NativeNorthOrderedCharts
open CategoryTheory Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.MeridianLoopFamily
open Finsler.NativeMeridianMatchingLoci Finsler.NativeMeridianPairCoordinates
open Finsler.MeridianTripleQuarterClocks Finsler.SobolevShift Finsler.SobolevCircleAction
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1100000

theorem north_clock (k : Fin 3) (s : ClosedInterval) :
    clock k 0 s = legClock k (MeridianQuarterIncidence.northTime s) := by
  fin_cases k <;> dsimp [clock, localTime, legClock, MeridianQuarterIncidence.northTime] <;> ring

private theorem continuous_northTime : Continuous MeridianQuarterIncidence.northTime := by
  exact (continuous_subtype_val.div_const 2).subtype_mk _

private theorem continuous_legClock (k : Fin 3) : Continuous (legClock k) := by
  fin_cases k
  · change Continuous (fun t : ClosedInterval => (t : ℝ) / 8)
    fun_prop
  · change Continuous (fun t : ClosedInterval => (2 + (t : ℝ)) / 8)
    fun_prop
  · change Continuous (fun t : ClosedInterval => (2 + (t : ℝ)) / 4)
    fun_prop

private theorem continuous_pairCutTime (b : Fin 3) :
    Continuous (fun z : ClosedInterval × ClosedInterval => pairCutTime b z.1 z.2) :=
  (((continuous_legClock (pairRight b)).comp continuous_snd).sub
    ((continuous_legClock (pairLeft b)).comp continuous_fst)).subtype_mk _

private theorem continuous_assembly {n : ℕ} (P : Sphere n) (b : Fin 3) :
    Continuous (fun z : equator P × (equator P × equator P) => assembly b z.1 z.2.1 z.2.2) := by
  fin_cases b
  · exact (continuous_fst.prodMk continuous_snd.fst).prodMk continuous_snd.snd
  · exact (continuous_fst.prodMk continuous_snd.snd).prodMk continuous_snd.fst
  · exact (continuous_snd.snd.prodMk continuous_fst).prodMk continuous_snd.fst

private theorem continuous_cut {n : ℕ} (P : Sphere n) (b : Fin 3) :
    Continuous (fun z : NativeMeridianPairCoordinates.parameters P => pairCutTime b
      (MeridianQuarterIncidence.northTime z.1.1) (MeridianQuarterIncidence.northTime z.2.1.1)) :=
  (continuous_pairCutTime b).comp
    ((continuous_northTime.comp continuous_fst.fst).prodMk (continuous_northTime.comp continuous_snd.fst.fst))

private theorem continuous_source {n : ℕ} (P : Sphere n) (b : Fin 3) :
    Continuous (fun z : NativeMeridianPairCoordinates.parameters P => assembly b z.1.2 z.2.1.2 z.2.2) :=
  (continuous_assembly P b).comp (continuous_fst.snd.prodMk (continuous_snd.fst.snd.prodMk continuous_snd.snd))

def northParameters {n : ℕ} (P : Sphere n) :
    NativeMeridianPairCoordinates.parameters P ⟶ NativeMeridianPairCoordinates.parameters P :=
  TopCat.ofHom ⟨fun z => ((MeridianQuarterIncidence.northTime z.1.1, z.1.2),
    ((MeridianQuarterIncidence.northTime z.2.1.1, z.2.1.2), z.2.2)), by
    exact ((continuous_northTime.comp continuous_fst.fst).prodMk continuous_fst.snd).prodMk
      (((continuous_northTime.comp continuous_snd.fst.fst).prodMk continuous_snd.fst.snd).prodMk continuous_snd.snd)⟩

def forward {n : ℕ} (P : Sphere n) (b : Fin 3) :
    NativeMeridianPairCoordinates.parameters P ⟶ NativeGlobalTimeSquare.squareDomain P :=
  TopCat.ofHom ⟨fun z => (pairCutTime b (MeridianQuarterIncidence.northTime z.1.1)
    (MeridianQuarterIncidence.northTime z.2.1.1), (z.1.1, assembly b z.1.2 z.2.1.2 z.2.2)), by
    exact (continuous_cut P b).prodMk (continuous_fst.fst.prodMk (continuous_source P b))⟩

def wrapped {n : ℕ} (P : Sphere n) (b : Fin 3) :
    NativeMeridianPairCoordinates.parameters P ⟶ NativeGlobalTimeSquare.squareDomain P :=
  TopCat.ofHom ⟨fun z => (⟨1 - (pairCutTime b (MeridianQuarterIncidence.northTime z.1.1)
    (MeridianQuarterIncidence.northTime z.2.1.1) : ℝ), by
      have ht := pairCutTime_interior b (MeridianQuarterIncidence.northTime z.1.1) (MeridianQuarterIncidence.northTime z.2.1.1)
      constructor <;> linarith [ht.1, ht.2]⟩, (z.2.1.1, assembly b z.1.2 z.2.1.2 z.2.2)), by
    exact ((continuous_const.sub (continuous_subtype_val.comp (continuous_cut P b))).subtype_mk _).prodMk
      (continuous_snd.fst.fst.prodMk (continuous_source P b))⟩

def rotationSource {n : ℕ} (P : Sphere n) (k : Fin 3) :
    NativeGlobalTimeSquare.squareDomain P ⟶ NativeTripleSelfEvaluation.sourceSpace P :=
  TopCat.ofHom ⟨fun z => (z.1, (⟨clock k 0 z.2.1, clock_mem k 0 z.2.1⟩, z.2.2)), by
    have ht : Continuous (fun z : NativeGlobalTimeSquare.squareDomain P =>
        (⟨clock k 0 z.2.1, clock_mem k 0 z.2.1⟩ : ClosedInterval)) := by
      fin_cases k <;> dsimp [clock, localTime] <;> fun_prop
    exact continuous_fst.prodMk (ht.prodMk continuous_snd.snd)⟩

theorem global_factor {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) :
    NativeGlobalTimeSquare.intoCut P v₀ k =
      rotationSource P k ≫ NativeTripleSelfEvaluation.intoCut P v₀ := rfl

theorem forward_source {n : ℕ} (P : Sphere n) (b : Fin 3) :
    forward P b ≫ rotationSource P (pairLeft b) =
      northParameters P ≫ NativeMeridianPairCoordinates.intoSource P b := by
  apply TopCat.ext
  intro z
  apply Prod.ext
  · rfl
  · exact Prod.ext (Subtype.ext (north_clock (pairLeft b) z.1.1)) rfl

theorem forward_intoCut {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) :
    forward P b ≫ NativeGlobalTimeSquare.intoCut P v₀ (pairLeft b) =
      northParameters P ≫ NativeMeridianPairCoordinates.intoCut P v₀ b := by
  have h := congrArg (fun f => f ≫ NativeTripleSelfEvaluation.intoCut P v₀) (forward_source P b)
  exact (congrArg (fun f => forward P b ≫ f) (global_factor P v₀ (pairLeft b))).trans
    ((Category.assoc _ _ _).symm.trans (h.trans (Category.assoc _ _ _)))

theorem forward_cut_interior {n : ℕ} (P : Sphere n) (b : Fin 3) (z : NativeMeridianPairCoordinates.parameters P) :
    0 < ((forward P b z).1 : ℝ) ∧ ((forward P b z).1 : ℝ) < 1 :=
  pairCutTime_interior b _ _

theorem wrapped_cut_interior {n : ℕ} (P : Sphere n) (b : Fin 3) (z : NativeMeridianPairCoordinates.parameters P) :
    0 < ((wrapped P b z).1 : ℝ) ∧ ((wrapped P b z).1 : ℝ) < 1 := by
  have ht := forward_cut_interior P b z
  change 0 < 1 - ((forward P b z).1 : ℝ) ∧ 1 - ((forward P b z).1 : ℝ) < 1
  exact ⟨sub_pos.mpr ht.2, sub_lt_self 1 ht.1⟩

end
end Finsler.NativeNorthOrderedCharts
