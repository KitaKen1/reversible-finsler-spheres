module

public import Finsler.Analysis.IntervalH1ShiftEnergy
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

/-! Genuine L² transfer between the Lebesgue interval and the standard circle.
The canonical measurable section and covering map preserve the actual measures.
Their induced L² maps are inverse linear isometries. Circle translations vary
jointly continuously in L². This is not a circle Sobolev identification. -/

@[expose] public section

namespace Finsler.CircleLpTransfer

open Finsler.IntervalSobolev MeasureTheory Set Filter
open scoped Topology ENNReal

noncomputable section

abbrev Phase := Finsler.SobolevCircleRepresentative.Circle
abbrev CircleLp (E : Type*) [NormedAddCommGroup E] := Lp E 2 (volume : Measure Phase)

local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

def sectionPoint (x : Phase) : ℝ := AddCircle.equivIoc (1 : ℝ) 0 x

theorem sectionPoint_coe (x : Phase) : ((sectionPoint x : ℝ) : Phase) = x :=
  AddCircle.coe_equivIoc

theorem sectionPoint_eq {t : ℝ} (ht : t ∈ Ioc 0 1) : sectionPoint (t : Phase) = t := by
  exact congrArg Subtype.val (AddCircle.equivIoc_coe_eq (by simpa only [zero_add] using ht))

theorem section_measurePreserving : MeasurePreserving sectionPoint
    (volume : Measure Phase) intervalMeasure := by
  have h := (measurePreserving_subtype_coe (μa := (volume : Measure ℝ))
    (measurableSet_Ioc : MeasurableSet (Ioc (0 : ℝ) (0 + 1)))).comp
      (AddCircle.measurePreserving_equivIoc (1 : ℝ) (a := 0))
  change MeasurePreserving sectionPoint (volume : Measure Phase)
    (volume.restrict (Ioc (0 : ℝ) (0 + 1))) at h
  simpa only [zero_add, ← MeasureTheory.restrict_Ioo_eq_restrict_Ioc] using! h

theorem cover_measurePreserving : MeasurePreserving (fun t : ℝ => (t : Phase))
    intervalMeasure (volume : Measure Phase) := by
  have h := AddCircle.measurePreserving_mk (1 : ℝ) 0
  simpa only [zero_add, ← MeasureTheory.restrict_Ioo_eq_restrict_Ioc] using! h

def toCircleL (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Lp E 2 intervalMeasure →L[ℝ] CircleLp E :=
  (Lp.compMeasurePreservingₗᵢ ℝ sectionPoint section_measurePreserving).toContinuousLinearMap

def toIntervalL (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    CircleLp E →L[ℝ] Lp E 2 intervalMeasure :=
  (Lp.compMeasurePreservingₗᵢ ℝ (fun t : ℝ => (t : Phase)) cover_measurePreserving).toContinuousLinearMap

theorem toCircleL_ae {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Lp E 2 intervalMeasure) : toCircleL E f =ᵐ[volume] fun x => f (sectionPoint x) :=
  Lp.coeFn_compMeasurePreserving f section_measurePreserving

theorem toIntervalL_ae {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : CircleLp E) : toIntervalL E f =ᵐ[intervalMeasure] fun t => f (t : Phase) :=
  Lp.coeFn_compMeasurePreserving f cover_measurePreserving

theorem toCircleL_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Lp E 2 intervalMeasure) : ‖toCircleL E f‖ = ‖f‖ :=
  Lp.norm_compMeasurePreserving f section_measurePreserving

theorem toIntervalL_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : CircleLp E) : ‖toIntervalL E f‖ = ‖f‖ :=
  Lp.norm_compMeasurePreserving f cover_measurePreserving

theorem toInterval_toCircle {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Lp E 2 intervalMeasure) : toIntervalL E (toCircleL E f) = f := by
  apply Lp.ext
  filter_upwards [toIntervalL_ae (toCircleL E f),
    cover_measurePreserving.quasiMeasurePreserving.ae_eq_comp (toCircleL_ae f),
    ae_restrict_mem measurableSet_Ioo] with t h₁ h₂ ht
  exact h₁.trans (by simpa only [Function.comp_apply, sectionPoint_eq (Ioo_subset_Ioc_self ht)] using h₂)

theorem toCircle_toInterval {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : CircleLp E) : toCircleL E (toIntervalL E f) = f := by
  apply Lp.ext
  filter_upwards [toCircleL_ae (toIntervalL E f),
    section_measurePreserving.quasiMeasurePreserving.ae_eq_comp (toIntervalL_ae f)] with x h₁ h₂
  exact h₁.trans (by simpa only [Function.comp_apply, sectionPoint_coe] using h₂)

def translation (a : Phase) : C(Phase, Phase) :=
  ⟨fun x => a + x, continuous_const.add continuous_id⟩

theorem translation_apply (a x : Phase) : translation a x = a + x := rfl

theorem translation_measurePreserving (a : Phase) :
    MeasurePreserving (translation a) (volume : Measure Phase) volume :=
  measurePreserving_add_left volume a

theorem translation_continuous : Continuous translation :=
  ContinuousMap.continuous_of_continuous_uncurry _ (continuous_fst.add continuous_snd)

def translateL (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (a : Phase) :
    CircleLp E →L[ℝ] CircleLp E :=
  (Lp.compMeasurePreservingₗᵢ ℝ (translation a) (translation_measurePreserving a)).toContinuousLinearMap

theorem translateL_ae {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : CircleLp E) (a : Phase) : translateL E a f =ᵐ[volume] fun x => f (a + x) :=
  Lp.coeFn_compMeasurePreserving f (translation_measurePreserving a)

theorem translateL_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : CircleLp E) (a : Phase) : ‖translateL E a f‖ = ‖f‖ :=
  Lp.norm_compMeasurePreserving f (translation_measurePreserving a)

theorem translateL_joint_continuous (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Continuous (fun p : CircleLp E × Phase => translateL E p.2 p.1) :=
  continuous_fst.compMeasurePreservingLp (translation_continuous.comp continuous_snd)
    (fun _ => translation_measurePreserving _) (by norm_num)

end

end Finsler.CircleLpTransfer
