module

public import Finsler.Loop.LocalNativeBallCupCorrection
public import Finsler.Loop.LocalizedCutEvaluationCochain

/-! Connect the ACTUAL whole-ball tested/cup primitive calculation
to the SAME ORIGINAL GeometricTimeCupCochain.splitCup on every real
smaller near tube. Both original tested and retained maps restrict
EXACTLY, and retained evaluation is the actual first sphere point.
No native first-Thom cap or supported-global class comparison is
silently inferred from this literal pre-cap cochain identity. -/
@[expose] public section
namespace Finsler.LocalNativeBallOriginalSplit
open CategoryTheory SphereOddDegree Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.MeridianLoopFamily
open Finsler.CochainComparison Finsler.SupportedCapNaturality Finsler.BorelLoop
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 900000

abbrev nearInclusion {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) (r : ℝ) :=
  SupportedCap.subspaceMap (LocalNativeBallCut.space P v₀) (LocalNativeBallCut.near P v₀ b r)

theorem retained_firstPoint {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) :
    LocalNativeBallCut.retainedH1 P v₀ b ≫ MeridianThetaCutCoefficient.evaluation n =
      LocalNativeBallCupCorrection.firstPoint P v₀ := by
  apply TopCat.ext
  intro z
  apply Subtype.ext
  have hx := congrArg Prod.fst (LocalNativeBallCut.self_evaluation P v₀ b z)
  change H1FiberBase.point (LocalNativeBallCut.cutParameters P v₀ b z).2 = z.1.val at hx
  exact (H1SelfCutNeighborhood.basepoint_right (LocalNativeBallCut.toTube P v₀ b z)).trans (congrArg Subtype.val hx)

theorem evaluation_pullback (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {η : ℝ} (hη : 0 < η) :
    cochainPullback (LocalNativeBallCut.retainedH1 P v₀ b) (m + 1)
      (LocalizedCutEvaluationCochain.loopCocycle (m + 1) (by omega) (LocalNativeBallCut.center P v₀) hη) =
      LocalNativeBallCupCorrection.evaluationCocycle m P v₀ hη := by
  rw [LocalizedCutEvaluationCochain.loopCocycle, ← pullback_comp, retained_firstPoint]
  rfl

theorem tested_cochain_restrict {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) {r : ℝ} (hr : r ≤ 1)
    (p : ℕ) (T : singularCochainGroup (ZMod 2) (Loops n) p) :
    cochainPullback (LocalNativeBallCut.toNeighborhood P v₀ b r) p
      (cochainPullback (TopCat.ofHom (SupportedSelfCut.tested n hr)) p T) =
      cochainPullback (nearInclusion P v₀ b r) p (cochainPullback (LocalNativeBallCut.testedH1 P v₀ b) p T) := by
  rw [← pullback_comp, ← LocalNativeBallCut.tested_restrict, pullback_comp]

theorem retained_cochain_restrict {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) {r : ℝ} (hr : r ≤ 1)
    (p : ℕ) (T : singularCochainGroup (ZMod 2) (Loops n) p) :
    cochainPullback (LocalNativeBallCut.toNeighborhood P v₀ b r) p
      (cochainPullback (TopCat.ofHom (SupportedSelfCut.retained n hr)) p T) =
      cochainPullback (nearInclusion P v₀ b r) p (cochainPullback (LocalNativeBallCut.retainedH1 P v₀ b) p T) := by
  rw [← pullback_comp, ← LocalNativeBallCut.retained_restrict, pullback_comp]

theorem original_split_pullback (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3)
    {r η : ℝ} (hr : r ≤ 1) (hη : 0 < η) :
    cochainPullback (LocalNativeBallCut.toNeighborhood P v₀ b r) (m + (m + 1))
      (GeometricTimeCupCochain.splitCup m m hr (classRepr (Loops (m + 1)) m (MeridianLoopClass.H1TransgressionClass m))
        (m + 1) (LocalizedCutEvaluationCochain.loopCocycle (m + 1) (by omega) (LocalNativeBallCut.center P v₀) hη)) =
      cochainPullback (nearInclusion P v₀ b r) (m + (m + 1))
        (cochainCup m (m + 1) (LocalNativeBallPrimitive.testedCocycle m P v₀ b)
          (LocalNativeBallCupCorrection.evaluationCocycle m P v₀ hη)) := by
  dsimp only [GeometricTimeCupCochain.splitCup, NormalizedSelfCut.testedCocycle]
  rw [cochainCup_naturality, tested_cochain_restrict, retained_cochain_restrict, evaluation_pullback]
  exact (cochainCup_naturality (nearInclusion P v₀ b r) m (m + 1)
    (LocalNativeBallPrimitive.testedCocycle m P v₀ b) (LocalNativeBallCupCorrection.evaluationCocycle m P v₀ hη)).symm

end
end Finsler.LocalNativeBallOriginalSplit
