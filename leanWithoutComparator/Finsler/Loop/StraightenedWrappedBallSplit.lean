module

public import Finsler.Loop.NativeCutPointSwap

/-! Actual original wrapped cut after exchanging the ball coordinates.
Its normalized Thom cochain and near/exterior covers are those of the
OLD local cap, and its retained evaluation is the first sphere point.
The actual ORIGINAL split cochain restricts to the actual new tested
cocycle cupped with the SAME existing localized evaluation cocycle. -/
@[expose] public section
namespace Finsler.StraightenedWrappedBallSplit
open CategoryTheory SphereOddDegree Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.MeridianLoopFamily
open Finsler.CochainComparison Finsler.SupportedCapNaturality Finsler.BorelLoop
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1100000

def testedH1 {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) :=
  NativeCutPointSwap.ballSwap P v₀ ≫ LocalNativeWrappedBallCut.testedH1 P v₀ b

def retainedH1 {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) :=
  NativeCutPointSwap.ballSwap P v₀ ≫ LocalNativeWrappedBallCut.retainedH1 P v₀ b

def toTube {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) :=
  NativeCutPointSwap.ballSwap P v₀ ≫ LocalNativeWrappedBallCut.toTube P v₀ b

theorem maps_exterior {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) (ρ : ℝ) :
    Set.MapsTo (NativeCutPointSwap.straightenedCut P v₀ b) (LocalNativeSupportedCap.exterior P v₀ b ρ)
      (SupportedSelfCut.exterior n ρ) := by
  intro z hz
  change ρ < SupportedSelfCut.distance n (NativeCutPointSwap.straightenedCut P v₀ b z)
  rw [NativeCutPointSwap.straightened_distance]
  exact hz

theorem maps_near {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) (r : ℝ) :
    Set.MapsTo (NativeCutPointSwap.straightenedCut P v₀ b) (LocalNativeBallCut.near P v₀ b r)
      (SupportedSelfCut.neighborhood n r) := by
  intro z hz
  change SupportedSelfCut.distance n (NativeCutPointSwap.straightenedCut P v₀ b z) < r
  rw [NativeCutPointSwap.straightened_distance]
  exact hz

def toNeighborhood {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) (r : ℝ) :=
  restriction (NativeCutPointSwap.straightenedCut P v₀ b) (LocalNativeBallCut.near P v₀ b r)
    (SupportedSelfCut.neighborhood n r) (maps_near P v₀ b r)

theorem tested_restrict {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) {r : ℝ} (hr : r ≤ 1) :
    LocalNativeBallOriginalSplit.nearInclusion P v₀ b r ≫ testedH1 P v₀ b =
      toNeighborhood P v₀ b r ≫ TopCat.ofHom (SupportedSelfCut.tested n hr) := by
  apply TopCat.ext
  intro z
  rfl

theorem retained_restrict {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) {r : ℝ} (hr : r ≤ 1) :
    LocalNativeBallOriginalSplit.nearInclusion P v₀ b r ≫ retainedH1 P v₀ b =
      toNeighborhood P v₀ b r ≫ TopCat.ofHom (SupportedSelfCut.retained n hr) := by
  apply TopCat.ext
  intro z
  rfl

theorem retained_firstPoint {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) :
    retainedH1 P v₀ b ≫ MeridianThetaCutCoefficient.evaluation n = LocalNativeBallCupCorrection.firstPoint P v₀ := by
  apply TopCat.ext
  intro z
  apply Subtype.ext
  have hx := congrArg Prod.fst (LocalNativeWrappedBallCut.self_evaluation P v₀ b (NativeCutPointSwap.ballSwap P v₀ z))
  change H1FiberBase.point (NativeCutPointSwap.straightenedCut P v₀ b z).2 = z.1.val at hx
  exact (H1SelfCutNeighborhood.basepoint_right (toTube P v₀ b z)).trans (congrArg Subtype.val hx)

theorem evaluation_pullback (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {η : ℝ} (hη : 0 < η) :
    cochainPullback (retainedH1 P v₀ b) (m + 1)
      (LocalizedCutEvaluationCochain.loopCocycle (m + 1) (by omega) (LocalNativeBallCut.center P v₀) hη) =
      LocalNativeBallCupCorrection.evaluationCocycle m P v₀ hη := by
  rw [LocalizedCutEvaluationCochain.loopCocycle, ← pullback_comp, retained_firstPoint]
  rfl

theorem tested_cochain_restrict {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) {r : ℝ} (hr : r ≤ 1)
    (p : ℕ) (T : singularCochainGroup (ZMod 2) (Loops n) p) :
    cochainPullback (toNeighborhood P v₀ b r) p
      (cochainPullback (TopCat.ofHom (SupportedSelfCut.tested n hr)) p T) =
      cochainPullback (LocalNativeBallOriginalSplit.nearInclusion P v₀ b r) p (cochainPullback (testedH1 P v₀ b) p T) := by
  rw [← pullback_comp, ← tested_restrict, pullback_comp]

theorem retained_cochain_restrict {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) {r : ℝ} (hr : r ≤ 1)
    (p : ℕ) (T : singularCochainGroup (ZMod 2) (Loops n) p) :
    cochainPullback (toNeighborhood P v₀ b r) p
      (cochainPullback (TopCat.ofHom (SupportedSelfCut.retained n hr)) p T) =
      cochainPullback (LocalNativeBallOriginalSplit.nearInclusion P v₀ b r) p (cochainPullback (retainedH1 P v₀ b) p T) := by
  rw [← pullback_comp, ← retained_restrict, pullback_comp]

theorem original_split_pullback (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3)
    {r η : ℝ} (hr : r ≤ 1) (hη : 0 < η) :
    cochainPullback (toNeighborhood P v₀ b r) (m + (m + 1))
      (GeometricTimeCupCochain.splitCup m m hr (classRepr (Loops (m + 1)) m (MeridianLoopClass.H1TransgressionClass m))
        (m + 1) (LocalizedCutEvaluationCochain.loopCocycle (m + 1) (by omega) (LocalNativeBallCut.center P v₀) hη)) =
      cochainPullback (LocalNativeBallOriginalSplit.nearInclusion P v₀ b r) (m + (m + 1))
        (cochainCup m (m + 1)
          (cochainPullback (testedH1 P v₀ b) m (classRepr (Loops (m + 1)) m (MeridianLoopClass.H1TransgressionClass m)))
          (LocalNativeBallCupCorrection.evaluationCocycle m P v₀ hη)) := by
  dsimp only [GeometricTimeCupCochain.splitCup, NormalizedSelfCut.testedCocycle]
  rw [cochainCup_naturality, tested_cochain_restrict, retained_cochain_restrict, evaluation_pullback]
  exact (cochainCup_naturality (LocalNativeBallOriginalSplit.nearInclusion P v₀ b r) m (m + 1) _ _).symm

end
end Finsler.StraightenedWrappedBallSplit
