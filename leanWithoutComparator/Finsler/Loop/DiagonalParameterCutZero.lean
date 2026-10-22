module

public import Finsler.Loop.NativeGlobalSquareFaceZero

/-! The ORIGINAL complete parameter cap vanishes on every genuine
diagonal family. The proof uses the actual normalized Thom support
and original small approximation, without replacing the cut. -/
@[expose] public section
namespace Finsler.DiagonalParameterCutZero
open CategoryTheory CategoryTheory.Limits SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.MeridianLoopFamily Finsler.CochainComparison
open Finsler.BorelLoop Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

def diagonal (n : ℕ) : Set (SelfCutThomCocycle.parameters n) :=
  {z | H1FiberBase.point z.2 = H1SelfCutNeighborhood.endpoint z}

theorem thom_zero (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    cochainPullback (SupportedCap.subspaceMap (SelfCutThomCocycle.parameters n) (diagonal n)) n
      (NormalizedSelfCut.cocycle n hn hρ) = 0 := by
  rw [NormalizedSelfCut.cocycle, ← pullback_comp]
  apply NormalizedDiagonalCocycle.pullback_zero_of_diagonal hn hρ
  intro z
  exact z.property

theorem family_zero (m p : ℕ) (Q : Sphere (m + 1)) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η)
    (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p)
    {X : TopCat.{0}} (f : X ⟶ SelfCutThomCocycle.parameters (m + 1))
    (hf : ∀ x, H1FiberBase.point (f x).2 = H1SelfCutNeighborhood.endpoint (f x)) :
    cochainPullback f ((m + 1) + (p + (m + 1)))
      (LocalizedParameterCutCochain.cochain m p Q hρ hρr hr hη T) = 0 := by
  have hz := SelfCutEndpoints.cut_map_zero (SupportedSelfCut.exterior (m + 1) ρ) (SupportedSelfCut.neighborhood (m + 1) r)
    (diagonal (m + 1)) (SupportedSelfCut.exterior_open (m + 1) ρ) (SupportedSelfCut.neighborhood_open (m + 1) r)
    (SupportedSelfCut.cover (m + 1) hρr) (m + 1) (p + (m + 1)) (NormalizedSelfCut.cocycle (m + 1) (by omega) hρ)
    (NormalizedSelfCut.cocycle_supported (m + 1) (by omega) hρ) (thom_zero (m + 1) (by omega) hρ) f hf
  change (push f).f _ ≫ ((NormalizedSelfCut.operation (m + 1) (by omega) hρ hρr).component (p + (m + 1)) ≫ _) = 0
  have hz' : (push f).f ((m + 1) + (p + (m + 1))) ≫
      (NormalizedSelfCut.operation (m + 1) (by omega) hρ hρr).component (p + (m + 1)) = 0 := hz
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun a => a ≫ GeometricTimeCupCochain.splitCup m p hr T (m + 1)
      (LocalizedCutEvaluationCochain.loopCocycle (m + 1) (by omega) Q hη)) hz').trans zero_comp)

end
end Finsler.DiagonalParameterCutZero
