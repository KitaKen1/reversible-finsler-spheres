module

public import Finsler.Topology.PrismShuffle
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.HomotopyInvariance

/-! The genuine simplicial homotopy prism equals the recursively shuffled
simplex-times-interval rectangle, before passing to homology. -/

@[expose] public section
namespace Finsler.PrismRectangle

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology
open Finsler.CochainComparison
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

private theorem sign_smul {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (p : ℕ) (v : V) : ((-1 : ℤ) ^ p) • v = v := by
  have hs : (((-1 : ℤ) ^ p : ℤ) : ZMod 2) = 1 := by
    simp only [Int.cast_pow, Int.cast_neg, Int.cast_one, ZMod.neg_eq_self_mod_two, one_pow]
  rw [← Int.cast_smul_eq_zsmul (ZMod 2), hs, one_smul]

private theorem neg_eq_self {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (v : V) : -v = v := by
  simpa only [pow_one, neg_one_zsmul] using sign_smul 1 v

theorem linear_generator {A B : Type} (u : A ⟶ B) (a : A) :
    Sigma.ι (fun _ : A => coeff) a ≫ (sigmaConst.obj coeff).map u =
      Sigma.ι (fun _ : B => coeff) (u a) := by
  dsimp [sigmaConst, Sigma.map']
  simp

theorem prism_simplex {X Y : SSet.{0}} {f g : X ⟶ Y} (H : SSet.Homotopy f g)
    (q : ℕ) (σ : X _⦋q⦌) :
    X.ιChainComplex σ ≫ (H.chainComplexMap coeff).hom q (q + 1) =
      SSet.shuffleChain coeff q 1 (q + 1) rfl ≫
        (SSet.chainComplexMap (SSet.yonedaEquiv.symm σ ▷ Δ[1] ≫ H.h) coeff).f (q + 1) := by
  change X.ιChainComplex σ ≫ SimplicialObject.Homotopy.ToChainHomotopy.hom
    (H.toSimplicialObjectHomotopy.whiskerRight (sigmaConst.obj coeff)) q (q + 1) = _
  rw [SimplicialObject.Homotopy.ToChainHomotopy.hom_eq]
  simp only [Preadditive.comp_neg, neg_eq_self, Preadditive.comp_sum,
    Preadditive.comp_zsmul, sign_smul, PrismShuffle.shuffle_one, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro i _
  change Sigma.ι (fun _ : X _⦋q⦌ => coeff) σ ≫
      (sigmaConst.obj coeff).map (H.toSimplicialObjectHomotopy.h i) = _
  rw [linear_generator, SSet.ι_chainComplexMap_f]
  rfl

def rectangle {X Y : SSet.{0}} {f g : X ⟶ Y} (H : SSet.Homotopy f g) (q : ℕ) :
    (X.chainComplex coeff).X q ⟶ (Y.chainComplex coeff).X (q + 1) :=
  Cofan.IsColimit.desc (X.isColimitChainComplexXCofan coeff q) fun σ =>
    SSet.shuffleChain coeff q 1 (q + 1) rfl ≫
      (SSet.chainComplexMap (SSet.yonedaEquiv.symm σ ▷ Δ[1] ≫ H.h) coeff).f (q + 1)

theorem rectangle_eq_prism {X Y : SSet.{0}} {f g : X ⟶ Y} (H : SSet.Homotopy f g)
    (q : ℕ) : rectangle H q = (H.chainComplexMap coeff).hom q (q + 1) := by
  apply SSet.chainComplex_hom_ext (X := X) (R := coeff)
  intro σ
  have hc : X.ιChainComplex σ ≫ rectangle H q =
      SSet.shuffleChain coeff q 1 (q + 1) rfl ≫
        (SSet.chainComplexMap (SSet.yonedaEquiv.symm σ ▷ Δ[1] ≫ H.h) coeff).f (q + 1) :=
    Cofan.IsColimit.fac _ _ σ
  exact hc.trans (prism_simplex H q σ).symm

end
end Finsler.PrismRectangle
