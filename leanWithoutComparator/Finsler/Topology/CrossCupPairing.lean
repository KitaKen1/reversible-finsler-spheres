module

public import Finsler.Topology.CrossCupComparison

/-! Evaluate the existing projection-cup on the actual external homology product.
Both matching bidegrees and mismatched bidegrees use the actual cochains. -/

@[expose] public section

namespace Finsler.CrossCupPairing

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.ChainEvaluation

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

def pairing (X : TopCat.{0}) (k : ℕ) (a : cohomologyZMod2 X k) : PoolCap.homology X k ⟶ coeff :=
  ModuleCat.ofHom ((kroneckerMap X k).hom a)

theorem cochain_pairing (X Y : TopCat.{0}) (p q : ℕ)
    (φ : singularCochainGroup (ZMod 2) X p) (ψ : singularCochainGroup (ZMod 2) Y q)
    (hφ : cochainCoboundary (ZMod 2) X p φ = 0)
    (hψ : cochainCoboundary (ZMod 2) Y q ψ = 0) :
    evaluation (chains (X ⊗ Y)) (p + q) (SingularCrossEvaluation.cochain X Y p q φ ψ)
      (SingularCrossEvaluation.cochain_closed X Y p q φ ψ hφ hψ) =
      pairing (X ⊗ Y) (p + q) (cupZMod2
        ((cohPullback (fst X Y) p).hom (cocycleClass X p φ hφ))
        ((cohPullback (snd X Y) q).hom (cocycleClass Y q ψ hψ))) := by
  let φ' := cochainPullback (fst X Y) p φ
  let ψ' := cochainPullback (snd X Y) q ψ
  have hφ' := cochainPullback_cocycle (fst X Y) p φ hφ
  have hψ' := cochainPullback_cocycle (snd X Y) q ψ hψ
  have hc := cochainCupZMod2_respects_cocycles p q φ' ψ' hφ' hψ'
  have he : evaluation (chains (X ⊗ Y)) (p + q)
      (SingularCrossEvaluation.cochain X Y p q φ ψ)
        (SingularCrossEvaluation.cochain_closed X Y p q φ ψ hφ hψ) =
      evaluation (chains (X ⊗ Y)) (p + q) (cochainCup p q φ' ψ') hc := by
    apply (cancel_epi ((chains (X ⊗ Y)).homologyπ (p + q))).mp
    rw [homologyπ_evaluation, homologyπ_evaluation]
    exact congrArg ((chains (X ⊗ Y)).iCycles (p + q) ≫ ·)
      (CrossCupComparison.cochain_comparison X Y p q φ ψ)
  calc
    _ = evaluation (chains (X ⊗ Y)) (p + q) (cochainCup p q φ' ψ') hc := he
    _ = pairing (X ⊗ Y) (p + q) (cocycleClass (X ⊗ Y) (p + q) (cochainCup p q φ' ψ') hc) :=
      ChainEvaluation.pool_comparison (X ⊗ Y) (p + q) (cochainCup p q φ' ψ') hc
    _ = _ := by rw [cohPullback_cocycleClass, cohPullback_cocycleClass, cupZMod2_mk]

theorem cross_cup_pairing (X Y : TopCat.{0}) (p q : ℕ)
    (a : cohomologyZMod2 X p) (b : cohomologyZMod2 Y q) :
    FilteredBilinearLoopProduct.crossMap X Y p q (p + q) rfl ≫
      pairing (X ⊗ Y) (p + q)
        (cupZMod2 ((cohPullback (fst X Y) p).hom a) ((cohPullback (snd X Y) q).hom b)) =
      (pairing X p a ⊗ₘ pairing Y q b) ≫ (ρ_ coeff).hom := by
  obtain ⟨φ, hφ, rfl⟩ := cocycleClass_surjective X p a
  obtain ⟨ψ, hψ, rfl⟩ := cocycleClass_surjective Y q b
  calc
    _ = FilteredBilinearLoopProduct.crossMap X Y p q (p + q) rfl ≫
        evaluation (chains (X ⊗ Y)) (p + q) (SingularCrossEvaluation.cochain X Y p q φ ψ)
          (SingularCrossEvaluation.cochain_closed X Y p q φ ψ hφ hψ) :=
      congrArg (FilteredBilinearLoopProduct.crossMap X Y p q (p + q) rfl ≫ ·)
        (cochain_pairing X Y p q φ ψ hφ hψ).symm
    _ = (evaluation (chains X) p φ hφ ⊗ₘ evaluation (chains Y) q ψ hψ) ≫ (ρ_ coeff).hom :=
      SingularCrossEvaluation.cross_evaluation X Y p q φ ψ hφ hψ
    _ = _ := congrArg₂ (fun f g => (f ⊗ₘ g) ≫ (ρ_ coeff).hom)
      (ChainEvaluation.pool_comparison X p φ hφ) (ChainEvaluation.pool_comparison Y q ψ hψ)

theorem cross_cup_pairing_of_ne (X Y : TopCat.{0}) (p q i j : ℕ)
    (h : i + j = p + q) (hi : i ≠ p)
    (a : cohomologyZMod2 X p) (b : cohomologyZMod2 Y q) :
    FilteredBilinearLoopProduct.crossMap X Y i j (p + q) h ≫
      pairing (X ⊗ Y) (p + q)
        (cupZMod2 ((cohPullback (fst X Y) p).hom a) ((cohPullback (snd X Y) q).hom b)) = 0 := by
  obtain ⟨φ, hφ, rfl⟩ := cocycleClass_surjective X p a
  obtain ⟨ψ, hψ, rfl⟩ := cocycleClass_surjective Y q b
  calc
    _ = FilteredBilinearLoopProduct.crossMap X Y i j (p + q) h ≫
        evaluation (chains (X ⊗ Y)) (p + q) (SingularCrossEvaluation.cochain X Y p q φ ψ)
          (SingularCrossEvaluation.cochain_closed X Y p q φ ψ hφ hψ) :=
      congrArg (FilteredBilinearLoopProduct.crossMap X Y i j (p + q) h ≫ ·)
        (cochain_pairing X Y p q φ ψ hφ hψ).symm
    _ = 0 := SingularCrossEvaluation.cross_evaluation_of_ne X Y p q i j h hi φ ψ hφ hψ

theorem cross_cup_apply (X Y : TopCat.{0}) (p q : ℕ)
    (a : cohomologyZMod2 X p) (b : cohomologyZMod2 Y q)
    (x : PoolCap.homology X p) (y : PoolCap.homology Y q) :
    (kroneckerMap (X ⊗ Y) (p + q)).hom
        (cupZMod2 ((cohPullback (fst X Y) p).hom a) ((cohPullback (snd X Y) q).hom b))
          (FilteredBilinearLoopProduct.cross X Y p q (p + q) rfl x y) =
      (kroneckerMap X p).hom a x * (kroneckerMap Y q).hom b y := by
  have he := ConcreteCategory.congr_hom (cross_cup_pairing X Y p q a b) (x ⊗ₜ[ZMod 2] y)
  change _ = (ρ_ coeff).hom.hom (((pairing X p a) ⊗ₘ (pairing Y q b)).hom (x ⊗ₜ[ZMod 2] y)) at he
  rw [ModuleCat.MonoidalCategory.tensorHom_tmul, ModuleCat.MonoidalCategory.rightUnitor_hom_apply] at he
  exact he.trans (mul_comm _ _)


end
end Finsler.CrossCupPairing
