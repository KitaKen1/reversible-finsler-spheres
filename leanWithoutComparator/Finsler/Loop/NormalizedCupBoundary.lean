module

public import Finsler.Loop.FirstInputRotationNormalizedGamma
public import Finsler.Loop.CupCapOrder
import all Finsler.Loop.FirstInputRotationNormalizedGamma

/-! The actual normalization primitive, cupped with a closed right
factor, bounds the change of the first cup factor. All total degrees
are explicit so the original annular convention can be retained. -/

@[expose] public section
namespace Finsler.NormalizedCupBoundary

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1200000

theorem cup_zero_right (X : TopCat.{0}) (a n D : ℕ) (hD : a + n = D)
    (φ : singularCochainGroup (ZMod 2) X a) : CupOne.cup X a n D hD φ 0 = 0 :=
  map_zero ((TauCeti.ChainComplex.cupCochain (ZMod 2) (Finsler.RelativeCap.diagonal X)
    (ρ_ coeff).hom a n D hD) φ)

theorem cup_sub_left (X : TopCat.{0}) (a n D : ℕ) (hD : a + n = D)
    (φ ψ : singularCochainGroup (ZMod 2) X a) (σ : singularCochainGroup (ZMod 2) X n) :
    CupOne.cup X a n D hD (φ - ψ) σ = CupOne.cup X a n D hD φ σ - CupOne.cup X a n D hD ψ σ :=
  map_sub ((TauCeti.ChainComplex.cupCochain (ZMod 2) (Finsler.RelativeCap.diagonal X)
    (ρ_ coeff).hom a n D hD).flip σ) φ ψ

theorem boundary_right_closed (X : TopCat.{0}) (a n D : ℕ) (hD : a + n = D)
    (φ : singularCochainGroup (ZMod 2) X a) (σ : singularCochainGroup (ZMod 2) X n)
    (hσ : cochainCoboundary (ZMod 2) X n σ = 0) :
    cochainCoboundary (ZMod 2) X D (CupOne.cup X a n D hD φ σ) =
      CupOne.cup X (a + 1) n (D + 1) (by omega) (cochainCoboundary (ZMod 2) X a φ) σ := by
  have hb := TauCeti.ChainComplex.d_comp_cupCochain (k := ZMod 2)
    (Finsler.RelativeCap.diagonal X) (ρ_ coeff).hom a n D hD φ σ
  change cochainCoboundary (ZMod 2) X D (CupOne.cup X a n D hD φ σ) =
    CupOne.cup X (a + 1) n (D + 1) (by omega) (cochainCoboundary (ZMod 2) X a φ) σ +
      ((-1 : ℤ) ^ a) • CupOne.cup X a (n + 1) (D + 1) (by omega) φ
        (cochainCoboundary (ZMod 2) X n σ) at hb
  rw [hσ, cup_zero_right, smul_zero, add_zero] at hb
  exact hb

theorem normalization_boundary (X : TopCat.{0}) (a d n D : ℕ) (ha : a + 1 = d) (hD : a + n = D)
    (φ : singularCochainGroup (ZMod 2) X d) (σ : singularCochainGroup (ZMod 2) X n)
    (hφ : cochainCoboundary (ZMod 2) X d φ = 0)
    (hσ : cochainCoboundary (ZMod 2) X n σ = 0) :
    cochainCoboundary (ZMod 2) X D (CupOne.cup X a n D hD
      ((SingularNormalization.projectorHomotopy X).hom a d ≫ φ) σ) =
    CupOne.cup X d n (D + 1) (by omega) (SingularNormalization.normalize X d φ) σ -
      CupOne.cup X d n (D + 1) (by omega) φ σ := by
  subst d
  rw [boundary_right_closed X a n D hD _ σ hσ]
  have hp := FirstInputRotationNormalizedGamma.primitive_boundary_regrade X a (a + 1) rfl φ hφ
  simp only [eqToHom_refl, Category.id_comp] at hp
  rw [hp, cup_sub_left]

end
end Finsler.NormalizedCupBoundary
