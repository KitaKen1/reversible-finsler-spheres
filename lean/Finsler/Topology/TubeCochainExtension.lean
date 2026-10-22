module

public import Finsler.Topology.SupportedCap
public import Finsler.Topology.SupportedCapNaturality
public import Finsler.Topology.RelativeCupCochain
public import Finsler.Topology.CupOne

/-! Literal extension by zero of a tube cochain, defined on the actual
singular-simplex basis. The extension need not be globally closed. Its
restriction is the original tube cochain, so the cup coboundary and the
cup-one error term vanish on every simplex lying wholly in that tube. -/

@[expose] public section
namespace Finsler.TubeCochainExtension

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
attribute [local instance] Classical.propDecidable

variable (X : TopCat.{0}) (O : Set X)

def extend (n : ℕ) (ψ : singularCochainGroup (ZMod 2) (TopCat.of O) n) :
    singularCochainGroup (ZMod 2) X n := by
  classical
  exact Cofan.IsColimit.desc ((TopCat.toSSet.obj X).isColimitChainComplexXCofan coeff n)
    fun σ => if hσ : Set.range (X.toSSetObjEquiv _ σ) ⊆ O then
      (TopCat.toSSet.obj (TopCat.of O)).ιChainComplex (SupportedCap.simplexLift X O σ hσ) ≫ ψ
    else 0

theorem on_simplex (n : ℕ) (ψ : singularCochainGroup (ZMod 2) (TopCat.of O) n)
    (σ : TopCat.toSSet.obj X _⦋n⦌) :
    (TopCat.toSSet.obj X).ιChainComplex σ ≫ extend X O n ψ =
      if hσ : Set.range (X.toSSetObjEquiv _ σ) ⊆ O then
        (TopCat.toSSet.obj (TopCat.of O)).ιChainComplex (SupportedCap.simplexLift X O σ hσ) ≫ ψ
      else 0 := by
  classical
  exact Cofan.IsColimit.fac _ _ σ

theorem included_range {n : ℕ} (σ : TopCat.toSSet.obj (TopCat.of O) _⦋n⦌) :
    Set.range (X.toSSetObjEquiv _
      ((TopCat.toSSet.map (SupportedCap.subspaceMap X O)).app _ σ)) ⊆ O := by
  rw [TauCeti.TopCat.toSSetObjEquiv_toSSet_map_app]
  rintro _ ⟨t, rfl⟩
  exact ((TopCat.of O).toSSetObjEquiv _ σ t).property

theorem lift_included {n : ℕ} (σ : TopCat.toSSet.obj (TopCat.of O) _⦋n⦌) :
    SupportedCap.simplexLift X O
      ((TopCat.toSSet.map (SupportedCap.subspaceMap X O)).app _ σ) (included_range X O σ) = σ := by
  apply ((TopCat.of O).toSSetObjEquiv _).injective
  ext t : 1
  simp only [SupportedCap.simplexLift, Equiv.apply_symm_apply]
  apply Subtype.ext
  change (X.toSSetObjEquiv _ ((TopCat.toSSet.map (SupportedCap.subspaceMap X O)).app _ σ) t) = _
  rw [TauCeti.TopCat.toSSetObjEquiv_toSSet_map_app]
  rfl

theorem restriction (n : ℕ) (ψ : singularCochainGroup (ZMod 2) (TopCat.of O) n) :
    cochainPullback (SupportedCap.subspaceMap X O) n (extend X O n ψ) = ψ := by
  classical
  apply SSet.chainComplex_hom_ext (X := TopCat.toSSet.obj (TopCat.of O)) (R := coeff)
  intro σ
  change (TopCat.toSSet.obj (TopCat.of O)).ιChainComplex σ ≫
      ((SSet.chainComplexMap (TopCat.toSSet.map (SupportedCap.subspaceMap X O)) coeff).f n ≫
        extend X O n ψ) = _
  rw [SSet.ι_chainComplexMap_f_assoc, on_simplex,
    dite_eq_left (included_range X O σ), lift_included]

theorem local_closed (n : ℕ) (ψ : singularCochainGroup (ZMod 2) (TopCat.of O) n)
    (hψ : cochainCoboundary (ZMod 2) (TopCat.of O) n ψ = 0) :
    cochainPullback (SupportedCap.subspaceMap X O) (n + 1)
      (cochainCoboundary (ZMod 2) X n (extend X O n ψ)) = 0 := by
  have he := ConcreteCategory.congr_hom
    ((singularCochainComplexZMod2.map (SupportedCap.subspaceMap X O).op).comm n (n + 1))
    (extend X O n ψ)
  change cochainCoboundary (ZMod 2) (TopCat.of O) n
      (cochainPullback (SupportedCap.subspaceMap X O) n (extend X O n ψ)) =
    cochainPullback (SupportedCap.subspaceMap X O) (n + 1)
      (cochainCoboundary (ZMod 2) X n (extend X O n ψ)) at he
  rw [restriction, hψ] at he
  exact he.symm

theorem cup_local_closed (p q : ℕ) (φ : singularCochainGroup (ZMod 2) X p)
    (hφ : cochainCoboundary (ZMod 2) X p φ = 0)
    (ψ : singularCochainGroup (ZMod 2) (TopCat.of O) q)
    (hψ : cochainCoboundary (ZMod 2) (TopCat.of O) q ψ = 0) :
    cochainPullback (SupportedCap.subspaceMap X O) (p + q + 1)
      (cochainCoboundary (ZMod 2) X (p + q) (cochainCup p q φ (extend X O q ψ))) = 0 := by
  have he := ConcreteCategory.congr_hom
    ((singularCochainComplexZMod2.map (SupportedCap.subspaceMap X O).op).comm (p + q) (p + q + 1))
    (cochainCup p q φ (extend X O q ψ))
  change cochainCoboundary (ZMod 2) (TopCat.of O) (p + q)
      (cochainPullback (SupportedCap.subspaceMap X O) (p + q) (cochainCup p q φ (extend X O q ψ))) = _ at he
  rw [cochainCup_naturality, restriction] at he
  exact he.symm.trans (cochainCupZMod2_respects_cocycles p q _ _
    (pullback_closed (SupportedCap.subspaceMap X O) p φ hφ) hψ)

theorem cupOne_error_zero (p q r m : ℕ) (h : r + (p + q + 1) = m + 1)
    (σ : singularCochainGroup (ZMod 2) X r)
    (φ : singularCochainGroup (ZMod 2) X p) (hφ : cochainCoboundary (ZMod 2) X p φ = 0)
    (ψ : singularCochainGroup (ZMod 2) (TopCat.of O) q)
    (hψ : cochainCoboundary (ZMod 2) (TopCat.of O) q ψ = 0) :
    cochainPullback (SupportedCap.subspaceMap X O) m
      (CupOne.cupOne X r (p + q + 1) m h σ
        (cochainCoboundary (ZMod 2) X (p + q) (cochainCup p q φ (extend X O q ψ)))) = 0 :=
  CupOne.restriction_zero (SupportedCap.subspaceMap X O) r (p + q + 1) m h σ _
    (Or.inr (cup_local_closed X O p q φ hφ ψ hψ))

end
end Finsler.TubeCochainExtension
