module

public import Finsler.Topology.TubeCochainExtension

/-! Literal pullback of a genuine zero extension to the inverse-image
domain. This supplies endpoint zero statements without a globally
defined partial family or a global cocycle extension. -/

@[expose] public section
namespace Finsler.TubeExtensionPullback

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {X Y : TopCat.{0}} (f : Y ⟶ X) (K : Set X)

theorem parent_iff {p : ℕ} (σ : TopCat.toSSet.obj Y _⦋p⦌) :
    Set.range (X.toSSetObjEquiv _ ((TopCat.toSSet.map f).app _ σ)) ⊆ K ↔
      Set.range (Y.toSSetObjEquiv _ σ) ⊆ f ⁻¹' K := by
  rw [TauCeti.TopCat.toSSetObjEquiv_toSSet_map_app]
  constructor
  · intro h z hz
    obtain ⟨t, rfl⟩ := hz
    exact h ⟨t, rfl⟩
  · intro h z hz
    obtain ⟨t, rfl⟩ := hz
    exact h ⟨t, rfl⟩

theorem lift_natural {p : ℕ} (σ : TopCat.toSSet.obj Y _⦋p⦌)
    (hσ : Set.range (Y.toSSetObjEquiv _ σ) ⊆ f ⁻¹' K) :
    (TopCat.toSSet.map (restriction f (f ⁻¹' K) K (fun _ h => h))).app _
      (SupportedCap.simplexLift Y (f ⁻¹' K) σ hσ) =
    SupportedCap.simplexLift X K ((TopCat.toSSet.map f).app _ σ)
      ((parent_iff f K σ).mpr hσ) := by
  apply ((TopCat.of K).toSSetObjEquiv _).injective
  apply ContinuousMap.ext
  intro t
  apply Subtype.ext
  simp only [TauCeti.TopCat.toSSetObjEquiv_toSSet_map_app, SupportedCap.simplexLift,
    Equiv.apply_symm_apply]
  rfl

theorem pullback_extend (p : ℕ) (κ : singularCochainGroup (ZMod 2) (TopCat.of K) p) :
    cochainPullback f p (TubeCochainExtension.extend X K p κ) =
      TubeCochainExtension.extend Y (f ⁻¹' K) p
        (cochainPullback (restriction f (f ⁻¹' K) K (fun _ h => h)) p κ) := by
  classical
  apply SSet.chainComplex_hom_ext (X := TopCat.toSSet.obj Y) (R := coeff)
  intro σ
  change (TopCat.toSSet.obj Y).ιChainComplex σ ≫
    ((push f).f p ≫ TubeCochainExtension.extend X K p κ) = _
  rw [push, SSet.ι_chainComplexMap_f_assoc,
    TubeCochainExtension.on_simplex, TubeCochainExtension.on_simplex]
  by_cases hσ : Set.range (Y.toSSetObjEquiv _ σ) ⊆ f ⁻¹' K
  · rw [dite_eq_left ((parent_iff f K σ).mpr hσ), dite_eq_left hσ]
    change _ = (TopCat.toSSet.obj (TopCat.of (f ⁻¹' K))).ιChainComplex
      (SupportedCap.simplexLift Y (f ⁻¹' K) σ hσ) ≫
        ((push (restriction f (f ⁻¹' K) K (fun _ h => h))).f p ≫ κ)
    rw [push, SSet.ι_chainComplexMap_f_assoc, lift_natural]
  · have hmap : ¬ Set.range (X.toSSetObjEquiv _ ((TopCat.toSSet.map f).app _ σ)) ⊆ K :=
      fun h => hσ ((parent_iff f K σ).mp h)
    rw [dite_eq_right hmap, dite_eq_right hσ]

theorem extend_zero (p : ℕ) : TubeCochainExtension.extend X K p 0 = 0 := by
  classical
  apply SSet.chainComplex_hom_ext (X := TopCat.toSSet.obj X) (R := coeff)
  intro σ
  rw [TubeCochainExtension.on_simplex]
  split <;> simp only [comp_zero]

theorem pullback_zero (p : ℕ) (κ : singularCochainGroup (ZMod 2) (TopCat.of K) p)
    (hκ : cochainPullback (restriction f (f ⁻¹' K) K (fun _ h => h)) p κ = 0) :
    cochainPullback f p (TubeCochainExtension.extend X K p κ) = 0 := by
  rw [pullback_extend, hκ, extend_zero]

end
end Finsler.TubeExtensionPullback
