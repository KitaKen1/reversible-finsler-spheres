module

public import Finsler.Topology.TubeExtensionPullback

/-! Literal naturality of zero extension across an actual inverse-image
subspace square, without requiring definitionally identical domain sets.
The statements concern the actual simplex extension, not its cohomology. -/

@[expose] public section
namespace Finsler.TubeExtensionSquare

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1100000

variable {X Y : TopCat.{0}} (f : Y ⟶ X) (K : Set X) (D : Set Y)
  (g : TopCat.of D ⟶ TopCat.of K)
  (hD : ∀ y, y ∈ D ↔ f y ∈ K)
  (hsquare : g ≫ SupportedCap.subspaceMap X K = SupportedCap.subspaceMap Y D ≫ f)

include hD in
theorem parent_iff {p : ℕ} (σ : TopCat.toSSet.obj Y _⦋p⦌) :
    Set.range (X.toSSetObjEquiv _ ((TopCat.toSSet.map f).app _ σ)) ⊆ K ↔
      Set.range (Y.toSSetObjEquiv _ σ) ⊆ D := by
  rw [TauCeti.TopCat.toSSetObjEquiv_toSSet_map_app]
  constructor
  · intro h z hz
    obtain ⟨t, rfl⟩ := hz
    exact (hD _).mpr (h ⟨t, rfl⟩)
  · intro h z hz
    obtain ⟨t, rfl⟩ := hz
    exact (hD _).mp (h ⟨t, rfl⟩)

include hD hsquare in
theorem lift_square {p : ℕ} (σ : TopCat.toSSet.obj Y _⦋p⦌)
    (hσ : Set.range (Y.toSSetObjEquiv _ σ) ⊆ D) :
    (TopCat.toSSet.map g).app _ (SupportedCap.simplexLift Y D σ hσ) =
      SupportedCap.simplexLift X K ((TopCat.toSSet.map f).app _ σ)
        ((parent_iff f K D hD σ).mpr hσ) := by
  apply ((TopCat.of K).toSSetObjEquiv _).injective
  apply ContinuousMap.ext
  intro t
  apply Subtype.ext
  simp only [TauCeti.TopCat.toSSetObjEquiv_toSSet_map_app, SupportedCap.simplexLift,
    Equiv.apply_symm_apply]
  exact ConcreteCategory.congr_hom hsquare ⟨Y.toSSetObjEquiv _ σ t, hσ ⟨t, rfl⟩⟩

include hD hsquare in
theorem pullback_extend (p : ℕ) (κ : singularCochainGroup (ZMod 2) (TopCat.of K) p) :
    cochainPullback f p (TubeCochainExtension.extend X K p κ) =
      TubeCochainExtension.extend Y D p (cochainPullback g p κ) := by
  classical
  apply SSet.chainComplex_hom_ext (X := TopCat.toSSet.obj Y) (R := coeff)
  intro σ
  change (TopCat.toSSet.obj Y).ιChainComplex σ ≫
    ((push f).f p ≫ TubeCochainExtension.extend X K p κ) = _
  rw [push, SSet.ι_chainComplexMap_f_assoc,
    TubeCochainExtension.on_simplex, TubeCochainExtension.on_simplex]
  by_cases hσ : Set.range (Y.toSSetObjEquiv _ σ) ⊆ D
  · rw [dite_eq_left ((parent_iff f K D hD σ).mpr hσ), dite_eq_left hσ]
    change _ = (TopCat.toSSet.obj (TopCat.of D)).ιChainComplex (SupportedCap.simplexLift Y D σ hσ) ≫
      ((push g).f p ≫ κ)
    rw [push, SSet.ι_chainComplexMap_f_assoc, lift_square f K D g hD hsquare]
  · have hmap : ¬ Set.range (X.toSSetObjEquiv _ ((TopCat.toSSet.map f).app _ σ)) ⊆ K :=
      fun h => hσ ((parent_iff f K D hD σ).mp h)
    rw [dite_eq_right hmap, dite_eq_right hσ]

theorem pullback_on_map {X Y : TopCat.{0}} (K : Set X) (f : Y ⟶ TopCat.of K)
    (p : ℕ) (κ : singularCochainGroup (ZMod 2) (TopCat.of K) p) :
    cochainPullback (f ≫ SupportedCap.subspaceMap X K) p (TubeCochainExtension.extend X K p κ) =
      cochainPullback f p κ := by
  rw [pullback_comp, TubeCochainExtension.restriction]

end
end Finsler.TubeExtensionSquare
