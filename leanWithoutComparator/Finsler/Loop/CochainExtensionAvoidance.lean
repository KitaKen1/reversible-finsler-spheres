module

public import Finsler.Topology.TubeExtensionPullback

/-! A genuine zero extension vanishes on EVERY map whose image
avoids its support subset. No openness, closedness, or cocycle
condition is needed. This allows a seam cochain correction to be
extended while preserving an already-proved exterior zero. -/
@[expose] public section
namespace Finsler.CochainExtensionAvoidance
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open scoped Simplicial
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

theorem pullback_zero {X Y : TopCat.{0}} (O : Set X) (f : Y ⟶ X)
    (hf : ∀ y, f y ∉ O) (q : ℕ) (ψ : singularCochainGroup (ZMod 2) (TopCat.of O) q) :
    cochainPullback f q (TubeCochainExtension.extend X O q ψ) = 0 := by
  classical
  apply SSet.chainComplex_hom_ext (X := TopCat.toSSet.obj Y) (R := coeff)
  intro σ
  have hmap : ¬ Set.range (X.toSSetObjEquiv _ ((TopCat.toSSet.map f).app _ σ)) ⊆ O := by
    intro hmap
    obtain ⟨y, hy⟩ := Set.range_nonempty (Y.toSSetObjEquiv _ σ)
    obtain ⟨t, rfl⟩ := hy
    have h := hmap (Set.mem_range_self t)
    rw [TauCeti.TopCat.toSSetObjEquiv_toSSet_map_app] at h
    exact hf (Y.toSSetObjEquiv _ σ t) h
  change (TopCat.toSSet.obj Y).ιChainComplex σ ≫
    ((push f).f q ≫ TubeCochainExtension.extend X O q ψ) = _
  rw [push, SSet.ι_chainComplexMap_f_assoc, TubeCochainExtension.on_simplex, dite_eq_right hmap, comp_zero]

end
end Finsler.CochainExtensionAvoidance
