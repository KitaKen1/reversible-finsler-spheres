module

public import Finsler.Loop.CompactHomologyZeroDetection

/-! A compact class killed by a genuine continuous map factors through
ONE actual compact target where it is already zero. Both the actual
topological factorization and the actual induced homology zero are proved. -/

@[expose] public section
namespace Finsler.CompactMapZeroFactor
open CategoryTheory AlgebraicTopology TopologicalSpace Topology
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1300000

theorem exists_factor {X Y : TopCat.{0}} (f : X ⟶ Y) (K : Compacts X) (q : ℕ)
    (z : (chains (TopCat.of (K : Set X))).homology q)
    (hz : (HomologicalComplex.homologyMap (push (SupportedCap.subspaceMap X (K : Set X) ≫ f)) q).hom z = 0) :
    ∃ L : Compacts Y, ∃ g : TopCat.of (K : Set X) ⟶ TopCat.of (L : Set Y),
      g ≫ SupportedCap.subspaceMap Y (L : Set Y) = SupportedCap.subspaceMap X (K : Set X) ≫ f ∧
        (HomologicalComplex.homologyMap (push g) q).hom z = 0 := by
  let J : Compacts Y := ⟨f '' (K : Set X), K.isCompact.image f.hom.continuous⟩
  let g₀ : TopCat.of (K : Set X) ⟶ TopCat.of (J : Set Y) :=
    TopCat.ofHom ⟨fun x => ⟨f x.val, x.val, x.property, rfl⟩,
      (f.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩
  have hs : g₀ ≫ SupportedCap.subspaceMap Y (J : Set Y) = SupportedCap.subspaceMap X (K : Set X) ≫ f := by
    ext x : 1
    rfl
  let w := (HomologicalComplex.homologyMap (push g₀) q).hom z
  have hw : (HomologicalComplex.homologyMap (push (SupportedCap.subspaceMap Y (J : Set Y))) q).hom w = 0 := by
    change (HomologicalComplex.homologyMap (push g₀) q ≫
      HomologicalComplex.homologyMap (push (SupportedCap.subspaceMap Y (J : Set Y))) q).hom z = 0
    rw [← HomologicalComplex.homologyMap_comp, ← push_comp, hs]
    exact hz
  obtain ⟨L, a, ha⟩ := CompactHomologyZeroDetection.exists_larger Y q J w hw
  refine ⟨L, g₀ ≫ (CompactHomologyLift.diagram Y).map a, ?_, ?_⟩
  · ext x : 1
    rfl
  · rw [push_comp, HomologicalComplex.homologyMap_comp]
    exact ha

end
end Finsler.CompactMapZeroFactor
