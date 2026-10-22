module

public import Finsler.Topology.ThreeCapLocalBoundary
public import Finsler.Topology.DegreeLoweringHomology

/-! A genuine face on which the middle cochain vanishes is still
killed after actual small-chain approximation. The carrier is preserved
by the approximation. A bounded lift is then killed by source chain
monicity before any retained output or homology map. -/

@[expose] public section
namespace Finsler.ThreeCapRetractionZero

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.RelativeCapAssociativity Finsler.ThreeCapBlockVanishing TauCeti
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1400000

theorem after_approximation {X Y : TopCat.{0}} {ι : Type*} (W : ι → Set X)
    (f : Y ⟶ X) (A : Set X) (hf : Set.range f ⊆ A) (a b c q : ℕ)
    (J : singularCochainGroup (ZMod 2) X a) (φ : singularCochainGroup (ZMod 2) X b)
    (ψ : singularCochainGroup (ZMod 2) X c)
    (hφ : cochainPullback (SupportedCap.subspaceMap X A) b φ = 0) :
    (push f).f (a + b + c + q) ≫ (singularSmallApprox coeff W).f (a + b + c + q) ≫
      threeCap X a b c q J φ ψ = 0 := by
  have hcup : cochainPullback (SupportedCap.subspaceMap X A) (a + (b + c))
      (cochainCup a (b + c) J (cochainCup b c φ ψ)) = 0 := by
    rw [cochainCup_naturality, cochainCup_naturality, hφ,
      cochainCup_zero_left, cochainCup_zero_right]
  apply SSet.chainComplex_hom_ext (X := TopCat.toSSet.obj Y) (R := coeff)
  intro σ
  let τ := (TopCat.toSSet.map f).app _ σ
  have hrange : Set.range (X.toSSetObjEquiv _ τ) ⊆ A := by
    dsimp only [τ]
    rw [TauCeti.TopCat.toSSetObjEquiv_toSSet_map_app]
    rintro _ ⟨t, rfl⟩
    exact hf ⟨Y.toSSetObjEquiv _ σ t, rfl⟩
  have hs : τ ∈ (X.smallSingularSubcomplex (fun _ : PUnit.{1} => A)).obj _ :=
    (TopCat.mem_smallSingularSubcomplex_iff X (fun _ : PUnit.{1} => A) τ).mpr ⟨PUnit.unit, hrange⟩
  have hc : (TopCat.toSSet.obj X).ιChainComplex τ ∈ supported X (fun _ : PUnit.{1} => A)
      (a + b + c + q) :=
    TauCeti.ιChainComplex_mem_smallSingularChains (R := coeff) (U := fun _ : PUnit.{1} => A) ⟨τ, hs⟩
  have hafter := approximation_preserves W (fun _ : PUnit.{1} => A) hc
  have hz := CarrierCochainZero.cap_zero (fun _ : PUnit.{1} => A) (a + (b + c)) q
    (a + b + c + q) (by omega) (cochainCup a (b + c) J (cochainCup b c φ ψ))
    (fun _ => hcup) hafter
  rw [ThreeCapLocalBoundary.three_cap_cup]
  simp only [push, SSet.ι_chainComplexMap_f_assoc, comp_zero]
  simpa only [Category.assoc, τ] using hz

theorem after_retraction {X Y Z : TopCat.{0}} {ι : Type*} (W : ι → Set X)
    (hW : ∀ i, IsOpen (W i)) (hcW : ⋃ i, W i = Set.univ)
    (f : Y ⟶ X) (A : Set X) (hf : Set.range f ⊆ A) (a b c q : ℕ)
    (J : singularCochainGroup (ZMod 2) X a) (φ : singularCochainGroup (ZMod 2) X b)
    (ψ : singularCochainGroup (ZMod 2) X c)
    (hφ : cochainPullback (SupportedCap.subspaceMap X A) b φ = 0)
    (u : DegreeLoweringHomology.Map (small X W) (chains Z) (a + b + c))
    (i : chains Z ⟶ chains X) [Mono (i.f q)]
    (hi : u.component q ≫ i.f q =
      (inclusion X W).f (a + b + c + q) ≫ threeCap X a b c q J φ ψ) :
    (push f ≫ smallSingularRetraction coeff W hW hcW).f (a + b + c + q) ≫ u.component q = 0 := by
  apply (cancel_mono (i.f q)).mp
  rw [zero_comp, Category.assoc, hi, HomologicalComplex.comp_f,
    Category.assoc, ← Category.assoc ((smallSingularRetraction coeff W hW hcW).f (a + b + c + q)),
    ← HomologicalComplex.comp_f, smallSingularRetraction_comp_ι]
  exact after_approximation W f A hf a b c q J φ ψ hφ

end
end Finsler.ThreeCapRetractionZero
