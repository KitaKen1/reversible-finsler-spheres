module

public import Finsler.Topology.TubeCochainExtension
public import Finsler.Topology.CarrierCochainZero

/-! A nonzero evaluation of the actual zero-extended tested cochain
supplies an actual tested-length witness. The tested value is continuous
on its genuine domain and hence on every intermediate compact tube inside
that domain; no global continuity of its zero extension is assumed. -/

@[expose] public section
namespace Finsler.TubeTestWitness

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
attribute [local instance] Classical.propDecidable

variable {X Y : TopCat.{0}}

theorem nonzero_evaluation_witness (A : Set X) (p : ℕ)
    (φ : singularCochainGroup (ZMod 2) X p)
    (hφ : cochainPullback (SupportedCap.subspaceMap X A) p φ = 0)
    (σ : TopCat.toSSet.obj X _⦋p⦌)
    (hσ : (TopCat.toSSet.obj X).ιChainComplex σ ≫ φ ≠ 0) :
    ∃ z ∈ Set.range (X.toSSetObjEquiv _ σ), z ∉ A := by
  classical
  by_contra h
  push Not at h
  have hs : σ ∈ (X.smallSingularSubcomplex (fun _ : PUnit.{1} => A)).obj (Opposite.op ⦋p⦌) :=
    (TopCat.mem_smallSingularSubcomplex_iff X (fun _ : PUnit.{1} => A) σ).mpr ⟨PUnit.unit, h⟩
  have hc := TauCeti.ιChainComplex_mem_smallSingularChains (R := coeff)
    (U := fun _ : PUnit.{1} => A) ⟨σ, hs⟩
  exact hσ (CarrierCochainZero.carried_zero (fun _ : PUnit.{1} => A) p φ (fun _ => hφ) hc)

def partialValue (O : Set X) (g : TopCat.of O ⟶ Y) (ℓ : Y → ℝ) (z : X) : ℝ :=
  if hz : z ∈ O then ℓ (g ⟨z, hz⟩) else 0

theorem continuousOn_partialValue (O : Set X) (g : TopCat.of O ⟶ Y)
    (ℓ : Y → ℝ) (hℓ : Continuous ℓ) : ContinuousOn (partialValue O g ℓ) O := by
  rw [continuousOn_iff_continuous_domRestrict]
  change Continuous (fun z : O => partialValue O g ℓ z.val)
  have he : (fun z : O => partialValue O g ℓ z.val) = fun z => ℓ (g z) := by
    funext z
    simp only [partialValue, dite_eq_left z.property]
  rw [he]
  exact hℓ.comp g.hom.continuous

theorem extension_test_witness (O : Set X) (g : TopCat.of O ⟶ Y)
    (ℓ : Y → ℝ) (p : ℕ) (L : ℝ)
    (T : singularCochainGroup (ZMod 2) Y p)
    (hT : cochainPullback (SupportedCap.subspaceMap Y {y | ℓ y < L}) p T = 0)
    (σ : TopCat.toSSet.obj X _⦋p⦌)
    (hσ : (TopCat.toSSet.obj X).ιChainComplex σ ≫
      TubeCochainExtension.extend X O p (cochainPullback g p T) ≠ 0) :
    Set.range (X.toSSetObjEquiv _ σ) ⊆ O ∧
      ∃ z ∈ Set.range (X.toSSetObjEquiv _ σ), L ≤ partialValue O g ℓ z := by
  classical
  by_cases hO : Set.range (X.toSSetObjEquiv _ σ) ⊆ O
  · rw [TubeCochainExtension.on_simplex, dite_eq_left hO] at hσ
    have hzero : cochainPullback
        (SupportedCap.subspaceMap (TopCat.of O) {z | ℓ (g z) < L}) p
        (cochainPullback g p T) = 0 :=
      pullback_support g {z | ℓ (g z) < L} {y | ℓ y < L} (fun _ hz => hz) p T hT
    obtain ⟨z, hz, hnot⟩ := nonzero_evaluation_witness {z | ℓ (g z) < L} p
      (cochainPullback g p T) hzero (SupportedCap.simplexLift X O σ hO) hσ
    obtain ⟨t, rfl⟩ := hz
    refine ⟨hO, X.toSSetObjEquiv _ σ t, ⟨t, rfl⟩, ?_⟩
    have ht : X.toSSetObjEquiv _ σ t ∈ O := hO ⟨t, rfl⟩
    change ¬ ℓ (g (((TopCat.of O).toSSetObjEquiv _ (SupportedCap.simplexLift X O σ hO)) t)) < L at hnot
    simp only [SupportedCap.simplexLift, Equiv.apply_symm_apply] at hnot
    change ¬ ℓ (g ⟨X.toSSetObjEquiv _ σ t, ht⟩) < L at hnot
    rw [partialValue, dite_eq_left ht]
    exact le_of_not_gt hnot
  · rw [TubeCochainExtension.on_simplex, dite_eq_right hO] at hσ
    exact (hσ rfl).elim

end
end Finsler.TubeTestWitness
