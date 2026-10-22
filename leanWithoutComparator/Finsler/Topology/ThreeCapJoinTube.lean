module

public import Finsler.Topology.ThreeCapBlockVanishing
public import Finsler.Topology.NearFarCapComparison

/-! The actual first join Thom support removes a separately postulated
whole-rectangle near-tube inclusion. A far rectangle kills the actual
first cap, hence all three successive caps. Otherwise the original
factor covers put the whole rectangle in the enlarged join tube. -/

@[expose] public section
namespace Finsler.ThreeCapJoinTube

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.PairDistanceCover
open Finsler.RelativeCapAssociativity Finsler.ThreeCapBlockVanishing
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem near_rectangle {P Q : TopCat.{0}} {E : Type*} [PseudoMetricSpace E]
    (b : P → E) (c : Q → E) (r : ℝ) (cx : P) (cy : Q)
    (S : Set (P ⊗ Q : TopCat.{0}))
    (hrect : S ⊆ cover b (r / 4) cx ×ˢ cover c (r / 4) cy)
    (j k p q : ℕ) (J : singularCochainGroup (ZMod 2) (P ⊗ Q) j)
    (hJ : cochainPullback (SupportedCap.subspaceMap (P ⊗ Q)
      (NearFarCapComparison.far b c r)) j J = 0)
    (φ : singularCochainGroup (ZMod 2) (P ⊗ Q) k)
    (ψ : singularCochainGroup (ZMod 2) (P ⊗ Q) p)
    (σ : TopCat.toSSet.obj (P ⊗ Q) _⦋j + k + p + q⦌)
    (hσS : Set.range ((P ⊗ Q).toSSetObjEquiv _ σ) ⊆ S)
    (hn : (TopCat.toSSet.obj (P ⊗ Q)).ιChainComplex σ ≫
      threeCap (P ⊗ Q) j k p q J φ ψ ≠ 0) :
    ∀ z ∈ S, dist (b z.1) (c z.2) < 2 * r := by
  obtain hfar | hnear := near_far_rectangle b c r cx cy
  · have hσfar : Set.range ((P ⊗ Q).toSSetObjEquiv _ σ) ⊆ NearFarCapComparison.far b c r := by
      intro z hz
      have hs := hrect (hσS hz)
      exact hfar z.1 hs.1 z.2 hs.2
    have hz := SupportedCap.cap_zero_on_simplex (P ⊗ Q) (NearFarCapComparison.far b c r)
      j (k + (p + q)) (j + k + p + q) (by omega) J hJ σ hσfar
    exfalso
    apply hn
    change (TopCat.toSSet.obj (P ⊗ Q)).ιChainComplex σ ≫
      (absoluteChain (P ⊗ Q) j (k + (p + q)) (j + k + p + q) (by omega) J ≫
        absoluteChain (P ⊗ Q) k (p + q) (k + (p + q)) rfl φ ≫
          absoluteChain (P ⊗ Q) p q (p + q) rfl ψ) = 0
    rw [← Category.assoc, hz, zero_comp]
  · intro z hz
    have hs := hrect hz
    exact hnear z.1 hs.1 z.2 hs.2

theorem rectangle_in_tube {P Q : TopCat.{0}} {E : Type*} [PseudoMetricSpace E]
    (b : P → E) (c : Q → E) (r : ℝ) (cx : P) (cy : Q)
    (S K : Set (P ⊗ Q : TopCat.{0}))
    (hrect : S ⊆ cover b (r / 4) cx ×ˢ cover c (r / 4) cy)
    (hK : ∀ z, dist (b z.1) (c z.2) < 2 * r → z ∈ K)
    (j k p q : ℕ) (J : singularCochainGroup (ZMod 2) (P ⊗ Q) j)
    (hJ : cochainPullback (SupportedCap.subspaceMap (P ⊗ Q)
      (NearFarCapComparison.far b c r)) j J = 0)
    (φ : singularCochainGroup (ZMod 2) (P ⊗ Q) k)
    (ψ : singularCochainGroup (ZMod 2) (P ⊗ Q) p)
    (σ : TopCat.toSSet.obj (P ⊗ Q) _⦋j + k + p + q⦌)
    (hσS : Set.range ((P ⊗ Q).toSSetObjEquiv _ σ) ⊆ S)
    (hn : (TopCat.toSSet.obj (P ⊗ Q)).ιChainComplex σ ≫
      threeCap (P ⊗ Q) j k p q J φ ψ ≠ 0) : S ⊆ K := by
  intro z hz
  exact hK z (near_rectangle b c r cx cy S hrect j k p q J hJ φ ψ σ hσS hn z hz)

end
end Finsler.ThreeCapJoinTube
