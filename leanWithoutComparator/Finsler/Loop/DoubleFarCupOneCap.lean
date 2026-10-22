module

public import Finsler.Loop.MultiFarSupportedCochain
public import Finsler.Loop.CupCapOrder
public import Finsler.Topology.RelativeCupCommutativity

/-! TWO original supported cochains, a genuine three-open cover,
and a test defined ONLY on the common near set. The actual cup-one
cap has boundary equal to the two actual cup-order caps. Separate far
zeros suffice on this cover; no zero on their UNION is asserted.
Comparison with original sequential supported cuts is separate. -/
@[expose] public section
namespace Finsler.DoubleFarCupOneCap
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.MultiFarSupportedCap
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

def far (X : TopCat.{0}) (A C : Set X) : Bool → Set X := fun i => if i then C else A

theorem far_open (X : TopCat.{0}) (A C : Set X) (hA : IsOpen A) (hC : IsOpen C) :
    ∀ i, IsOpen (far X A C i) := by
  intro i
  cases i
  · exact hA
  · exact hC

theorem common_cover (X : TopCat.{0}) (A B C D : Set X)
    (hAB : A ∪ B = Set.univ) (hCD : C ∪ D = Set.univ) :
    (⋃ i, far X A C i) ∪ (B ∩ D) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  have hab : x ∈ A ∪ B := hAB.symm ▸ Set.mem_univ x
  have hcd : x ∈ C ∪ D := hCD.symm ▸ Set.mem_univ x
  rcases hab with ha | hb
  · exact Or.inl (Set.mem_iUnion.mpr ⟨false, ha⟩)
  · rcases hcd with hc | hd
    · exact Or.inl (Set.mem_iUnion.mpr ⟨true, hc⟩)
    · exact Or.inr ⟨hb, hd⟩

variable (X : TopCat.{0}) (A C : Set X) (p r : ℕ)
  (θ : singularCochainGroup (ZMod 2) X p)
  (η : singularCochainGroup (ZMod 2) X (r + 1))
  (hθ : cochainPullback (SupportedCap.subspaceMap X A) p θ = 0)
  (hη : cochainPullback (SupportedCap.subspaceMap X C) (r + 1) η = 0)

def leftCup := CupOne.cup X p (r + 1) (p + r + 1) (by omega) θ η
def rightCup := CupOne.cup X (r + 1) p (p + r + 1) (by omega) η θ
def kappa := CupOne.cupOne X p (r + 1) (p + r) (by omega) θ η

include hθ hη in
theorem left_supported : ∀ i, cochainPullback (SupportedCap.subspaceMap X (far X A C i)) (p + r + 1)
    (leftCup X p r θ η) = 0 := by
  intro i
  cases i with
  | false => exact CupCapOrder.restriction_zero _ p (r + 1) _ (by omega) θ η (Or.inl hθ)
  | true => exact CupCapOrder.restriction_zero _ p (r + 1) _ (by omega) θ η (Or.inr hη)

include hθ hη in
theorem right_supported : ∀ i, cochainPullback (SupportedCap.subspaceMap X (far X A C i)) (p + r + 1)
    (rightCup X p r θ η) = 0 := by
  intro i
  cases i with
  | false => exact CupCapOrder.restriction_zero _ (r + 1) p _ (by omega) η θ (Or.inr hθ)
  | true => exact CupCapOrder.restriction_zero _ (r + 1) p _ (by omega) η θ (Or.inl hη)

include hθ hη in
theorem kappa_supported : ∀ i, cochainPullback (SupportedCap.subspaceMap X (far X A C i)) (p + r)
    (kappa X p r θ η) = 0 := by
  intro i
  cases i with
  | false => exact CupOne.restriction_zero _ p (r + 1) _ (by omega) θ η (Or.inl hθ)
  | true => exact CupOne.restriction_zero _ p (r + 1) _ (by omega) θ η (Or.inr hη)

theorem kappa_boundary (hθc : cochainCoboundary (ZMod 2) X p θ = 0)
    (hηc : cochainCoboundary (ZMod 2) X (r + 1) η = 0) :
    cochainCoboundary (ZMod 2) X (p + r) (kappa X p r θ η) =
      leftCup X p r θ η - rightCup X p r θ η :=
  CupOne.boundary_cocycles X p (r + 1) (p + r) (by omega) θ η hθc hηc

variable (B : Set X) (hA : IsOpen A) (hC : IsOpen C) (hB : IsOpen B)
  (hc : (⋃ i, far X A C i) ∪ B = Set.univ)
  (q : ℕ) (ψ : singularCochainGroup (ZMod 2) (TopCat.of B) q)

def left : singularCochainGroup (ZMod 2) X ((p + r) + q + 1) :=
  cut X (far X A C) B (far_open X A C hA hC) hB hc (p + r + 1) q ((p + r) + q + 1) (by omega)
    (leftCup X p r θ η) (left_supported X A C p r θ η hθ hη) ≫ ψ

def right : singularCochainGroup (ZMod 2) X ((p + r) + q + 1) :=
  cut X (far X A C) B (far_open X A C hA hC) hB hc (p + r + 1) q ((p + r) + q + 1) (by omega)
    (rightCup X p r θ η) (right_supported X A C p r θ η hθ hη) ≫ ψ

def primitive : singularCochainGroup (ZMod 2) X ((p + r) + q) :=
  cut X (far X A C) B (far_open X A C hA hC) hB hc (p + r) q ((p + r) + q) rfl
    (kappa X p r θ η) (kappa_supported X A C p r θ η hθ hη) ≫ ψ

theorem boundary (hθc : cochainCoboundary (ZMod 2) X p θ = 0)
    (hηc : cochainCoboundary (ZMod 2) X (r + 1) η = 0)
    (hψ : cochainCoboundary (ZMod 2) (TopCat.of B) q ψ = 0) :
    cochainCoboundary (ZMod 2) X ((p + r) + q)
      (primitive X A C p r θ η hθ hη B hA hC hB hc q ψ) =
      left X A C p r θ η hθ hη B hA hC hB hc q ψ - right X A C p r θ η hθ hη B hA hC hB hc q ψ := by
  have hb := MultiFarSupportedCochain.correction_boundary X (far X A C) B (far_open X A C hA hC) hB hc
    (p + r) q ((p + r) + q) rfl (kappa X p r θ η) (kappa_supported X A C p r θ η hθ hη) ψ hψ
  have hd := MultiFarSupportedCochain.coboundary_supported X (far X A C) (p + r)
    (kappa X p r θ η) (kappa_supported X A C p r θ η hθ hη)
  have hs : ∀ i, cochainPullback (SupportedCap.subspaceMap X (far X A C i)) (p + r + 1)
      (leftCup X p r θ η - rightCup X p r θ η) = 0 := by
    intro i
    change ((singularCochainComplexZMod2.map (SupportedCap.subspaceMap X (far X A C i)).op).f _).hom (_ - _) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr ((left_supported X A C p r θ η hθ hη i).trans
      (right_supported X A C p r θ η hθ hη i).symm)
  have he := MultiFarSupportedCochain.cut_eq X (far X A C) B (far_open X A C hA hC) hB hc
    (p + r + 1) q ((p + r) + q + 1) (by omega) _ _ hd hs (kappa_boundary X p r θ η hθc hηc)
  change cochainCoboundary (ZMod 2) X ((p + r) + q) _ = _ at hb
  rw [he, MultiFarSupportedCochain.cut_sub X (far X A C) B (far_open X A C hA hC) hB hc
    (p + r + 1) q ((p + r) + q + 1) (by omega) _ _
    (left_supported X A C p r θ η hθ hη) (right_supported X A C p r θ η hθ hη) hs,
    Preadditive.sub_comp] at hb
  exact hb

theorem left_closed (hθc : cochainCoboundary (ZMod 2) X p θ = 0)
    (hηc : cochainCoboundary (ZMod 2) X (r + 1) η = 0)
    (hψ : cochainCoboundary (ZMod 2) (TopCat.of B) q ψ = 0) :
    cochainCoboundary (ZMod 2) X _ (left X A C p r θ η hθ hη B hA hC hB hc q ψ) = 0 :=
  MultiFarSupportedCochain.scalar_closed X (far X A C) B (far_open X A C hA hC) hB hc
    (p + r + 1) q _ (by omega) _ (left_supported X A C p r θ η hθ hη)
    (CupCapOrder.closed X p (r + 1) _ (by omega) θ η hθc hηc) ψ hψ

theorem right_closed (hθc : cochainCoboundary (ZMod 2) X p θ = 0)
    (hηc : cochainCoboundary (ZMod 2) X (r + 1) η = 0)
    (hψ : cochainCoboundary (ZMod 2) (TopCat.of B) q ψ = 0) :
    cochainCoboundary (ZMod 2) X _ (right X A C p r θ η hθ hη B hA hC hB hc q ψ) = 0 :=
  MultiFarSupportedCochain.scalar_closed X (far X A C) B (far_open X A C hA hC) hB hc
    (p + r + 1) q _ (by omega) _ (right_supported X A C p r θ η hθ hη)
    (CupCapOrder.closed X (r + 1) p _ (by omega) η θ hηc hθc) ψ hψ

theorem primitive_carrier_zero (S : Set X)
    (hS : cochainPullback (restriction (SupportedCap.subspaceMap X S)
      ((SupportedCap.subspaceMap X S) ⁻¹' B) B (fun _ h => h)) q ψ = 0) :
    cochainPullback (SupportedCap.subspaceMap X S) _
      (primitive X A C p r θ η hθ hη B hA hC hB hc q ψ) = 0 :=
  MultiFarSupportedCochain.subspace_zero X (far X A C) B (far_open X A C hA hC) hB hc
    S (p + r) q _ rfl _ (kappa_supported X A C p r θ η hθ hη) ψ hS

end
end Finsler.DoubleFarCupOneCap
