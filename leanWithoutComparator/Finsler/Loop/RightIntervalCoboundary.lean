module

public import Finsler.Loop.RightIntervalCochain

/-! Integrate an explicit coboundary through the canonical right
interval. Both endpoint restrictions and the full source differential
are retained. Naturality transfers spatial carriers to the primitive. -/
@[expose] public section
namespace Finsler.RightIntervalCoboundary
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.RightIntervalCochain
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

def primitive (X : TopCat.{0}) (p : ℕ) (T : singularCochainGroup (ZMod 2) (space X) (p + 1)) :
    singularCochainGroup (ZMod 2) X p := -(TimeTriangleSplit.interval X p ≫ T)

theorem boundary (X : TopCat.{0}) (p : ℕ) (T : singularCochainGroup (ZMod 2) (space X) (p + 1))
    (h₀ : cochainPullback (endpoint X 0) (p + 1) T = 0)
    (h₁ : cochainPullback (endpoint X 1) (p + 1) T = 0) :
    cochainCoboundary (ZMod 2) X p (primitive X p T) =
      TimeTriangleSplit.interval X (p + 1) ≫ cochainCoboundary (ZMod 2) (space X) (p + 1) T := by
  have h := congrArg (fun f => f ≫ T) (full_boundary X p)
  have h0 : (push (endpoint X 0)).f (p + 1) ≫ T = 0 := h₀
  have h1 : (push (endpoint X 1)).f (p + 1) ≫ T = 0 := h₁
  simp only [Preadditive.add_comp, Category.assoc, h0, h1, add_zero] at h
  change (chains X).d (p + 1) p ≫ (-(TimeTriangleSplit.interval X p ≫ T)) = _
  rw [Preadditive.comp_neg]
  exact (eq_neg_of_add_eq_zero_right h.symm).symm

theorem comparison (X : TopCat.{0}) (p : ℕ) (T : singularCochainGroup (ZMod 2) (space X) (p + 1))
    (A B : singularCochainGroup (ZMod 2) (space X) (p + 2))
    (hT : cochainCoboundary (ZMod 2) (space X) (p + 1) T = A - B)
    (h₀ : cochainPullback (endpoint X 0) (p + 1) T = 0)
    (h₁ : cochainPullback (endpoint X 1) (p + 1) T = 0) :
    cochainCoboundary (ZMod 2) X p (primitive X p T) =
      TimeTriangleSplit.interval X (p + 1) ≫ A - TimeTriangleSplit.interval X (p + 1) ≫ B := by
  rw [boundary X p T h₀ h₁, hT, Preadditive.comp_sub]

theorem primitive_pullback_zero {X Y : TopCat.{0}} (f : X ⟶ Y) (p : ℕ)
    (T : singularCochainGroup (ZMod 2) (space Y) (p + 1))
    (hT : cochainPullback (f ▷ TopCat.I) (p + 1) T = 0) :
    cochainPullback f p (primitive Y p T) = 0 := by
  change (push f).f p ≫ (-(TimeTriangleSplit.interval Y p ≫ T)) = 0
  rw [Preadditive.comp_neg, ← Category.assoc, naturality, Category.assoc]
  change -(TimeTriangleSplit.interval X p ≫ cochainPullback (f ▷ TopCat.I) (p + 1) T) = 0
  rw [hT, comp_zero, neg_zero]

end
end Finsler.RightIntervalCoboundary
