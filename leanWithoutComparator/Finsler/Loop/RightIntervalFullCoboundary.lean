module

public import Finsler.Loop.RightIntervalCoboundary

/-! The SAME interval integration primitive with both actual endpoint
terms retained. No endpoint vanishing or cycle hypothesis is imposed. -/
@[expose] public section
namespace Finsler.RightIntervalFullCoboundary
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.RightIntervalCochain
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 900000

def integrate (X : TopCat.{0}) (p : ℕ) (T : singularCochainGroup (ZMod 2) (space X) (p + 1)) :
    singularCochainGroup (ZMod 2) X p := TimeTriangleSplit.interval X p ≫ T

theorem boundary (X : TopCat.{0}) (p : ℕ) (T : singularCochainGroup (ZMod 2) (space X) (p + 1)) :
    cochainCoboundary (ZMod 2) X p (RightIntervalCoboundary.primitive X p T) =
      integrate X (p + 1) (cochainCoboundary (ZMod 2) (space X) (p + 1) T) +
        cochainPullback (endpoint X 1) (p + 1) T - cochainPullback (endpoint X 0) (p + 1) T := by
  have h := congrArg (fun f => f ≫ T) (full_boundary X p)
  simp only [Preadditive.add_comp, Category.assoc] at h
  change cochainPullback (endpoint X 0) (p + 1) T =
    cochainCoboundary (ZMod 2) X p (integrate X p T) +
      integrate X (p + 1) (cochainCoboundary (ZMod 2) (space X) (p + 1) T) +
      cochainPullback (endpoint X 1) (p + 1) T at h
  change (chains X).d (p + 1) p ≫ (-(TimeTriangleSplit.interval X p ≫ T)) = _
  rw [Preadditive.comp_neg]
  change -(cochainCoboundary (ZMod 2) X p (integrate X p T)) = _
  rw [h]
  abel

def corrected (X : TopCat.{0}) (p : ℕ) (T : singularCochainGroup (ZMod 2) (space X) (p + 1))
    (B : singularCochainGroup (ZMod 2) (space X) (p + 2)) : singularCochainGroup (ZMod 2) X (p + 1) :=
  integrate X (p + 1) B - cochainPullback (endpoint X 1) (p + 1) T +
    cochainPullback (endpoint X 0) (p + 1) T

theorem comparison (X : TopCat.{0}) (p : ℕ) (T : singularCochainGroup (ZMod 2) (space X) (p + 1))
    (A B : singularCochainGroup (ZMod 2) (space X) (p + 2))
    (hT : cochainCoboundary (ZMod 2) (space X) (p + 1) T = A - B) :
    cochainCoboundary (ZMod 2) X p (RightIntervalCoboundary.primitive X p T) =
      integrate X (p + 1) A - corrected X p T B := by
  rw [boundary, hT, corrected]
  simp only [integrate, Preadditive.comp_sub]
  abel

theorem corrected_of_endpoints (X : TopCat.{0}) (p : ℕ) (T : singularCochainGroup (ZMod 2) (space X) (p + 1))
    (B : singularCochainGroup (ZMod 2) (space X) (p + 2))
    (h₀ : cochainPullback (endpoint X 0) (p + 1) T = 0)
    (h₁ : cochainPullback (endpoint X 1) (p + 1) T = 0) :
    corrected X p T B = integrate X (p + 1) B := by
  rw [corrected, h₀, h₁, sub_zero, add_zero]

end
end Finsler.RightIntervalFullCoboundary
