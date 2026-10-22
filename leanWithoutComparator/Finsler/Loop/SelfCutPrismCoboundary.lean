module

public import Finsler.Loop.NativeSupportedIntervalOrder
public import Finsler.Topology.SelfCutTimePrism

/-! Transport an actual cochain coboundary through the ORIGINAL outer
self-cut time prism. Both endpoint restrictions are used explicitly.
The source boundary remains; the time-inserted chain is never assumed
to be an absolute cycle. The minus sign is kept even over ZMod 2. -/
@[expose] public section
namespace Finsler.SelfCutPrismCoboundary
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison Finsler.SmallChainCarrier
open Finsler.SupportedCapNaturality Finsler.SelfCutThomCocycle
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

def primitive (n p : ℕ) (T : singularCochainGroup (ZMod 2) (parameters n) (p + 1)) :
    singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p :=
  -(SelfCutTimePrism.prism n p ≫ T)

theorem boundary (n p : ℕ) (T : singularCochainGroup (ZMod 2) (parameters n) (p + 1))
    (h₀ : cochainPullback (atTime n 0) (p + 1) T = 0)
    (h₁ : cochainPullback (atTime n 1) (p + 1) T = 0) :
    cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop n)) p (primitive n p T) =
      SelfCutTimePrism.prism n (p + 1) ≫ cochainCoboundary (ZMod 2) (parameters n) (p + 1) T := by
  have h := congrArg (fun f => f ≫ T) (SelfCutTimePrism.prism_boundary_succ n p)
  have h0 : (push (atTime n 0)).f (p + 1) ≫ T = 0 := h₀
  have h1 : (push (atTime n 1)).f (p + 1) ≫ T = 0 := h₁
  simp only [Preadditive.add_comp, Category.assoc, h0, h1, add_zero] at h
  change (chains (TopCat.of (SphereLoop n))).d (p + 1) p ≫
    (-(SelfCutTimePrism.prism n p ≫ T)) = _
  rw [Preadditive.comp_neg]
  exact (eq_neg_of_add_eq_zero_right h.symm).symm

theorem comparison (n p : ℕ) (T : singularCochainGroup (ZMod 2) (parameters n) (p + 1))
    (A B : singularCochainGroup (ZMod 2) (parameters n) (p + 2))
    (hT : cochainCoboundary (ZMod 2) (parameters n) (p + 1) T = A - B)
    (h₀ : cochainPullback (atTime n 0) (p + 1) T = 0)
    (h₁ : cochainPullback (atTime n 1) (p + 1) T = 0) :
    cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop n)) p (primitive n p T) =
      SelfCutTimePrism.prism n (p + 1) ≫ A - SelfCutTimePrism.prism n (p + 1) ≫ B := by
  rw [boundary n p T h₀ h₁, hT, Preadditive.comp_sub]

theorem cycle_values_eq (n p : ℕ) (T : singularCochainGroup (ZMod 2) (parameters n) (p + 1))
    (A B : singularCochainGroup (ZMod 2) (parameters n) (p + 2))
    (hT : cochainCoboundary (ZMod 2) (parameters n) (p + 1) T = A - B)
    (h₀ : cochainPullback (atTime n 0) (p + 1) T = 0)
    (h₁ : cochainPullback (atTime n 1) (p + 1) T = 0)
    (c : coeff ⟶ (chains (TopCat.of (SphereLoop n))).X (p + 1))
    (hc : c ≫ (chains (TopCat.of (SphereLoop n))).d (p + 1) p = 0) :
    c ≫ SelfCutTimePrism.prism n (p + 1) ≫ A = c ≫ SelfCutTimePrism.prism n (p + 1) ≫ B := by
  have h := congrArg (fun f => c ≫ f) (comparison n p T A B hT h₀ h₁)
  change c ≫ ((chains (TopCat.of (SphereLoop n))).d (p + 1) p ≫ primitive n p T) = _ at h
  rw [← Category.assoc c, hc, zero_comp, Preadditive.comp_sub] at h
  simpa only [Category.assoc] using sub_eq_zero.mp h.symm

end
end Finsler.SelfCutPrismCoboundary
