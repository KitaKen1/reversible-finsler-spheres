module

public import Finsler.Topology.SupportedCapCochain

/-! Change a supported cap's actual cochain together with its support
proof. Keep the dependent support witness typed throughout the change. -/
@[expose] public section
namespace Finsler.SupportedCapCochainCongruence
open CategoryTheory SphereOddDegree Finsler.CochainComparison
noncomputable section
set_option autoImplicit false

theorem cut_eq (X : TopCat.{0}) (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (hc : A ∪ B = Set.univ) (p q N : ℕ) (hN : p + q = N)
    (φ ψ : singularCochainGroup (ZMod 2) X p)
    (hφ : cochainPullback (SupportedCap.subspaceMap X A) p φ = 0)
    (hψ : cochainPullback (SupportedCap.subspaceMap X A) p ψ = 0) (he : φ = ψ) :
    SupportedCap.cut X A B hA hB hc p q N hN φ hφ = SupportedCap.cut X A B hA hB hc p q N hN ψ hψ := by
  subst ψ
  rfl

end
end Finsler.SupportedCapCochainCongruence
