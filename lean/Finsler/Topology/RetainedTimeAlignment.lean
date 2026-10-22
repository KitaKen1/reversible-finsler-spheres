module

public import Finsler.Topology.ClosedCapFunctoriality

/-! Preserve an actual cap agreement while composing the specified
source retraction and aligning its original annular time degree. -/

@[expose] public section
namespace Finsler.RetainedTimeAlignment

open CategoryTheory
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

theorem agreement {K C E F D : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
    (R : K ⟶ C) (M : C ⟶ F) (j : E ⟶ D) (m p : ℕ)
    (c : ∀ q, C.X ((m + 1) + (p + q)) ⟶ E.X q)
    (d : ∀ q, F.X ((m + 1) + (p + q)) ⟶ D.X q)
    (hc : ∀ q, c q ≫ j.f q = M.f ((m + 1) + (p + q)) ≫ d q) (q : ℕ) :
    ClosedCapDegreeTransport.align m p (fun s => R.f ((m + 1) + (p + s)) ≫ c s) q ≫ j.f q =
      (R ≫ M).f ((m + p) + q + 1) ≫ ClosedCapDegreeTransport.align m p d q := by
  calc
    _ = ClosedCapDegreeTransport.align m p
        (fun s => (R.f ((m + 1) + (p + s)) ≫ c s) ≫ j.f s) q :=
      (ClosedCapFunctoriality.align_post j m p _ q).symm
    _ = ClosedCapDegreeTransport.align m p (fun s => (R ≫ M).f ((m + 1) + (p + s)) ≫ d s) q := by
      apply congrArg (fun z => ClosedCapDegreeTransport.align m p z q)
      funext s
      rw [HomologicalComplex.comp_f, Category.assoc, hc s, Category.assoc]
    _ = _ := ClosedCapFunctoriality.align_pre (R ≫ M) m p d q

end
end Finsler.RetainedTimeAlignment
