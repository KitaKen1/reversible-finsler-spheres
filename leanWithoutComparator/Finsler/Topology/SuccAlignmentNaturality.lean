module

public import Finsler.Topology.DegreeLoweringSuccAlignment
public import Finsler.Topology.ClosedCapDegreeTransport

/-! Literal normal form for the nested original cap degree transport.
The actual source retraction and retained output are preserved. -/

@[expose] public section
namespace Finsler.SuccAlignmentNaturality

open CategoryTheory CategoryTheory.Limits

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false

theorem nested_pre {C D E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
    (f : C ⟶ D) (a s p : ℕ) (u : DegreeLoweringHomology.Map D E (a + (s + 1) + p)) (q : ℕ) :
    ClosedCapDegreeTransport.align (a + s) p
      (fun q => eqToHom (congrArg C.X
        (show ((a + s) + 1) + (p + q) = a + (s + 1) + p + q by omega)) ≫
        (u.pre f).component q) q =
    f.f ((a + s + p) + q + 1) ≫
      DegreeLoweringSuccAlignment.align (a + s + p) u (by omega) q := by
  rw [← DegreeLoweringSuccAlignment.pre]
  dsimp only [ClosedCapDegreeTransport.align, DegreeLoweringSuccAlignment.align]
  rw [← Category.assoc, eqToHom_trans]

theorem post {C D E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ} {m : ℕ}
    (d : ℕ) (u : DegreeLoweringHomology.Map C D m) (hm : m = d + 1) (f : D ⟶ E) (q : ℕ) :
    DegreeLoweringSuccAlignment.align d (u.post f) hm q =
      DegreeLoweringSuccAlignment.align d u hm q ≫ f.f q := by
  simp only [DegreeLoweringSuccAlignment.align, DegreeLoweringHomology.Map.post, Category.assoc]

end
end Finsler.SuccAlignmentNaturality
