module

public import Finsler.Topology.PartialDoubleCapFiltered

/-! Refine an actual nested cap on its source small chains, preserving
its boundary identity and its specified actual ambient two-cap image. -/

@[expose] public section
namespace Finsler.NestedCapRefinement

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

def pre {K C E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ} (k p : ℕ) (f : K ⟶ C)
    (c : ∀ q, C.X (k + (p + q)) ⟶ E.X q) (q : ℕ) : K.X (k + (p + q)) ⟶ E.X q :=
  f.f (k + (p + q)) ≫ c q

theorem pre_comm {K C E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ} (k p : ℕ) (f : K ⟶ C)
    (c : ∀ q, C.X (k + (p + q)) ⟶ E.X q)
    (hc : ∀ q, c (q + 1) ≫ E.d (q + 1) q = C.d (k + (p + (q + 1))) (k + (p + q)) ≫ c q) (q : ℕ) :
    pre k p f c (q + 1) ≫ E.d (q + 1) q = K.d (k + (p + (q + 1))) (k + (p + q)) ≫ pre k p f c q := by
  dsimp only [pre]
  rw [Category.assoc, hc q, ← Category.assoc, f.comm, Category.assoc]

theorem pre_inclusion (X : TopCat.{0}) {ι κ : Type*} (U : ι → Set X) (V : κ → Set X)
    (f : small X V ⟶ small X U) (hf : f ≫ inclusion X U = inclusion X V)
    (E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ) (j : E ⟶ chains X) (k p : ℕ)
    (φ : singularCochainGroup (ZMod 2) X k) (ψ : singularCochainGroup (ZMod 2) X p)
    (c : ∀ q, (small X U).X (k + (p + q)) ⟶ E.X q)
    (hc : ∀ q, c q ≫ j.f q = (inclusion X U).f (k + (p + q)) ≫ PartialDoubleCap.cap X k p q φ ψ) (q : ℕ) :
    pre k p f c q ≫ j.f q = (inclusion X V).f (k + (p + q)) ≫ PartialDoubleCap.cap X k p q φ ψ := by
  dsimp only [pre]
  rw [Category.assoc, hc q, ← Category.assoc, ← HomologicalComplex.comp_f, hf]

end
end Finsler.NestedCapRefinement
