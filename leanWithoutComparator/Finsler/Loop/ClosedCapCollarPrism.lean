module

public import Finsler.Topology.DoubleCapSourceCollar
public import Finsler.Topology.ClosedCapDegreeTransport
public import Finsler.Topology.TimePrismNaturality

/-! An actual homotopy contained in a first-cochain zero collar is
killed by the genuinely retracted bounded two-cap. The proof factors
the actual prism through that collar, before applying the retained map. -/

@[expose] public section
namespace Finsler.ClosedCapCollarPrism

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 800000

variable {Y Z : TopCat.{0}} {f₀ f₁ : Y ⟶ Z} (H : TopCat.Homotopy f₀ f₁)
  (A : Set Z) (hH : ∀ (s : _root_.unitInterval) (y : Y), H (s, y) ∈ A)

def collarStart (H : TopCat.Homotopy f₀ f₁) (A : Set Z)
    (hH : ∀ (s : _root_.unitInterval) (y : Y), H (s, y) ∈ A) : Y ⟶ TopCat.of A :=
  TopCat.ofHom ⟨fun y => ⟨f₀ y, (show H (0, y) = f₀ y from H.map_zero_left y) ▸ hH 0 y⟩,
    f₀.hom.continuous.subtype_mk _⟩

def collarEnd (H : TopCat.Homotopy f₀ f₁) (A : Set Z)
    (hH : ∀ (s : _root_.unitInterval) (y : Y), H (s, y) ∈ A) : Y ⟶ TopCat.of A :=
  TopCat.ofHom ⟨fun y => ⟨f₁ y, (show H (1, y) = f₁ y from H.map_one_left y) ▸ hH 1 y⟩,
    f₁.hom.continuous.subtype_mk _⟩

def collarHomotopy : TopCat.Homotopy (collarStart H A hH) (collarEnd H A hH) where
  toFun z := ⟨H z, hH z.1 z.2⟩
  continuous_toFun := H.continuous.subtype_mk _
  map_zero_left y := Subtype.ext (H.map_zero_left y)
  map_one_left y := Subtype.ext (H.map_one_left y)

theorem prism_inclusion (d : ℕ) :
    ((collarHomotopy H A hH).toSSet.chainComplexMap coeff).hom d (d + 1) ≫
      (push (SupportedCap.subspaceMap Z A)).f (d + 1) =
        (H.toSSet.chainComplexMap coeff).hom d (d + 1) := by
  have hp := TimePrismNaturality.prism_post (collarHomotopy H A hH) (SupportedCap.subspaceMap Z A) d
  have hc := TimePrismNaturality.prism_congr
    ((TopCat.Homotopy.refl (SupportedCap.subspaceMap Z A)).comp (collarHomotopy H A hH)) H
    (by
      apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro z
      rfl) d
  exact hp.trans hc

private theorem transport_f {C D : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
    (f : C ⟶ D) (i j : ℕ) (h : i = j) :
    eqToHom (congrArg C.X h) ≫ f.f j = f.f i ≫ eqToHom (congrArg D.X h) := by
  subst j
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

variable {ι : Type*} (U : ι → Set Z) (hU : ∀ i, IsOpen (U i)) (hcU : ⋃ i, U i = Set.univ)
  (E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ) (m p : ℕ)
  (c : ∀ q, (small Z U).X ((m + 1) + (p + q)) ⟶ E.X q)
  (φ : singularCochainGroup (ZMod 2) Z (m + 1)) (ψ : singularCochainGroup (ZMod 2) Z p)
  (hφ : cochainPullback (SupportedCap.subspaceMap Z A) (m + 1) φ = 0)
  (j : E ⟶ chains Z) (hj : ∀ q, Mono (j.f q))
  (hi : ∀ q, c q ≫ j.f q = (inclusion Z U).f ((m + 1) + (p + q)) ≫
    PartialDoubleCap.cap Z (m + 1) p q φ ψ)

include hφ hj hi in
theorem map_zero (f : Y ⟶ Z) (hf : ∀ y, f y ∈ A) (q : ℕ) :
    (push f).f ((m + p) + q + 1) ≫ ClosedCapDegreeTransport.align m p
      (fun t => (TauCeti.smallSingularRetraction (X := Z) coeff U hU hcU).f ((m + 1) + (p + t)) ≫ c t) q = 0 := by
  have hz := DoubleCapSourceCollar.lift_zero U A (m + 1) p φ ψ hφ f hf hU hcU E j hj c hi q
  have he := transport_f (push f) ((m + p) + q + 1) ((m + 1) + (p + q)) (by omega)
  dsimp only [ClosedCapDegreeTransport.align]
  rw [← Category.assoc, ← he, Category.assoc]
  change eqToHom _ ≫ ((push f).f ((m + 1) + (p + q)) ≫
    (TauCeti.smallSingularRetraction (X := Z) coeff U hU hcU).f ((m + 1) + (p + q)) ≫ c q) = 0
  rw [hz, comp_zero]

include hH hφ hj hi in
theorem prism_zero (q : ℕ) :
    (H.toSSet.chainComplexMap coeff).hom ((m + p) + q) ((m + p) + q + 1) ≫
      ClosedCapDegreeTransport.align m p
        (fun t => (TauCeti.smallSingularRetraction (X := Z) coeff U hU hcU).f ((m + 1) + (p + t)) ≫ c t) q = 0 := by
  have hz := map_zero (Y := TopCat.of A) A U hU hcU E m p c φ ψ hφ j hj hi
    (SupportedCap.subspaceMap Z A) (fun y => y.property) q
  rw [← prism_inclusion H A hH ((m + p) + q), Category.assoc, hz, comp_zero]

end
end Finsler.ClosedCapCollarPrism
