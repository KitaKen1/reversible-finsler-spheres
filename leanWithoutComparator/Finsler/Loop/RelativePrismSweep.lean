module

public import Finsler.Loop.SelfHomotopySweep
public import Finsler.Loop.HomotopyRangeRestriction
public import Finsler.Topology.RelativeCap
public import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance

/-! Genuine relative time sweeps from ORIGINAL singular prisms.
Endpoint maps landing in the actual subspace vanish in the actual
relative chain quotient. TauCeti's relative homotopy descends the
SECOND prism and identifies its components with the ORIGINAL prism.
No cycle or relative-fundamental existence is assumed. -/
@[expose] public section
namespace Finsler.RelativePrismSweep
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

variable {Y : TopCat.{0}} (B : Set Y)

abbrev targetPair : TopPair.{0} := TopPair.ofSubset (X := Y) B

theorem absolute_relative_zero {X : TopCat.{0}} (f : X ⟶ Y) (hf : ∀ x, f x ∈ B) :
    push f ≫ (targetPair B).singularChainComplexπ coeff = 0 := by
  let g : X ⟶ TopCat.of B := TopCat.ofHom ⟨fun x => ⟨f x, hf x⟩, f.hom.continuous.subtype_mk _⟩
  have he : f = g ≫ (targetPair B).map := by ext x : 1; rfl
  rw [he, push_comp, Category.assoc]
  exact (congrArg (push g ≫ ·) ((targetPair B).chainComplexMap_comp_singularChainComplexπ coeff)).trans (comp_zero)

theorem pair_relative_zero {P : TopPair.{0}} (f : P ⟶ targetPair B)
    (hf : ∀ x, (TopPair.Hom.fst f) x ∈ B) : TopPair.singularChainComplexMap f coeff = 0 := by
  have : Epi (P.singularChainComplexπ coeff) := (P.shortExact_singularChainComplexShortComplex coeff).epi_g
  apply (cancel_epi (P.singularChainComplexπ coeff)).mp
  rw [← TopPair.singularChainComplexπ_pair_naturality, comp_zero]
  exact absolute_relative_zero B (TopPair.Hom.fst f) hf

section Chain
variable {C D : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ} {f g : C ⟶ D}

def zeroEndHomotopy (H : _root_.Homotopy f g) (hf : f = 0) (hg : g = 0) :
    _root_.Homotopy (0 : C ⟶ D) 0 :=
  (_root_.Homotopy.ofEq hf.symm).trans (H.trans (_root_.Homotopy.ofEq hg))

theorem zeroEndHomotopy_hom (H : _root_.Homotopy f g) (hf : f = 0) (hg : g = 0) (p q : ℕ) :
    (zeroEndHomotopy H hf hg).hom p q = H.hom p q := by
  simp only [zeroEndHomotopy, Homotopy.trans_hom, Homotopy.ofEq_hom]
  change (0 : C.X p ⟶ D.X q) + (H.hom p q + 0) = H.hom p q
  rw [zero_add, add_zero]
end Chain

variable {X : TopCat.{0}} {f g : X ⟶ Y}

def ordinary (H : TopCat.Homotopy f g) (hf : ∀ x, f x ∈ B) (hg : ∀ x, g x ∈ B) :
    _root_.Homotopy (0 : chains X ⟶ (targetPair B).singularChainComplex coeff) 0 :=
  zeroEndHomotopy ((H.toSSet.chainComplexMap coeff).compRight ((targetPair B).singularChainComplexπ coeff))
    (absolute_relative_zero B f hf) (absolute_relative_zero B g hg)

theorem ordinary_component (H : TopCat.Homotopy f g) (hf : ∀ x, f x ∈ B) (hg : ∀ x, g x ∈ B) (q : ℕ) :
    SelfHomotopySweep.component (ordinary B H hf hg) q =
      (H.toSSet.chainComplexMap coeff).hom q (q + 1) ≫ ((targetPair B).singularChainComplexπ coeff).f (q + 1) := by
  rw [SelfHomotopySweep.component, ordinary, zeroEndHomotopy_hom]
  rfl

variable {P : TopPair.{0}} {a b : P ⟶ targetPair B}

def relative (H : TopPair.Homotopy a b)
    (ha : ∀ x, (TopPair.Hom.fst a) x ∈ B) (hb : ∀ x, (TopPair.Hom.fst b) x ∈ B) :
    _root_.Homotopy (0 : P.singularChainComplex coeff ⟶ (targetPair B).singularChainComplex coeff) 0 :=
  zeroEndHomotopy (H.singularChainComplexMap coeff) (pair_relative_zero B a ha) (pair_relative_zero B b hb)

theorem relative_component (H : TopPair.Homotopy a b)
    (ha : ∀ x, (TopPair.Hom.fst a) x ∈ B) (hb : ∀ x, (TopPair.Hom.fst b) x ∈ B) (q : ℕ) :
    (P.singularChainComplexπ coeff).f q ≫ SelfHomotopySweep.component (relative B H ha hb) q =
      (H.fst.toSSet.chainComplexMap coeff).hom q (q + 1) ≫ ((targetPair B).singularChainComplexπ coeff).f (q + 1) := by
  rw [SelfHomotopySweep.component, relative, zeroEndHomotopy_hom]
  exact H.singularChainComplexMap_hom coeff q (q + 1)

end
end Finsler.RelativePrismSweep
