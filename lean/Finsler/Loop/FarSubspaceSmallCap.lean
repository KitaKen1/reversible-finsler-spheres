module

public import Finsler.Loop.SmallCapSubspaceLift

/-! Open extension of any genuine subspace cover, with a far set on
which the cochain vanishes. The actual cap lands directly in that
specified small subspace complex; whole parents, not only output faces,
are controlled. -/

@[expose] public section
namespace Finsler.FarSubspaceSmallCap

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.RelativeCapAssociativity
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1400000

variable (X : TopCat.{0}) (D : Set X) {ι : Type*} (U : ι → Set (TopCat.of D))
  (hU : ∀ i, IsOpen (U i))

def extension (i : ι) : Set X := (isOpen_induced_iff.mp (hU i)).choose

theorem extension_open (i : ι) : IsOpen (extension X D U hU i) :=
  (isOpen_induced_iff.mp (hU i)).choose_spec.1

theorem extension_preimage (i : ι) :
    Subtype.val ⁻¹' extension X D U hU i = U i :=
  (isOpen_induced_iff.mp (hU i)).choose_spec.2

variable (A G : Set X)

def cover : Option ι → Set X := fun i => match i with
  | none => A
  | some i => extension X D U hU i ∩ G

theorem cover_open (hA : IsOpen A) (hG : IsOpen G) (i : Option ι) :
    IsOpen (cover X D U hU A G i) := by
  cases i with
  | none => exact hA
  | some i => exact (extension_open X D U hU i).inter hG

theorem cover_univ (hcU : ⋃ i, U i = Set.univ) (hc : A ∪ G = Set.univ) (hGD : G ⊆ D) :
    ⋃ i, cover X D U hU A G i = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  have hz : z ∈ A ∪ G := hc.symm ▸ Set.mem_univ z
  rcases hz with hz | hz
  · exact Set.mem_iUnion.mpr ⟨none, hz⟩
  · let zD : D := ⟨z, hGD hz⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcU.symm ▸ Set.mem_univ zD)
    have he : z ∈ extension X D U hU i := by
      change zD ∈ Subtype.val ⁻¹' extension X D U hU i
      rw [extension_preimage]
      exact hi
    exact Set.mem_iUnion.mpr ⟨some i, he, hz⟩

theorem near_image (hGD : G ⊆ D) (i : ι) :
    cover X D U hU A G (some i) ⊆ SupportedCap.subspaceMap X D '' U i := by
  intro z hz
  let zD : D := ⟨z, hGD hz.2⟩
  have hi : zD ∈ U i := by
    rw [← extension_preimage X D U hU i]
    exact hz.1
  exact ⟨zD, hi, rfl⟩

theorem cover_refines (i : Option ι) :
    cover X D U hU A G i ⊆ A ∨ cover X D U hU A G i ⊆ G := by
  cases i with
  | none => exact Or.inl (Set.Subset.refl _)
  | some i => exact Or.inr (fun _ hz => hz.2)

variable (hGD : G ⊆ D) (d : ℕ) (φ : singularCochainGroup (ZMod 2) X d)
  (hfar : cochainPullback (SupportedCap.subspaceMap X A) d φ = 0)

include hGD hfar in
theorem parent_image (q : ℕ)
    (s : (X.smallSingularSubcomplex (cover X D U hU A G) : SSet) _⦋d + q⦌)
    (hnz : (TopCat.toSSet.obj X).ιChainComplex s.val ≫ absoluteChain X d q (d + q) rfl φ ≠ 0) :
    ∃ i, Set.range (X.toSSetObjEquiv _ s.val) ⊆ SupportedCap.subspaceMap X D '' U i := by
  obtain ⟨i, hi⟩ := (TopCat.mem_smallSingularSubcomplex_iff X (cover X D U hU A G) s.val).mp s.property
  cases i with
  | none => exact (hnz (SupportedCap.cap_zero_on_simplex X A d q (d + q) rfl φ hfar s.val hi)).elim
  | some i => exact ⟨i, hi.trans (near_image X D U hU A G hGD i)⟩

def component (q : ℕ) := SmallCapSubspaceLift.component X (TopCat.of D) D (Iso.refl _)
  (cover X D U hU A G) U d φ
  (fun q s hnz => by
    simpa only [SmallCapSubspaceLift.source, Iso.refl_hom, Category.id_comp] using
      parent_image X D U hU A G hGD d φ hfar q s hnz) q

theorem component_source (q : ℕ) :
    component X D U hU A G hGD d φ hfar q ≫
      (inclusion (TopCat.of D) U ≫ push (SupportedCap.subspaceMap X D)).f q =
    (inclusion X (cover X D U hU A G)).f (d + q) ≫ absoluteChain X d q (d + q) rfl φ := by
  simpa only [component, SmallCapSubspaceLift.target, SmallCapSubspaceLift.source,
    Iso.refl_hom, Category.id_comp] using
    SmallCapSubspaceLift.component_inclusion X (TopCat.of D) D (Iso.refl _)
      (cover X D U hU A G) U d φ
      (fun q s hnz => by
        simpa only [SmallCapSubspaceLift.source, Iso.refl_hom, Category.id_comp] using
          parent_image X D U hU A G hGD d φ hfar q s hnz) q

def operation (hφ : cochainCoboundary (ZMod 2) X d φ = 0) :=
  SmallCapSubspaceLift.operation X (TopCat.of D) D (Iso.refl _)
    (cover X D U hU A G) U d φ
    (fun q s hnz => by
      simpa only [SmallCapSubspaceLift.source, Iso.refl_hom, Category.id_comp] using
        parent_image X D U hU A G hGD d φ hfar q s hnz) hφ

end
end Finsler.FarSubspaceSmallCap
