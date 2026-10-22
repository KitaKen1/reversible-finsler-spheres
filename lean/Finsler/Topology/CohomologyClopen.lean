module

public import Finsler.Topology.DiagonalCohomology
public import TauCeti.AlgebraicTopology.Cohomology.Additivity

/-! Actual absolute cohomology is detected on a finite disjoint union.
This is used for the separated far set and diagonal, before choosing a
Thom cocycle vanishing on both. -/

@[expose] public section
namespace Finsler.CohomologyClopen

open CategoryTheory CategoryTheory.Limits SphereOddDegree
open Finsler.CochainComparison Finsler.BorelEvaluation
open Set

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

theorem sigma_eq_zero {ι : Type} (X : ι → TopCat.{0}) (k : ℕ)
    (a : cohomologyZMod2 (TopCat.of (Σ i, X i)) k)
    (ha : ∀ i, (cohPullback (TopCat.sigmaι X i) k).hom a = 0) : a = 0 := by
  let A := (TopCat.of (Σ i, X i)).singularCohomology coeff (ZMod 2) coeff k
  let b : A := (cohomologyEquiv _ k) a
  let f : ModuleCat.of (ZMod 2) (ZMod 2) ⟶ A :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton (ZMod 2) A b)
  have hf : f = 0 := by
    apply Fan.IsLimit.hom_ext (TauCeti.isLimitFanSingularCohomology X
      (ModuleCat (ZMod 2)) coeff (ZMod 2) coeff k)
    intro i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    simp only [fan_mk_proj, zero_comp]
    change (TopCat.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff)
      (TopCat.sigmaι X i) k).hom (r • b) = 0
    rw [map_smul]
    have hi : (TopCat.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff)
        (TopCat.sigmaι X i) k).hom b = 0 := by
      have h := cohomology_natural_apply (TopCat.sigmaι X i) k a
      rw [ha i, map_zero] at h
      exact h.symm
    rw [hi, smul_zero]
  have hb := ConcreteCategory.congr_hom hf (1 : ZMod 2)
  change (1 : ZMod 2) • b = 0 at hb
  rw [one_smul] at hb
  exact (cohomologyEquiv _ k).injective (hb.trans (map_zero _).symm)

def unionMap {X : Type} [TopologicalSpace X] (s : Bool → Set X) :
    (Σ i, s i) → (⋃ i, s i) :=
  fun z => ⟨z.2.val, mem_iUnion.mpr ⟨z.1, z.2.property⟩⟩

theorem continuous_unionMap {X : Type} [TopologicalSpace X] (s : Bool → Set X) :
    Continuous (unionMap s) :=
  (continuous_sigma fun _ => continuous_subtype_val).subtype_mk _

theorem unionMap_bijective {X : Type} [TopologicalSpace X] (s : Bool → Set X)
    (hdis : Disjoint (s false) (s true)) : Function.Bijective (unionMap s) := by
  constructor
  · rintro ⟨i, x⟩ ⟨j, y⟩ h
    have he : x.val = y.val := congrArg Subtype.val h
    have hij : i = j := by
      cases i <;> cases j
      · rfl
      · exact False.elim (Set.disjoint_left.mp hdis x.property (he.symm ▸ y.property))
      · exact False.elim (Set.disjoint_left.mp hdis y.property (he ▸ x.property))
      · rfl
    subst j
    exact Sigma.ext rfl (heq_of_eq (Subtype.ext he))
  · intro x
    obtain ⟨i, hi⟩ := mem_iUnion.mp x.property
    exact ⟨⟨i, x.val, hi⟩, Subtype.ext rfl⟩

def unionHomeomorph {X : Type} [TopologicalSpace X] [T2Space X]
    (s : Bool → Set X) (hs : ∀ i, IsCompact (s i))
    (hdis : Disjoint (s false) (s true)) : (Σ i, s i) ≃ₜ (⋃ i, s i) := by
  letI (i : Bool) : CompactSpace (s i) := isCompact_iff_compactSpace.mp (hs i)
  exact Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (unionMap s) (unionMap_bijective s hdis)) (continuous_unionMap s)

def unionInclusion {X : Type} [TopologicalSpace X] (s : Bool → Set X) (i : Bool) :
    TopCat.of (s i) ⟶ TopCat.of (⋃ i, s i) :=
  TopCat.ofHom ⟨fun x => ⟨x.val, mem_iUnion.mpr ⟨i, x.property⟩⟩,
    continuous_subtype_val.subtype_mk _⟩

theorem union_eq_zero {X : Type} [TopologicalSpace X] [T2Space X]
    (s : Bool → Set X) (hs : ∀ i, IsCompact (s i))
    (hdis : Disjoint (s false) (s true)) (k : ℕ)
    (a : cohomologyZMod2 (TopCat.of (⋃ i, s i)) k)
    (ha : ∀ i, (cohPullback (unionInclusion s i) k).hom a = 0) : a = 0 := by
  let Y : Bool → TopCat.{0} := fun i => TopCat.of (s i)
  let e := unionHomeomorph s hs hdis
  let f : TopCat.of (Σ i, Y i) ⟶ TopCat.of (⋃ i, s i) :=
    TopCat.ofHom ⟨e, e.continuous⟩
  let g : TopCat.of (⋃ i, s i) ⟶ TopCat.of (Σ i, Y i) :=
    TopCat.ofHom ⟨e.symm, e.symm.continuous⟩
  have hz : (cohPullback f k).hom a = 0 := by
    apply sigma_eq_zero Y k
    intro i
    rw [← Cup.pullback_comp]
    have he : TopCat.sigmaι Y i ≫ f = unionInclusion s i := by
      ext x : 1
      rfl
    rw [he, ha i]
  have hid : g ≫ f = 𝟙 _ := by
    ext x : 1
    exact e.apply_symm_apply x
  have h := congrArg (cohPullback g k).hom hz
  rw [← Cup.pullback_comp, hid, Finsler.DiagonalCohomology.pullback_id, map_zero] at h
  exact h

end
end Finsler.CohomologyClopen
