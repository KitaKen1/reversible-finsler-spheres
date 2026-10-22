module

public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import TauCeti.Analysis.InnerProductSpace.Spectrum

/-! Linear spectral splitting without a nondegeneracy assumption. Tau Ceti supplies eigenvector
spans of the ordered eigenbasis. The span of the zero eigenvalues is the actual kernel, and the
negative, positive and zero spans together give the whole space. The restriction to the nonzero
spectral subspace is invertible even when the full operator is singular. This is linear data for
a degenerate splitting lemma, not a nonlinear normal form. -/

@[expose] public section

namespace Finsler.HessianSplitting

open Set Module
open scoped Topology RealInnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (T : E →L[ℝ] E) (hT : T.toLinearMap.IsSymmetric)

/-- The span of the eigenvectors with negative eigenvalue. -/
def negative : Submodule ℝ E := hT.eigenvectorSpan rfl {i | hT.eigenvalues rfl i < 0}

/-- The span of the eigenvectors with positive eigenvalue. -/
def positive : Submodule ℝ E := hT.eigenvectorSpan rfl {i | 0 < hT.eigenvalues rfl i}

/-- The span of the eigenvectors with eigenvalue zero. -/
def zeroSpace : Submodule ℝ E := hT.eigenvectorSpan rfl {i | hT.eigenvalues rfl i = 0}

/-- The span of the eigenvectors with nonzero eigenvalue. -/
def transverse : Submodule ℝ E := negative T hT ⊔ positive T hT

/-- The negative part is the negative spectral subspace of Tau Ceti. -/
theorem negative_eq : negative T hT = hT.negativeSpectralSubspace rfl := by
  ext v
  rw [negative, hT.mem_negativeSpectralSubspace_iff, hT.mem_eigenvectorSpan_iff]
  exact Iff.rfl

/-- The positive part is the positive spectral subspace of Tau Ceti. -/
theorem positive_eq : positive T hT = hT.positiveSpectralSubspace rfl := by
  ext v
  rw [positive, hT.mem_positiveSpectralSubspace_iff, hT.mem_eigenvectorSpan_iff]
  exact Iff.rfl

/-- The coordinates of the image in the eigenbasis are the coordinates multiplied by the
eigenvalues. -/
theorem repr_apply (v : E) (i : Fin (finrank ℝ E)) :
    (hT.eigenvectorBasis rfl).repr (T v) i =
      hT.eigenvalues rfl i * (hT.eigenvectorBasis rfl).repr v i := by
  simpa using hT.eigenvectorBasis_apply_self_apply rfl v i

/-- Zero spectral directions are exactly the actual kernel, with no injectivity assumption. -/
theorem zeroSpace_eq_ker : zeroSpace T hT = LinearMap.ker T.toLinearMap := by
  ext v
  rw [zeroSpace, hT.mem_eigenvectorSpan_iff, LinearMap.mem_ker]
  constructor
  · intro hv
    apply (hT.eigenvectorBasis rfl).repr.injective
    ext i
    change (hT.eigenvectorBasis rfl).repr (T v) i = (hT.eigenvectorBasis rfl).repr 0 i
    rw [repr_apply, map_zero]
    by_cases hc : (hT.eigenvectorBasis rfl).repr v i = 0
    · rw [hc, mul_zero]
      rfl
    · have hi : i ∈ ((hT.eigenvectorBasis rfl).toBasis.repr v).support := by
        rw [Finsupp.mem_support_iff, OrthonormalBasis.coe_toBasis_repr_apply]
        exact hc
      have hz : hT.eigenvalues rfl i = 0 := hv (Finset.mem_coe.mpr hi)
      rw [hz, zero_mul]
      rfl
  · intro hv i hi
    have hc : (hT.eigenvectorBasis rfl).repr v i ≠ 0 := by
      have h := Finsupp.mem_support_iff.mp (Finset.mem_coe.mp hi)
      rwa [OrthonormalBasis.coe_toBasis_repr_apply] at h
    have he := repr_apply T hT v i
    have hv' : T v = 0 := hv
    rw [hv', map_zero] at he
    have he' : hT.eigenvalues rfl i * (hT.eigenvectorBasis rfl).repr v i = 0 := he.symm
    exact (mul_eq_zero.mp he').resolve_right hc

theorem negative_disjoint_positive : Disjoint (negative T hT) (positive T hT) :=
  hT.disjoint_eigenvectorSpan rfl
    (Set.disjoint_left.2 fun i (hneg : hT.eigenvalues rfl i < 0)
      (hpos : 0 < hT.eigenvalues rfl i) => lt_asymm hneg hpos)

/-- The nonzero spectral subspace as one eigenvector span. -/
theorem transverse_eq : transverse T hT =
    hT.eigenvectorSpan rfl ({i | hT.eigenvalues rfl i < 0} ∪ {i | 0 < hT.eigenvalues rfl i}) :=
  (hT.eigenvectorSpan_union rfl _ _).symm

theorem transverse_disjoint_zero : Disjoint (transverse T hT) (zeroSpace T hT) := by
  rw [transverse_eq]
  refine hT.disjoint_eigenvectorSpan rfl (Set.disjoint_left.2 ?_)
  rintro i (hi | hi) (hz : hT.eigenvalues rfl i = 0)
  · exact (ne_of_lt (show hT.eigenvalues rfl i < 0 from hi)) hz
  · exact (ne_of_gt (show 0 < hT.eigenvalues rfl i from hi)) hz

/-- All three spectral parts span the whole space, including degenerate directions. -/
theorem transverse_sup_zero : transverse T hT ⊔ zeroSpace T hT = ⊤ := by
  rw [transverse_eq, zeroSpace, ← hT.eigenvectorSpan_union rfl]
  have hs : ({i | hT.eigenvalues rfl i < 0} ∪ {i | 0 < hT.eigenvalues rfl i}) ∪
      {i | hT.eigenvalues rfl i = 0} = Set.univ := by
    refine Set.eq_univ_of_forall fun i => ?_
    rcases lt_trichotomy (hT.eigenvalues rfl i) 0 with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
    · exact Or.inl (Or.inr h)
  rw [hs, hT.eigenvectorSpan_univ rfl]

theorem transverse_isCompl_ker : IsCompl (transverse T hT) (LinearMap.ker T.toLinearMap) := by
  rw [← zeroSpace_eq_ker T hT]
  exact ⟨transverse_disjoint_zero T hT, codisjoint_iff.mpr (transverse_sup_zero T hT)⟩

theorem exists_three_parts (v : E) :
    ∃ a ∈ negative T hT, ∃ b ∈ positive T hT, ∃ c ∈ LinearMap.ker T.toLinearMap,
      a + b + c = v := by
  have hv : v ∈ transverse T hT ⊔ LinearMap.ker T.toLinearMap := by
    rw [← zeroSpace_eq_ker T hT, transverse_sup_zero]
    trivial
  obtain ⟨u, hu, c, hc, huv⟩ := Submodule.mem_sup.mp hv
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hu
  exact ⟨a, ha, b, hb, c, hc, by rw [hab, huv]⟩

theorem map_negative_mem {v : E} (hv : v ∈ negative T hT) : T v ∈ negative T hT :=
  hT.map_eigenvectorSpan_le rfl _ (Submodule.mem_map.mpr ⟨v, hv, rfl⟩)

theorem map_positive_mem {v : E} (hv : v ∈ positive T hT) : T v ∈ positive T hT :=
  hT.map_eigenvectorSpan_le rfl _ (Submodule.mem_map.mpr ⟨v, hv, rfl⟩)

theorem map_transverse_mem {v : E} (hv : v ∈ transverse T hT) : T v ∈ transverse T hT := by
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hv
  rw [← hab, map_add]
  exact Submodule.add_mem _ (Submodule.mem_sup_left (map_negative_mem T hT ha))
    (Submodule.mem_sup_right (map_positive_mem T hT hb))

/-- The genuine restriction of the symmetric operator to its nonzero spectral subspace. -/
def transverseMap : transverse T hT →ₗ[ℝ] transverse T hT :=
  T.toLinearMap.restrict fun _ hv => map_transverse_mem T hT hv

theorem transverseMap_apply (v : transverse T hT) : (transverseMap T hT v : E) = T v := rfl

theorem transverseMap_injective : Function.Injective (transverseMap T hT) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro a ha
  have hker : (a : E) ∈ LinearMap.ker T.toLinearMap := by
    have h := congrArg Subtype.val ha
    exact h
  have hboth : (a : E) ∈ transverse T hT ⊓ LinearMap.ker T.toLinearMap := ⟨a.2, hker⟩
  rw [(transverse_isCompl_ker T hT).disjoint.eq_bot] at hboth
  exact Subtype.ext ((Submodule.mem_bot ℝ).mp hboth)

/-- The transverse operator is genuinely invertible in finite dimension, without assuming that
the whole operator is invertible. -/
def transverseEquiv : transverse T hT ≃L[ℝ] transverse T hT :=
  (LinearEquiv.ofInjectiveEndo (transverseMap T hT)
    (transverseMap_injective T hT)).toContinuousLinearEquiv

theorem transverseEquiv_apply (v : transverse T hT) :
    (transverseEquiv T hT v : E) = T v := rfl

/-- The dimension of the negative part counts the negative eigenvalues with multiplicity. -/
theorem finrank_negative :
    finrank ℝ (negative T hT) = {i | hT.eigenvalues rfl i < 0}.ncard :=
  hT.finrank_eigenvectorSpan rfl _

/-- The dimension of the positive part counts the positive eigenvalues with multiplicity. -/
theorem finrank_positive :
    finrank ℝ (positive T hT) = {i | 0 < hT.eigenvalues rfl i}.ncard :=
  hT.finrank_eigenvectorSpan rfl _

/-- The nullity counts the zero eigenvalues with multiplicity. -/
theorem finrank_ker :
    finrank ℝ (LinearMap.ker T.toLinearMap) = {i | hT.eigenvalues rfl i = 0}.ncard := by
  rw [← zeroSpace_eq_ker T hT]
  exact hT.finrank_eigenvectorSpan rfl _

/-- Negative dimension, positive dimension and nullity add to the ambient dimension. -/
theorem finrank_three_parts :
    finrank ℝ (negative T hT) + finrank ℝ (positive T hT) +
      finrank ℝ (LinearMap.ker T.toLinearMap) = finrank ℝ E := by
  have hnp := Submodule.finrank_sup_add_finrank_inf_eq (negative T hT) (positive T hT)
  rw [(negative_disjoint_positive T hT).eq_bot, finrank_bot, add_zero] at hnp
  have htk := Submodule.finrank_sup_add_finrank_inf_eq (transverse T hT)
    (LinearMap.ker T.toLinearMap)
  rw [(transverse_isCompl_ker T hT).disjoint.eq_bot, finrank_bot, add_zero,
    (transverse_isCompl_ker T hT).codisjoint.eq_top, finrank_top] at htk
  rw [← hnp]
  exact htk.symm

end

end Finsler.HessianSplitting
