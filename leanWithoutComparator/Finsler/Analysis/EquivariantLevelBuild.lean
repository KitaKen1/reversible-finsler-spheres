module

public import Finsler.Analysis.LevelBuild
public import Finsler.Analysis.LabelFamilyAverage
public import Finsler.Analysis.EquivariantGroupAverage

/-! A compatible finite family of local labels has a global equivariant descent field.
Average the existing glued field, retaining its values on the prescribed compact tubes.
Strictness only needs the original summand, so the band need not be invariant. -/

@[expose] public section

namespace Finsler.EquivariantLevelBuild

open Set Finsler.LevelBuild Finsler.LabelFamilyAverage Finsler.EquivariantField
open Finsler.EquivariantGroupAverage
open scoped ContDiff
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι]

theorem exists_equivariant_level_field
    (r h : E →L[ℝ] E) (hr : ∀ x, r (r x) = x) (hh : ∀ x, h (h x) = x)
    (hrh : ∀ x, r (h x) = h (r x)) (rev : ι → ι)
    {f : E → ℝ} {O B Crit : Set E} {U : ι → Set E} {W : ι → E → E}
    {β : ι → E → ℝ} {C T : ι → Set E}
    (hfr : ∀ x, f (r x) = f x) (hfh : ∀ x, f (h x) = f x)
    (hOr : ∀ x ∈ O, r x ∈ O) (hOh : ∀ x ∈ O, h x ∈ O)
    (hf : ∀ x ∈ O, DifferentiableAt ℝ f x)
    (hβr : ∀ x, (∑ i, β i (r x)) = ∑ i, β i x)
    (hβh : ∀ x, (∑ i, β i (h x)) = ∑ i, β i x)
    (hU : ∀ i, IsOpen (U i)) (hUO : ∀ i, U i ⊆ O)
    (hUdis : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hW : ∀ i, ContDiffOn ℝ ∞ (W i) (U i))
    (hWle : ∀ i, ∀ y ∈ U i, fderiv ℝ f y (W i y) ≤ 0)
    (hWlt : ∀ i, ∀ y ∈ U i, y ∉ C i → fderiv ℝ f y (W i y) < 0)
    (hT : ∀ i, IsCompact (T i)) (hTU : ∀ i, T i ⊆ U i)
    (hTr : ∀ i x, x ∈ T i → r x ∈ T (rev i))
    (hTh : ∀ i x, x ∈ T i → h x ∈ T i)
    (hWr : ∀ i x, x ∈ T i → W (rev i) (r x) = r (W i x))
    (hWh : ∀ i x, x ∈ T i → W i (h x) = h (W i x))
    (hβT : ∀ i, tsupport (β i) ⊆ T i)
    (hβd : ∀ i y, DifferentiableAt ℝ (β i) y)
    (hβle : ∀ i, ∀ y ∈ tsupport (β i), fderiv ℝ (fun y => f y + β i y) y (W i y) ≤ 0)
    (hβlt : ∀ i, ∀ y ∈ tsupport (β i), y ∉ C i →
      fderiv ℝ (fun y => f y + β i y) y (W i y) < 0)
    (hcrit : Crit ⊆ ⋃ i, T i)
    (hband : ∀ 𝒲 : Set E, IsOpen 𝒲 → Crit ⊆ 𝒲 → ∃ V : E → E, ContDiff ℝ ∞ V ∧
      HasCompactSupport V ∧ tsupport V ⊆ O ∧ (∀ y ∈ O, fderiv ℝ f y (V y) ≤ 0) ∧
      ∀ y ∈ B, y ∉ 𝒲 → fderiv ℝ f y (V y) < 0) :
    ∃ V : E → E, ContDiff ℝ ∞ V ∧ HasCompactSupport V ∧ tsupport V ⊆ O ∧
      (∀ i, ∀ y ∈ T i, V y = W i y) ∧
      (∀ x, V (r x) = r (V x)) ∧ (∀ x, V (h x) = h (V x)) ∧
      (∀ y ∈ O, fderiv ℝ (fun y => f y + ∑ i, β i y) y (V y) ≤ 0) ∧
      ∀ y ∈ O, y ∈ B → (∀ i, y ∉ C i) →
        fderiv ℝ (fun y => f y + ∑ i, β i y) y (V y) < 0 := by
  classical
  obtain ⟨V, hV, hVc, hVO, hVT, hVle, hVlt⟩ := exists_level_field Finset.univ
    (fun i _ => hU i) (fun i _ => hUO i) (fun i _ j _ hij => hUdis i j hij)
    (fun i _ => hW i) (fun i _ => hWle i) (fun i _ => hWlt i)
    (fun i _ => hT i) (fun i _ => hTU i) (fun i _ => hβT i)
    (fun i _ => hβle i) (fun i _ => hβlt i) (by simpa using hcrit) hband
  let g : E → ℝ := fun y => f y + ∑ i, β i y
  have hgr : ∀ x, g (r x) = g x := fun x => by dsimp [g]; rw [hfr, hβr]
  have hgh : ∀ x, g (h x) = g x := fun x => by dsimp [g]; rw [hfh, hβh]
  have hg : ∀ x ∈ O, DifferentiableAt ℝ g x := fun x hx =>
    (hf x hx).add (DifferentiableAt.fun_sum fun i _ => hβd i x)
  refine ⟨avg r h V, avg_contDiff r h hrh hV, avg_hasCompactSupport r h hr hh hrh hVc,
    avg_tsupport_subset r h hr hh hrh hVO hOr hOh, ?_, avg_r hr hrh V,
    avg_h hh hrh V, ?_, ?_⟩
  · intro i y hy
    exact avg_eq_on_family r h hr hh hrh rev T W V hTr hTh
      (fun i x hx => hVT i (Finset.mem_univ i) x hx) hWr hWh hy
  · intro y hy
    exact avg_nonpos_on r h hr hh hrh hgr hgh hg hOr hOh hVle hy
  · intro y hy hyB hyC
    exact avg_strict_of_nonpos r h hr hh hrh hgr hgh hg hOr hOh hVle hy
      (hVlt y hy hyB (fun i _ => hyC i))

end

end Finsler.EquivariantLevelBuild
