module

public import Finsler.Analysis.ReversalFamily
public import Finsler.Topology.CriticalCircles

/-! choose neighbourhoods of positive compact sets so that both
ordinary and reversal-cross disjointness hold. -/

@[expose] public section

namespace Finsler.ReversalSeparation

open Set Finsler.ReversalFamily Finsler.CriticalCircles
noncomputable section
set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*} [Fintype ι]

theorem exists_separated_neighbourhoods (r : E →L[ℝ] E) (hr : ∀ x, r (r x) = x)
    (Γ : ι → Set E) (hΓ : ∀ i, IsCompact (Γ i))
    (hdis : ∀ i j, i ≠ j → Disjoint (Γ i) (Γ j))
    (hcross : ∀ i j, Disjoint (Γ i) (r ⁻¹' Γ j)) :
    ∃ U : ι → Set E, (∀ i, IsOpen (U i) ∧ Γ i ⊆ U i) ∧
      (∀ i j, i ≠ j → Disjoint (U i) (U j)) ∧
      ∀ i j, Disjoint (U i) (r ⁻¹' U j) := by
  classical
  obtain ⟨V, hV, hVdis⟩ := exists_disjoint_nhds Finset.univ (setFamily r Γ)
    (fun p _ => set_isCompact r hr hΓ p)
    (fun p _ q _ hpq => sets_disjoint r hdis hcross p q hpq)
  let U : ι → Set E := fun i => V (i, true) ∩ r ⁻¹' V (i, false)
  refine ⟨U, ?_, ?_, ?_⟩
  · intro i
    refine ⟨(hV (i, true) (Finset.mem_univ _)).1.inter
      ((hV (i, false) (Finset.mem_univ _)).1.preimage r.continuous), ?_⟩
    intro x hx
    refine ⟨(hV (i, true) (Finset.mem_univ _)).2 hx,
      (hV (i, false) (Finset.mem_univ _)).2 ?_⟩
    change r (r x) ∈ Γ i
    rwa [hr]
  · intro i j hij
    exact (hVdis (Finset.mem_univ (i, true)) (Finset.mem_univ (j, true))
      (fun he => hij (congrArg Prod.fst he))).mono inter_subset_left inter_subset_left
  · intro i j
    apply Set.disjoint_left.mpr
    intro x hx hy
    have hj : x ∈ V (j, false) := by
      have he : r (r x) ∈ V (j, false) := hy.2
      rwa [hr] at he
    exact Set.disjoint_left.mp (hVdis (Finset.mem_univ (i, true)) (Finset.mem_univ (j, false))
      (by intro he; have hb := congrArg Prod.snd he; cases hb)) hx.1 hj

end

end Finsler.ReversalSeparation
