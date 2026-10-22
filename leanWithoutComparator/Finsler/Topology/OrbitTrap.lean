module

public import Finsler.Topology.LensTrap

/-! Trapping of whole orbits up to the lens time. Let a descent of g be given, open sets
𝒲' ⊆ 𝒲 and 𝒱 with 𝒲 and 𝒱 disjoint, and a time τ ≥ 0 such that the points below b which the
flow does not take below a in time τ lie in 𝒲' ∪ 𝒱, and the orbits of the points of 𝒲' stay in
𝒲 up to the time τ (a margin). Then for every time T ≥ τ the orbit of a point of 𝒲 below b which
the flow does not take below a in time T stays in 𝒲 up to the time T: up to the time T - τ the
orbit lies in 𝒲' ∪ 𝒱, so in 𝒲' because it is connected and starts in 𝒲, and the margin covers
the remaining time τ. On a compact band with strict decrease of the time-one map outside
𝒲' ∪ 𝒱 this holds for all sufficiently tight cuts with τ = 1. This is the trapping hypothesis of
the transport of lens pairs between two systems. -/

@[expose] public section

namespace Finsler.OrbitTrap

open Set Topology Finsler.FlowLens Finsler.LensTrap

noncomputable section

variable {W : TopCat.{0}} {g : W → ℝ} (D : Descent W g)

/-- **Trapping of whole orbits.** -/
theorem orbit_trap {𝒲 𝒲' 𝒱 : Set W} (h𝒲' : IsOpen 𝒲') (h𝒱 : IsOpen 𝒱) (hsub : 𝒲' ⊆ 𝒲)
    (hdis : Disjoint 𝒲 𝒱) {τ a b T : ℝ} (hτ : 0 ≤ τ) (hτT : τ ≤ T)
    (hcore : ∀ v, g v < b → a ≤ g (D.flow τ v) → v ∈ 𝒲' ∪ 𝒱)
    (hmargin : ∀ v ∈ 𝒲', ∀ s, 0 ≤ s → s ≤ τ → D.flow s v ∈ 𝒲)
    (w : W) (hw : w ∈ 𝒲) (hb : g w < b) (ha : a ≤ g (D.flow T w)) (s : ℝ) (hs : 0 ≤ s)
    (hsT : s ≤ T) : D.flow s w ∈ 𝒲 := by
  set s₁ := T - τ with hs₁
  have hs₁0 : 0 ≤ s₁ := sub_nonneg.mpr hτT
  have hcont : Continuous fun r : ℝ => D.flow r w :=
    D.cont.comp (continuous_id.prodMk continuous_const)
  have hmem : ∀ r, r ∈ Icc (0 : ℝ) s₁ → D.flow r w ∈ 𝒲' ∪ 𝒱 := by
    intro r hr
    refine hcore _ (lt_of_le_of_lt (D.mono r w hr.1) hb) (ha.trans ?_)
    have h : D.flow τ (D.flow r w) = D.flow (τ + r) w := (D.add τ r w hτ hr.1).symm
    rw [h]
    exact mono_time D (add_nonneg hτ hr.1) (by linarith [hr.2]) w
  have hdis' : Disjoint 𝒲' 𝒱 := hdis.mono_left hsub
  have hin : ∀ r, r ∈ Icc (0 : ℝ) s₁ → D.flow r w ∈ 𝒲' := by
    intro r hr
    have hpre : IsPreconnected (Icc (0 : ℝ) r) := isPreconnected_Icc
    have hsubU : Icc (0 : ℝ) r ⊆ (fun r : ℝ => D.flow r w) ⁻¹' 𝒲' ∪
        (fun r : ℝ => D.flow r w) ⁻¹' 𝒱 := fun r' hr' =>
      hmem r' ⟨hr'.1, hr'.2.trans hr.2⟩
    have hw0 : D.flow 0 w ∈ 𝒲' := by
      have h0 := hmem 0 ⟨le_rfl, hs₁0⟩
      rw [D.zero] at h0 ⊢
      exact h0.resolve_right fun h𝒱w => Set.disjoint_left.mp hdis hw h𝒱w
    have hne : (Icc (0 : ℝ) r ∩ (fun r : ℝ => D.flow r w) ⁻¹' 𝒲').Nonempty :=
      ⟨0, ⟨le_rfl, hr.1⟩, hw0⟩
    by_contra hnot
    have hr𝒱 : D.flow r w ∈ 𝒱 := (hmem r hr).resolve_left hnot
    obtain ⟨r', -, hr'1, hr'2⟩ := hpre _ _ (h𝒲'.preimage hcont) (h𝒱.preimage hcont) hsubU hne
      ⟨r, ⟨hr.1, le_rfl⟩, hr𝒱⟩
    exact (Set.disjoint_left.mp hdis') hr'1 hr'2
  by_cases hss : s ≤ s₁
  · exact hsub (hin s ⟨hs, hss⟩)
  · rw [not_le] at hss
    have h1 := hin s₁ ⟨hs₁0, le_rfl⟩
    have h2 := hmargin _ h1 (s - s₁) (by linarith) (by linarith)
    rwa [← D.add (s - s₁) s₁ w (by linarith) hs₁0, sub_add_cancel] at h2

/-- **Trapping of whole orbits on a compact band.** If the time-one map decreases g strictly at
the points of a compact band outside 𝒲' ∪ 𝒱, and the orbits of the points of 𝒲' stay in 𝒲 up
to the time one, then for all sufficiently tight cuts in the band and every time T ≥ 1 the
orbit of a point of 𝒲 below b which the flow does not take below a in time T stays in 𝒲 up to
the time T. -/
theorem exists_orbit_trap (hg : Continuous g) {a₀ b₀ : ℝ} {𝒲 𝒲' 𝒱 : Set W} (h𝒲' : IsOpen 𝒲')
    (h𝒱 : IsOpen 𝒱) (hsub : 𝒲' ⊆ 𝒲) (hdis : Disjoint 𝒲 𝒱)
    (hK : IsCompact {w : W | a₀ ≤ g w ∧ g w ≤ b₀})
    (hstrict : ∀ w, a₀ ≤ g w → g w ≤ b₀ → w ∉ 𝒲' ∪ 𝒱 → g (D.flow 1 w) < g w)
    (hmargin : ∀ v ∈ 𝒲', ∀ s, 0 ≤ s → s ≤ 1 → D.flow s v ∈ 𝒲) :
    ∃ d : ℝ, 0 < d ∧ ∀ a b T : ℝ, a₀ ≤ a → b ≤ b₀ → b - a < d → 1 ≤ T →
      ∀ w ∈ 𝒲, g w < b → a ≤ g (D.flow T w) → ∀ s, 0 ≤ s → s ≤ T → D.flow s w ∈ 𝒲 := by
  obtain ⟨d, hd, htrap⟩ := exists_trap D hg (h𝒲'.union h𝒱) hK hstrict
  refine ⟨d, hd, fun a b T ha hb hab hT w hw hwb hwa s hs hsT => ?_⟩
  exact orbit_trap D h𝒲' h𝒱 hsub hdis zero_le_one hT
    (fun v hv hv' => htrap a b 1 ha hb hab le_rfl v hv hv') hmargin w hw hwb hwa s hs hsT

end

end Finsler.OrbitTrap
