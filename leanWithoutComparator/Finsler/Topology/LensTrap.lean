module

public import Finsler.Topology.FlowLens

/-! Trapping and descent for a descending semiflow on a compact band. Let g be continuous with
a descent, and let the band {a₀ ≤ g ≤ b₀} be compact. If the time-one map decreases g strictly
at the points of the band outside an open set 𝒲, there is d > 0 such that for cuts a₀ ≤ a,
b ≤ b₀ with b − a < d and every time T ≥ 1, the points below b which are not taken below a in
time T lie in 𝒲: at such a point the time-one map decreases g by less than d, and the decrease
is bounded below on the compact part of the band outside 𝒲. If the time-one map decreases g
strictly at all points of a compact strip {c₁ ≤ g ≤ c₂}, some time takes the sublevel of c₂
below c₁. If 𝒲 is the union of two disjoint open sets, a point of one of them below b which is
not taken below a stays in it as long as it is not taken below a, since its orbit up to that
time lies in 𝒲 and is connected. -/

@[expose] public section

namespace Finsler.LensTrap

open Set Topology Finsler.FlowLens

noncomputable section

variable {W : TopCat.{0}} {g : W → ℝ} (D : Descent W g)

/-- The value after time T is at most the value after an earlier time. -/
theorem mono_time {s T : ℝ} (hs : 0 ≤ s) (hsT : s ≤ T) (w : W) :
    g (D.flow T w) ≤ g (D.flow s w) := by
  have h : D.flow T w = D.flow (T - s) (D.flow s w) := by
    rw [← D.add (T - s) s w (sub_nonneg.mpr hsT) hs, sub_add_cancel]
  rw [h]
  exact D.mono _ _ (sub_nonneg.mpr hsT)

/-- Trapping: on a compact band on which the time-one map decreases g strictly outside an
open set 𝒲, the points below b not taken below a in time T ≥ 1 lie in 𝒲 if b − a is small. -/
theorem exists_trap (hg : Continuous g) {a₀ b₀ : ℝ} {𝒲 : Set W} (h𝒲 : IsOpen 𝒲)
    (hK : IsCompact {w : W | a₀ ≤ g w ∧ g w ≤ b₀})
    (hstrict : ∀ w, a₀ ≤ g w → g w ≤ b₀ → w ∉ 𝒲 → g (D.flow 1 w) < g w) :
    ∃ d : ℝ, 0 < d ∧ ∀ a b T : ℝ, a₀ ≤ a → b ≤ b₀ → b - a < d → 1 ≤ T →
      ∀ w, g w < b → a ≤ g (D.flow T w) → w ∈ 𝒲 := by
  have hF : IsCompact ({w : W | a₀ ≤ g w ∧ g w ≤ b₀} ∩ 𝒲ᶜ) := hK.inter_right h𝒲.isClosed_compl
  have hc : ContinuousOn (fun w => g w - g (D.flow 1 w))
      ({w : W | a₀ ≤ g w ∧ g w ≤ b₀} ∩ 𝒲ᶜ) :=
    (hg.sub (hg.comp (flow_continuous D 1))).continuousOn
  by_cases hne : ({w : W | a₀ ≤ g w ∧ g w ≤ b₀} ∩ 𝒲ᶜ).Nonempty
  · obtain ⟨w₀, hw₀, hmin⟩ := hF.exists_isMinOn hne hc
    refine ⟨g w₀ - g (D.flow 1 w₀), sub_pos.mpr (hstrict w₀ hw₀.1.1 hw₀.1.2 hw₀.2), ?_⟩
    intro a b T ha hb hd hT w hw hw'
    by_contra hnot
    have h1 : g (D.flow T w) ≤ g (D.flow 1 w) := mono_time D zero_le_one hT w
    have h2 : g (D.flow T w) ≤ g w := D.mono T w (zero_le_one.trans hT)
    have hmem : w ∈ {w : W | a₀ ≤ g w ∧ g w ≤ b₀} ∩ 𝒲ᶜ :=
      ⟨⟨by linarith, by linarith⟩, hnot⟩
    have h3 : g w₀ - g (D.flow 1 w₀) ≤ g w - g (D.flow 1 w) := hmin hmem
    linarith
  · refine ⟨1, one_pos, ?_⟩
    intro a b T ha hb _ hT w hw hw'
    by_contra hnot
    have h2 : g (D.flow T w) ≤ g w := D.mono T w (zero_le_one.trans hT)
    exact hne ⟨w, ⟨by linarith, by linarith⟩, hnot⟩

/-- The value after n unit steps is below c₁ or has dropped by n d, if every unit step from
the strip {c₁ ≤ g ≤ c₂} drops g by at least d. -/
theorem drop_steps {c₁ c₂ d : ℝ}
    (hdrop : ∀ w, c₁ ≤ g w → g w ≤ c₂ → d ≤ g w - g (D.flow 1 w)) (w : W) (hw : g w ≤ c₂) :
    ∀ n : ℕ, g (D.flow n w) < c₁ ∨ g (D.flow n w) ≤ g w - n * d
  | 0 => by
    right
    rw [Nat.cast_zero, D.zero, zero_mul, sub_zero]
  | n + 1 => by
    have hstep : D.flow ((n + 1 : ℕ) : ℝ) w = D.flow 1 (D.flow n w) := by
      rw [← D.add 1 n w zero_le_one (Nat.cast_nonneg n), Nat.cast_add, Nat.cast_one, add_comm]
    have hmono : g (D.flow n w) ≤ g w := D.mono n w (Nat.cast_nonneg n)
    rw [hstep]
    rcases drop_steps hdrop w hw n with h | h
    · exact Or.inl (lt_of_le_of_lt (D.mono 1 _ zero_le_one) h)
    · by_cases h' : g (D.flow n w) < c₁
      · exact Or.inl (lt_of_le_of_lt (D.mono 1 _ zero_le_one) h')
      · right
        have h1 := hdrop (D.flow n w) (not_lt.mp h') (hmono.trans hw)
        push_cast
        linarith

/-- Descent across a compact strip on which the time-one map decreases g strictly: some time
takes the sublevel of c₂ below c₁. -/
theorem exists_push (hg : Continuous g) {c₁ c₂ : ℝ}
    (hK : IsCompact {w : W | c₁ ≤ g w ∧ g w ≤ c₂})
    (hstrict : ∀ w, c₁ ≤ g w → g w ≤ c₂ → g (D.flow 1 w) < g w) :
    ∃ s₀ : ℝ, 0 ≤ s₀ ∧ ∀ w, g w ≤ c₂ → g (D.flow s₀ w) < c₁ := by
  have hc : ContinuousOn (fun w => g w - g (D.flow 1 w)) {w : W | c₁ ≤ g w ∧ g w ≤ c₂} :=
    (hg.sub (hg.comp (flow_continuous D 1))).continuousOn
  by_cases hne : ({w : W | c₁ ≤ g w ∧ g w ≤ c₂}).Nonempty
  · obtain ⟨w₀, hw₀, hmin⟩ := hK.exists_isMinOn hne hc
    have hd : 0 < g w₀ - g (D.flow 1 w₀) := sub_pos.mpr (hstrict w₀ hw₀.1 hw₀.2)
    obtain ⟨n, hn⟩ := exists_nat_gt ((c₂ - c₁) / (g w₀ - g (D.flow 1 w₀)))
    refine ⟨n, Nat.cast_nonneg n, fun w hw => ?_⟩
    have hn' : c₂ - c₁ < n * (g w₀ - g (D.flow 1 w₀)) := (div_lt_iff₀ hd).mp hn
    rcases drop_steps D (fun w h1 h2 => hmin (a := w) ⟨h1, h2⟩) w hw n with h | h
    · exact h
    · linarith
  · refine ⟨0, le_rfl, fun w hw => ?_⟩
    rw [D.zero]
    by_contra h
    exact hne ⟨w, not_lt.mp h, hw⟩

/-- If the points below b not taken below a in time T lie in the union of two disjoint open
sets, a point of the first one stays in it as long as it is not taken below a. -/
theorem trap_piece {a b T : ℝ} (hT : 0 ≤ T) {𝒲 𝒱 : Set W} (h𝒲 : IsOpen 𝒲) (h𝒱 : IsOpen 𝒱)
    (hdis : Disjoint 𝒲 𝒱)
    (htrap : ∀ w, g w < b → a ≤ g (D.flow T w) → w ∈ 𝒲 ∪ 𝒱)
    (w : W) (hw : w ∈ 𝒲) (hb : g w < b) (s : ℝ) (hs : 0 ≤ s)
    (ha : a ≤ g (D.flow T (D.flow s w))) : D.flow s w ∈ 𝒲 := by
  have hcont : Continuous fun r : ℝ => D.flow r w :=
    D.cont.comp (continuous_id.prodMk continuous_const)
  have hmem : ∀ r, r ∈ Icc (0 : ℝ) s → D.flow r w ∈ 𝒲 ∪ 𝒱 := by
    intro r hr
    refine htrap _ (lt_of_le_of_lt (D.mono r w hr.1) hb) (ha.trans ?_)
    have h : D.flow T (D.flow s w) = D.flow (s - r) (D.flow T (D.flow r w)) := by
      rw [flow_comm D hr.1 hT, ← D.add (s - r) r _ (sub_nonneg.mpr hr.2) hr.1, sub_add_cancel,
        flow_comm D hs hT]
    rw [h]
    exact D.mono _ _ (sub_nonneg.mpr hr.2)
  have hpre : IsPreconnected (Icc (0 : ℝ) s) := isPreconnected_Icc
  have hsub : Icc (0 : ℝ) s ⊆ (fun r : ℝ => D.flow r w) ⁻¹' 𝒲 ∪
      (fun r : ℝ => D.flow r w) ⁻¹' 𝒱 := fun r hr => hmem r hr
  have h0 : (Icc (0 : ℝ) s ∩ (fun r : ℝ => D.flow r w) ⁻¹' 𝒲).Nonempty :=
    ⟨0, ⟨le_rfl, hs⟩, by
      change D.flow 0 w ∈ 𝒲
      rw [D.zero]
      exact hw⟩
  by_contra hnot
  have hs𝒱 : D.flow s w ∈ 𝒱 := (hmem s ⟨hs, le_rfl⟩).resolve_left hnot
  obtain ⟨r, -, hr𝒲, hr𝒱⟩ := hpre _ _ (h𝒲.preimage hcont) (h𝒱.preimage hcont) hsub h0
    ⟨s, ⟨hs, le_rfl⟩, hs𝒱⟩
  exact (Set.disjoint_left.mp hdis) hr𝒲 hr𝒱

end

end Finsler.LensTrap
