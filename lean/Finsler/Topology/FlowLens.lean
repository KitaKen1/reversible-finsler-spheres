module

public import Finsler.Topology.PairTriple

/-! Lens pairs of a descending semiflow. A descent for a function g on a space is a continuous
semiflow along which g does not increase. For cuts a ≤ b and a time T ≥ 0 the lens set Y
consists of the points below b which the flow takes below a in time T. The time-T map deforms
the sublevel of b into itself, takes Y into the sublevel of a and keeps both, because the flow
maps commute; hence the cohomology of the sublevel of b relative to Y is that of the sublevel
of b relative to the sublevel of a. For a' < a the points which the flow does not take to
energy at most a' in time T form an open set N, and the pair (N ∩ {g < b}, N ∩ Y) is an
excision of ({g < b}, Y). No compactness and no strictness of the descent is used. -/

@[expose] public section

namespace Finsler.FlowLens

open CategoryTheory Set Topology Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop
open Finsler.BorelCrossing Finsler.BorelDeformation Finsler.PairTriple

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- A continuous semiflow along which a function does not increase. -/
structure Descent (W : TopCat.{0}) (g : W → ℝ) where
  flow : ℝ → W → W
  cont : Continuous fun p : ℝ × W => flow p.1 p.2
  zero : ∀ w, flow 0 w = w
  add : ∀ s t w, 0 ≤ s → 0 ≤ t → flow (s + t) w = flow s (flow t w)
  mono : ∀ t w, 0 ≤ t → g (flow t w) ≤ g w

variable {W : TopCat.{0}} {g : W → ℝ} (D : Descent W g)

theorem flow_continuous (t : ℝ) : Continuous (D.flow t) :=
  D.cont.comp (continuous_const.prodMk continuous_id)

/-- The flow maps of two nonnegative times commute. -/
theorem flow_comm {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (w : W) :
    D.flow t (D.flow s w) = D.flow s (D.flow t w) := by
  rw [← D.add t s w ht hs, ← D.add s t w hs ht, add_comm]

/-- The value after time T does not increase along the flow. -/
theorem mono_after {s T : ℝ} (hs : 0 ≤ s) (hT : 0 ≤ T) (w : W) :
    g (D.flow T (D.flow s w)) ≤ g (D.flow T w) := by
  rw [flow_comm D hs hT]
  exact D.mono s _ hs

/-- The strict sublevel of a function. -/
def sub (g : W → ℝ) (c : ℝ) : Set W := {w | g w < c}

/-- The lens set: the points below b which the flow takes below a in time T. -/
def lensY (a b T : ℝ) : Set W := {w | g w < b ∧ g (D.flow T w) < a}

theorem lensY_subset (a b T : ℝ) : lensY D a b T ⊆ sub g b := fun _ hw => hw.1

theorem sub_subset_lensY {a b T : ℝ} (hab : a ≤ b) (hT : 0 ≤ T) : sub g a ⊆ lensY D a b T :=
  fun w hw => ⟨lt_of_lt_of_le hw hab, lt_of_le_of_lt (D.mono T w hT) hw⟩

theorem lensY_isOpen (hg : Continuous g) (a b T : ℝ) : IsOpen (lensY D a b T) :=
  (isOpen_lt hg continuous_const).inter
    (isOpen_lt (hg.comp (flow_continuous D T)) continuous_const)

/-- The flow up to a time s₀ as a homotopy of a set which the flow keeps. -/
def flowHomotopy {u : Set W} (s₀ : ℝ) (hs₀ : 0 ≤ s₀)
    (hu : ∀ s w, 0 ≤ s → w ∈ u → D.flow s w ∈ u) :
    (ContinuousMap.id u).Homotopy
      ⟨fun w => ⟨D.flow s₀ w, hu s₀ w hs₀ w.2⟩,
        ((flow_continuous D s₀).comp continuous_subtype_val).subtype_mk _⟩ where
  toFun p := ⟨D.flow ((p.1 : ℝ) * s₀) p.2, hu _ _ (mul_nonneg p.1.2.1 hs₀) p.2.2⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact D.cont.comp (((continuous_subtype_val.comp continuous_fst).mul continuous_const).prodMk
      (continuous_subtype_val.comp continuous_snd))
  map_zero_left w := by
    apply Subtype.ext
    change D.flow (((0 : unitInterval) : ℝ) * s₀) (w : W) = (w : W)
    rw [show ((0 : unitInterval) : ℝ) = 0 from rfl, zero_mul, D.zero]
  map_one_left w := by
    apply Subtype.ext
    change D.flow (((1 : unitInterval) : ℝ) * s₀) (w : W) = D.flow s₀ (w : W)
    rw [show ((1 : unitInterval) : ℝ) = 1 from rfl, one_mul]

theorem flowHomotopy_apply {u : Set W} (s₀ : ℝ) (hs₀ : 0 ≤ s₀)
    (hu : ∀ s w, 0 ≤ s → w ∈ u → D.flow s w ∈ u) (τ : unitInterval) (w : u) :
    (flowHomotopy D s₀ hs₀ hu (τ, w) : W) = D.flow ((τ : ℝ) * s₀) w := rfl

theorem sub_flow (c : ℝ) (s : ℝ) (w : W) (hs : 0 ≤ s) (hw : w ∈ sub g c) :
    D.flow s w ∈ sub g c :=
  lt_of_le_of_lt (D.mono s w hs) hw

theorem lensY_flow {a b T : ℝ} (hT : 0 ≤ T) (s : ℝ) (w : W) (hs : 0 ≤ s)
    (hw : w ∈ lensY D a b T) : D.flow s w ∈ lensY D a b T :=
  ⟨lt_of_le_of_lt (D.mono s w hs) hw.1, lt_of_le_of_lt (mono_after D hs hT w) hw.2⟩

/-- The time-T map deforms the sublevel of b, taking the lens set into the sublevel of a. -/
def lensDeformation {a b T : ℝ} (hT : 0 ≤ T) :
    PairDeformation (sub g a) (sub g b) (lensY D a b T) (sub g b) where
  r := ⟨fun w => ⟨D.flow T w, sub_flow D b T w hT w.2⟩,
    ((flow_continuous D T).comp continuous_subtype_val).subtype_mk _⟩
  H := flowHomotopy D T hT (sub_flow D b)
  r_mem w := sub_flow D b T w hT w.2
  r_sub _ hw := hw.2
  keep_sub' τ w hw := lensY_flow D hT _ w (mul_nonneg τ.2.1 hT) hw
  keep τ w hw := sub_flow D b _ w (mul_nonneg τ.2.1 hT) hw
  keep_sub τ w hw := sub_flow D a _ w (mul_nonneg τ.2.1 hT) hw

/-- The cohomology of the sublevel of b relative to the lens set is the cohomology of the
sublevel of b relative to the sublevel of a. -/
theorem lens_bijective {a b T : ℝ} (hab : a ≤ b) (hT : 0 ≤ T) (n : ℕ) :
    Function.Bijective (Hmap (trivHom (relPair (sub_subset_lensY D hab hT)
      (lensY_subset D a b T))) n) :=
  PairTriple.bijective_Hmap _ (fun k => bijective_nativePull_relPair
    (sub_subset_lensY D hab hT) (lensY_subset D a b T) (lensDeformation D hT) k) n

/-- The points which the flow does not take to energy at most a' in time T. -/
def lensN (a' T : ℝ) : Set W := {w | a' < g (D.flow T w)}

theorem lensN_isOpen (hg : Continuous g) (a' T : ℝ) : IsOpen (lensN D a' T) :=
  isOpen_lt continuous_const (hg.comp (flow_continuous D T))

/-- For a' < a the part of the lens pair in N is an excision of it. -/
theorem lensN_bijective (hg : Continuous g) {a' a b T : ℝ} (ha : a' < a) (n : ℕ) :
    Function.Bijective (Hmap (trivHom (inclPair
      (inter_subset_inter_right (lensN D a' T) (lensY_subset D a b T))
      (lensY_subset D a b T) inter_subset_right inter_subset_right)) n) :=
  PairTriple.bijective_Hmap _ (fun k => Finsler.BorelLens.bijective_nativePull_excision
    (lensN D a' T) (lensY_subset D a b T) (lensY_isOpen D hg a b T) (lensN_isOpen D hg a' T)
    (fun w hw => by
      by_cases h : g (D.flow T w) < a
      · exact Or.inl ⟨hw, h⟩
      · exact Or.inr (lt_of_lt_of_le ha (not_lt.mp h))) k) n

end

end Finsler.FlowLens
