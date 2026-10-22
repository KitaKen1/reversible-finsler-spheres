module

public import Finsler.Topology.FlowLens

/-! The lens pair of a function with a split quadratic part. A cone structure on a space W
consists of scalings sc l m (of a negative and a positive part), continuous norms nn and np of
the two parts, homogeneous of degree one, and a function base invariant under the scalings; a
point with nn = 0 is fixed by sc 0 1. Its energy is base − nn² + np². A descent for the energy
is split if the flow commutes with the scalings, does not decrease nn and does not increase np
and base. Let 𝒲 be an open set kept by the scalings, a, b cuts, T ≥ 0 a time such that points of
𝒲 below b which are not taken below a in time T stay in 𝒲 as long as they are not taken below a
(trapping), and s₀ ≥ 0 a time after which such points with np = 0 have base below b. Then the
cohomology of the lens pair in 𝒲, ({energy < b} ∩ 𝒲, Y ∩ 𝒲), is the cohomology of the pair

  T_b = {np = 0, base < b} ∩ 𝒲   relative to   {nn ≠ 0 or base ∘ flow_T < a}.

The steps: shrinking the positive part deforms the pair into the part with np = 0; there the
pair is an excision of the pair with the whole lens set of the part np = 0, which the flow
keeps; flowing for the time s₀ deforms it into the union of T_b and that lens set; excision
gives T_b relative to its points taken below a in time T; and the scalings of the negative
part by 1 + τ ρ / (nn ∘ flow_T), ρ² = max(base ∘ flow_T − a, 0), deform the points with nn ≠ 0
or base ∘ flow_T < a into those taken below a. The last pair is the pair of the negative part
over the lens pair of the base, relative to the nonzero vectors. -/

@[expose] public section

namespace Finsler.ConeLens

open CategoryTheory Set Topology Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop
open Finsler.BorelCrossing Finsler.BorelDeformation Finsler.PairTriple Finsler.FlowLens

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- A cone structure: scalings of a negative and a positive part, their norms and a base
function. -/
structure Cone (W : TopCat.{0}) where
  sc : ℝ → ℝ → W → W
  cont : Continuous fun p : (ℝ × ℝ) × W => sc p.1.1 p.1.2 p.2
  one : ∀ w, sc 1 1 w = w
  nn : W → ℝ
  np : W → ℝ
  base : W → ℝ
  nn_cont : Continuous nn
  np_cont : Continuous np
  base_cont : Continuous base
  nn_nonneg : ∀ w, 0 ≤ nn w
  np_nonneg : ∀ w, 0 ≤ np w
  nn_sc : ∀ l m w, 0 ≤ l → 0 ≤ m → nn (sc l m w) = l * nn w
  np_sc : ∀ l m w, 0 ≤ l → 0 ≤ m → np (sc l m w) = m * np w
  base_sc : ∀ l m w, 0 ≤ l → 0 ≤ m → base (sc l m w) = base w
  nn_zero : ∀ w, nn w = 0 → sc 0 1 w = w

variable {W : TopCat.{0}} (C : Cone W)

/-- The energy of a cone structure. -/
def Cone.energy (w : W) : ℝ := C.base w - C.nn w ^ 2 + C.np w ^ 2

theorem energy_continuous : Continuous C.energy :=
  (C.base_cont.sub (C.nn_cont.pow 2)).add (C.np_cont.pow 2)

theorem energy_sc (l m : ℝ) (w : W) (hl : 0 ≤ l) (hm : 0 ≤ m) :
    C.energy (C.sc l m w) = C.base w - (l * C.nn w) ^ 2 + (m * C.np w) ^ 2 := by
  rw [Cone.energy, C.base_sc l m w hl hm, C.nn_sc l m w hl hm, C.np_sc l m w hl hm]

/-- Shrinking the positive part does not increase the energy. -/
theorem energy_shrink {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (w : W) :
    C.energy (C.sc 1 s w) ≤ C.energy w := by
  rw [energy_sc C 1 s w zero_le_one hs0, Cone.energy, one_mul]
  have h := pow_le_pow_left₀ (mul_nonneg hs0 (C.np_nonneg w))
    (mul_le_of_le_one_left (C.np_nonneg w) hs1) 2
  linarith

/-- Stretching the negative part does not increase the energy. -/
theorem energy_stretch {l : ℝ} (hl : 1 ≤ l) (w : W) :
    C.energy (C.sc l 1 w) ≤ C.energy w := by
  rw [energy_sc C l 1 w (zero_le_one.trans hl) zero_le_one, Cone.energy, one_mul]
  have h := pow_le_pow_left₀ (C.nn_nonneg w) (le_mul_of_one_le_left (C.nn_nonneg w) hl) 2
  linarith

/-- With vanishing positive part the energy is at most the base. -/
theorem energy_le_base {w : W} (hw : C.np w = 0) : C.energy w ≤ C.base w := by
  rw [Cone.energy, hw]
  nlinarith [sq_nonneg (C.nn w)]

/-- The base is at most the energy plus the square of the negative norm. -/
theorem base_le (w : W) : C.base w ≤ C.energy w + C.nn w ^ 2 := by
  rw [Cone.energy]
  nlinarith [sq_nonneg (C.np w)]

/-- A descent for the energy which is compatible with the cone structure. -/
structure Split (D : Descent W C.energy) : Prop where
  comm : ∀ t l m w, 0 ≤ t → 0 ≤ l → 0 ≤ m → D.flow t (C.sc l m w) = C.sc l m (D.flow t w)
  nn_flow : ∀ t w, 0 ≤ t → C.nn w ≤ C.nn (D.flow t w)
  np_flow : ∀ t w, 0 ≤ t → C.np (D.flow t w) ≤ C.np w
  base_flow : ∀ t w, 0 ≤ t → C.base (D.flow t w) ≤ C.base w

variable {C} {D : Descent W C.energy} (hS : Split C D)

include hS in
theorem np_flow_eq_zero {t : ℝ} (ht : 0 ≤ t) {w : W} (hw : C.np w = 0) :
    C.np (D.flow t w) = 0 :=
  le_antisymm ((hS.np_flow t w ht).trans hw.le) (C.np_nonneg _)

include hS in
/-- A point with vanishing negative norm keeps it along the flow. -/
theorem nn_flow_eq_zero {t : ℝ} (ht : 0 ≤ t) {w : W} (hw : C.nn w = 0) :
    C.nn (D.flow t w) = 0 := by
  have h := congrArg C.nn (hS.comm t 0 1 w ht le_rfl zero_le_one)
  rw [C.nn_zero w hw, C.nn_sc 0 1 _ le_rfl zero_le_one, zero_mul] at h
  exact h

variable (C D) (𝒲 : Set W) (a b T : ℝ)

/-- The part of the sublevel of b in 𝒲. -/
def setU : Set W := {w | C.energy w < b ∧ w ∈ 𝒲}

/-- The part of the lens set in 𝒲. -/
def setY : Set W := {w | C.energy w < b ∧ C.energy (D.flow T w) < a ∧ w ∈ 𝒲}

/-- The part of the sublevel in 𝒲 with vanishing positive part. -/
def setU0 : Set W := {w | C.np w = 0 ∧ C.energy w < b ∧ w ∈ 𝒲}

/-- The part of the lens set in 𝒲 with vanishing positive part. -/
def setY0 : Set W :=
  {w | C.np w = 0 ∧ C.energy w < b ∧ C.energy (D.flow T w) < a ∧ w ∈ 𝒲}

/-- The lens set of the part with vanishing positive part. -/
def setYa : Set W := {w | C.np w = 0 ∧ C.energy w < b ∧ C.energy (D.flow T w) < a}

/-- The points of 𝒲 with vanishing positive part and base below b. -/
def setTb : Set W := {w | C.np w = 0 ∧ C.base w < b ∧ w ∈ 𝒲}

/-- The points of T_b taken below a in time T. -/
def setS : Set W :=
  {w | C.np w = 0 ∧ C.base w < b ∧ w ∈ 𝒲 ∧ C.energy (D.flow T w) < a}

/-- The points of T_b with nonzero negative part or base taken below a in time T. -/
def setSx : Set W :=
  {w | C.np w = 0 ∧ C.base w < b ∧ w ∈ 𝒲 ∧ (C.nn w ≠ 0 ∨ C.base (D.flow T w) < a)}

theorem setY_sub_setU : setY C D 𝒲 a b T ⊆ setU C 𝒲 b := fun _ hw => ⟨hw.1, hw.2.2⟩

theorem setY0_sub_setU0 : setY0 C D 𝒲 a b T ⊆ setU0 C 𝒲 b :=
  fun _ hw => ⟨hw.1, hw.2.1, hw.2.2.2⟩

theorem setY0_sub_setY : setY0 C D 𝒲 a b T ⊆ setY C D 𝒲 a b T := fun _ hw => hw.2

theorem setU0_sub_setU : setU0 C 𝒲 b ⊆ setU C 𝒲 b := fun _ hw => hw.2

theorem setY0_sub_setYa : setY0 C D 𝒲 a b T ⊆ setYa C D a b T :=
  fun _ hw => ⟨hw.1, hw.2.1, hw.2.2.1⟩

theorem setTb_sub_setU0 : setTb C 𝒲 b ⊆ setU0 C 𝒲 b :=
  fun _ hw => ⟨hw.1, lt_of_le_of_lt (energy_le_base C hw.1) hw.2.1, hw.2.2⟩

theorem setS_sub_setTb : setS C D 𝒲 a b T ⊆ setTb C 𝒲 b := fun _ hw => ⟨hw.1, hw.2.1, hw.2.2.1⟩

theorem setS_sub_setYa : setS C D 𝒲 a b T ⊆ setYa C D a b T :=
  fun _ hw => ⟨hw.1, lt_of_le_of_lt (energy_le_base C hw.1) hw.2.1, hw.2.2.2⟩

theorem setSx_sub_setTb : setSx C D 𝒲 a b T ⊆ setTb C 𝒲 b :=
  fun _ hw => ⟨hw.1, hw.2.1, hw.2.2.1⟩

variable {C D 𝒲 a b T}

include hS in
theorem setS_sub_setSx (hT : 0 ≤ T) : setS C D 𝒲 a b T ⊆ setSx C D 𝒲 a b T := by
  intro w hw
  refine ⟨hw.1, hw.2.1, hw.2.2.1, ?_⟩
  by_cases hnn : C.nn w = 0
  · right
    have h := base_le C (D.flow T w)
    rw [nn_flow_eq_zero hS hT hnn] at h
    have h2 := hw.2.2.2
    linarith
  · exact Or.inl hnn

section Shrink

variable (hsat : ∀ l m w, 0 ≤ l → 0 ≤ m → w ∈ 𝒲 → C.sc l m w ∈ 𝒲)

include hsat in
theorem shrink_mem_setU {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {w : W} (hw : w ∈ setU C 𝒲 b) :
    C.sc 1 s w ∈ setU C 𝒲 b :=
  ⟨lt_of_le_of_lt (energy_shrink C hs0 hs1 w) hw.1, hsat 1 s w zero_le_one hs0 hw.2⟩

include hS hsat in
theorem shrink_mem_setY (hT : 0 ≤ T) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {w : W}
    (hw : w ∈ setY C D 𝒲 a b T) : C.sc 1 s w ∈ setY C D 𝒲 a b T := by
  refine ⟨lt_of_le_of_lt (energy_shrink C hs0 hs1 w) hw.1, ?_, hsat 1 s w zero_le_one hs0 hw.2.2⟩
  rw [hS.comm T 1 s w hT zero_le_one hs0]
  exact lt_of_le_of_lt (energy_shrink C hs0 hs1 _) hw.2.1

theorem shrink_np {s : ℝ} (hs0 : 0 ≤ s) {w : W} (hw : C.np w = 0) : C.np (C.sc 1 s w) = 0 := by
  rw [C.np_sc 1 s w zero_le_one hs0, hw, mul_zero]

/-- The map removing the positive part. -/
def shrinkEnd : C(setU C 𝒲 b, setU C 𝒲 b) :=
  ⟨fun w => ⟨C.sc 1 0 w, shrink_mem_setU hsat le_rfl zero_le_one w.2⟩,
    (C.cont.comp ((continuous_const (y := ((1 : ℝ), (0 : ℝ)))).prodMk
      continuous_subtype_val)).subtype_mk _⟩

/-- The homotopy shrinking the positive part. -/
def shrinkHomotopy : (ContinuousMap.id (setU C 𝒲 b)).Homotopy (shrinkEnd hsat) where
  toFun p := ⟨C.sc 1 (1 - (p.1 : ℝ)) p.2,
    shrink_mem_setU hsat (sub_nonneg.mpr p.1.2.2) (sub_le_self 1 p.1.2.1) p.2.2⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact C.cont.comp ((continuous_const.prodMk
      (continuous_const.sub (continuous_subtype_val.comp continuous_fst))).prodMk
      (continuous_subtype_val.comp continuous_snd))
  map_zero_left w := by
    apply Subtype.ext
    change C.sc 1 (1 - ((0 : unitInterval) : ℝ)) (w : W) = (w : W)
    rw [show ((0 : unitInterval) : ℝ) = 0 from rfl, sub_zero, C.one]
  map_one_left w := by
    apply Subtype.ext
    change C.sc 1 (1 - ((1 : unitInterval) : ℝ)) (w : W) = C.sc 1 0 (w : W)
    rw [show ((1 : unitInterval) : ℝ) = 1 from rfl, sub_self]

/-- Shrinking the positive part deforms the lens pair in 𝒲 into its part with vanishing
positive part. -/
def shrinkDeformation (hT : 0 ≤ T) :
    PairDeformation (setY0 C D 𝒲 a b T) (setU0 C 𝒲 b) (setY C D 𝒲 a b T) (setU C 𝒲 b) where
  r := shrinkEnd hsat
  H := shrinkHomotopy hsat
  r_mem w := ⟨(C.np_sc 1 0 (w : W) zero_le_one le_rfl).trans (zero_mul _),
    (shrink_mem_setU hsat le_rfl zero_le_one w.2).1,
    (shrink_mem_setU hsat le_rfl zero_le_one w.2).2⟩
  r_sub w hw := ⟨(C.np_sc 1 0 (w : W) zero_le_one le_rfl).trans (zero_mul _),
    shrink_mem_setY hS hsat hT le_rfl zero_le_one hw⟩
  keep_sub' τ _ hw :=
    shrink_mem_setY hS hsat hT (sub_nonneg.mpr τ.2.2) (sub_le_self 1 τ.2.1) hw
  keep τ _ hw := ⟨shrink_np (sub_nonneg.mpr τ.2.2) hw.1,
    (shrink_mem_setU hsat (sub_nonneg.mpr τ.2.2) (sub_le_self 1 τ.2.1)
      (setU0_sub_setU C 𝒲 b hw)).1,
    (shrink_mem_setU hsat (sub_nonneg.mpr τ.2.2) (sub_le_self 1 τ.2.1)
      (setU0_sub_setU C 𝒲 b hw)).2⟩
  keep_sub τ _ hw := ⟨shrink_np (sub_nonneg.mpr τ.2.2) hw.1,
    shrink_mem_setY hS hsat hT (sub_nonneg.mpr τ.2.2) (sub_le_self 1 τ.2.1)
      (setY0_sub_setY C D 𝒲 a b T hw)⟩

include hS hsat in
/-- The lens pair in 𝒲 has the cohomology of its part with vanishing positive part. -/
theorem shrink_bijective (hT : 0 ≤ T) (n : ℕ) :
    Function.Bijective (Hmap (trivHom (inclPair (setY0_sub_setU0 C D 𝒲 a b T)
      (setY_sub_setU C D 𝒲 a b T) (setY0_sub_setY C D 𝒲 a b T) (setU0_sub_setU C 𝒲 b))) n) :=
  PairTriple.bijective_Hmap _ (fun k => bijective_nativePull_inclPair _ _ _ _
    (shrinkDeformation hS hsat hT) k) n

end Shrink

section Flow

include hS in
theorem setYa_flow (hT : 0 ≤ T) (s : ℝ) (w : W) (hs : 0 ≤ s) (hw : w ∈ setYa C D a b T) :
    D.flow s w ∈ setYa C D a b T :=
  ⟨np_flow_eq_zero hS hs hw.1, lt_of_le_of_lt (D.mono s w hs) hw.2.1,
    lt_of_le_of_lt (mono_after D hs hT w) hw.2.2⟩

variable (htrap : ∀ w, w ∈ 𝒲 → C.energy w < b → a ≤ C.energy (D.flow T w) → ∀ s, 0 ≤ s →
  a ≤ C.energy (D.flow T (D.flow s w)) → D.flow s w ∈ 𝒲)

include hS htrap in
/-- The flow keeps the union of the part of the sublevel in 𝒲 and the lens set, on the part
with vanishing positive part. -/
theorem union_flow (hT : 0 ≤ T) (s : ℝ) (w : W) (hs : 0 ≤ s)
    (hw : w ∈ setU0 C 𝒲 b ∪ setYa C D a b T) : D.flow s w ∈ setU0 C 𝒲 b ∪ setYa C D a b T := by
  rcases hw with hw | hw
  · by_cases h : C.energy (D.flow T (D.flow s w)) < a
    · exact Or.inr ⟨np_flow_eq_zero hS hs hw.1, lt_of_le_of_lt (D.mono s w hs) hw.2.1, h⟩
    · have h' := not_lt.mp h
      exact Or.inl ⟨np_flow_eq_zero hS hs hw.1, lt_of_le_of_lt (D.mono s w hs) hw.2.1,
        htrap w hw.2.2 hw.2.1 (h'.trans (mono_after D hs hT w)) s hs h'⟩
  · exact Or.inr (setYa_flow hS hT s w hs hw)

include hS htrap in
theorem tb_union_flow (hT : 0 ≤ T) (s : ℝ) (w : W) (hs : 0 ≤ s)
    (hw : w ∈ setTb C 𝒲 b ∪ setYa C D a b T) : D.flow s w ∈ setTb C 𝒲 b ∪ setYa C D a b T := by
  rcases hw with hw | hw
  · have hE : C.energy w < b := lt_of_le_of_lt (energy_le_base C hw.1) hw.2.1
    by_cases h : C.energy (D.flow T (D.flow s w)) < a
    · exact Or.inr ⟨np_flow_eq_zero hS hs hw.1, lt_of_le_of_lt (D.mono s w hs) hE, h⟩
    · have h' := not_lt.mp h
      exact Or.inl ⟨np_flow_eq_zero hS hs hw.1, lt_of_le_of_lt (hS.base_flow s w hs) hw.2.1,
        htrap w hw.2.2 hE (h'.trans (mono_after D hs hT w)) s hs h'⟩
  · exact Or.inr (setYa_flow hS hT s w hs hw)

variable {s₀ : ℝ} (hpush : ∀ w, w ∈ 𝒲 → C.np w = 0 → C.energy w < b →
  a ≤ C.energy (D.flow T w) → C.base (D.flow s₀ w) < b)

include hS htrap hpush in
theorem push_mem (hT : 0 ≤ T) (hs₀ : 0 ≤ s₀) (w : W)
    (hw : w ∈ setU0 C 𝒲 b ∪ setYa C D a b T) :
    D.flow s₀ w ∈ setTb C 𝒲 b ∪ setYa C D a b T := by
  rcases hw with hw | hw
  · by_cases h : C.energy (D.flow T (D.flow s₀ w)) < a
    · exact Or.inr ⟨np_flow_eq_zero hS hs₀ hw.1, lt_of_le_of_lt (D.mono s₀ w hs₀) hw.2.1, h⟩
    · have h' := not_lt.mp h
      have h'' := h'.trans (mono_after D hs₀ hT w)
      exact Or.inl ⟨np_flow_eq_zero hS hs₀ hw.1, hpush w hw.2.2 hw.1 hw.2.1 h'',
        htrap w hw.2.2 hw.2.1 h'' s₀ hs₀ h'⟩
  · exact Or.inr (setYa_flow hS hT s₀ w hs₀ hw)

include hS htrap hpush in
/-- Flowing for the time s₀ deforms the union of the part of the sublevel and the lens set
into the union of T_b and the lens set. -/
def pushDeformation (hT : 0 ≤ T) (hs₀ : 0 ≤ s₀) :
    PairDeformation (setYa C D a b T) (setTb C 𝒲 b ∪ setYa C D a b T) (setYa C D a b T)
      (setU0 C 𝒲 b ∪ setYa C D a b T) where
  r := _
  H := flowHomotopy D s₀ hs₀ (union_flow hS htrap hT)
  r_mem w := push_mem hS htrap hpush hT hs₀ w w.2
  r_sub w hw := setYa_flow hS hT s₀ w hs₀ hw
  keep_sub' τ w hw := setYa_flow hS hT _ w (mul_nonneg τ.2.1 hs₀) hw
  keep τ w hw := tb_union_flow hS htrap hT _ w (mul_nonneg τ.2.1 hs₀) hw
  keep_sub τ w hw := setYa_flow hS hT _ w (mul_nonneg τ.2.1 hs₀) hw

include hS htrap hpush in
theorem push_bijective (hT : 0 ≤ T) (hs₀ : 0 ≤ s₀) (n : ℕ) :
    Function.Bijective (Hmap (trivHom (inclPair
      (subset_union_right : setYa C D a b T ⊆ setTb C 𝒲 b ∪ setYa C D a b T)
      (subset_union_right : setYa C D a b T ⊆ setU0 C 𝒲 b ∪ setYa C D a b T) subset_rfl
      (union_subset_union_left _ (setTb_sub_setU0 C 𝒲 b)))) n) :=
  PairTriple.bijective_Hmap _ (fun k => bijective_nativePull_inclPair _ _ _ _
    (pushDeformation hS htrap hpush hT hs₀) k) n

end Flow

section Excision

variable (h𝒲 : IsOpen 𝒲)

include h𝒲 in
/-- The part of the lens pair in 𝒲 with vanishing positive part is an excision of the union
with the whole lens set of that part. -/
theorem exc_bijective (n : ℕ) :
    Function.Bijective (Hmap (trivHom (inclPair (setY0_sub_setU0 C D 𝒲 a b T)
      (subset_union_right : setYa C D a b T ⊆ setU0 C 𝒲 b ∪ setYa C D a b T)
      (setY0_sub_setYa C D 𝒲 a b T) subset_union_left)) n) := by
  refine bijective_Hmap_excision _ _ _ _ ?_ (lensY D a b T)
    {w | C.energy w < b ∧ w ∈ 𝒲} (lensY_isOpen D (energy_continuous C) a b T)
    ((isOpen_lt (energy_continuous C) continuous_const).inter h𝒲) ?_ ?_ ?_ n
  · exact fun w hw hw' => ⟨hw.1, hw.2.1, hw'.2.2, hw.2.2⟩
  · rintro w (hw | hw)
    · exact Or.inr ⟨hw.2.1, hw.2.2⟩
    · exact Or.inl ⟨hw.2.1, hw.2.2⟩
  · rintro w ⟨hw, hw' | hw'⟩
    · exact ⟨hw'.1, hw.1, hw.2⟩
    · exact hw'
  · rintro w ⟨hw, hw' | hw'⟩
    · exact hw'
    · exact ⟨hw'.1, hw.1, hw.2⟩

include h𝒲 in
/-- T_b relative to its points taken below a is an excision of the union of T_b and the lens
set relative to the lens set. -/
theorem exc_tb_bijective (n : ℕ) :
    Function.Bijective (Hmap (trivHom (inclPair (setS_sub_setTb C D 𝒲 a b T)
      (subset_union_right : setYa C D a b T ⊆ setTb C 𝒲 b ∪ setYa C D a b T)
      (setS_sub_setYa C D 𝒲 a b T) subset_union_left)) n) := by
  refine bijective_Hmap_excision _ _ _ _ ?_ (lensY D a b T)
    {w | C.base w < b ∧ w ∈ 𝒲} (lensY_isOpen D (energy_continuous C) a b T)
    ((isOpen_lt C.base_cont continuous_const).inter h𝒲) ?_ ?_ ?_ n
  · exact fun w hw hw' => ⟨hw.1, hw.2.1, hw.2.2, hw'.2.2⟩
  · rintro w (hw | hw)
    · exact Or.inr ⟨hw.2.1, hw.2.2⟩
    · exact Or.inl ⟨hw.2.1, hw.2.2⟩
  · rintro w ⟨hw, hw' | hw'⟩
    · exact ⟨hw'.1, hw.1, hw.2⟩
    · exact hw'
  · rintro w ⟨hw, hw' | hw'⟩
    · exact hw'
    · exact ⟨hw'.1, hw.1, hw.2⟩

end Excision

section Radial

variable (C D a T)

/-- The radius below which a point with base above a after time T is not taken below a. -/
def rho (w : W) : ℝ := Real.sqrt (max (C.base (D.flow T w) - a) 0)

/-- The relative amount of stretching. -/
def quot (w : W) : ℝ := rho C D a T w / C.nn (D.flow T w)

theorem rho_continuous : Continuous (rho C D a T) :=
  Real.continuous_sqrt.comp
    (((C.base_cont.comp (flow_continuous D T)).sub continuous_const).max continuous_const)

theorem rho_nonneg (w : W) : 0 ≤ rho C D a T w := Real.sqrt_nonneg _

theorem rho_sq (w : W) : C.base (D.flow T w) - a ≤ rho C D a T w ^ 2 := by
  rw [rho, Real.sq_sqrt (le_max_right _ _)]
  exact le_max_left _ _

theorem rho_eq_zero {w : W} (hw : C.base (D.flow T w) < a) : rho C D a T w = 0 := by
  rw [rho, max_eq_right (sub_nonpos.mpr hw.le), Real.sqrt_zero]

theorem quot_nonneg (w : W) : 0 ≤ quot C D a T w :=
  div_nonneg (rho_nonneg C D a T w) (C.nn_nonneg _)

variable {C D a T}

include hS in
/-- The relative amount of stretching is continuous at the points with nonzero negative part
or base taken below a. -/
theorem quot_continuousAt (hT : 0 ≤ T) {w : W} (hw : w ∈ setSx C D 𝒲 a b T) :
    ContinuousAt (quot C D a T) w := by
  by_cases h : C.nn (D.flow T w) = 0
  · have hnn : C.nn w = 0 := le_antisymm ((hS.nn_flow T w hT).trans h.le) (C.nn_nonneg w)
    have hb : C.base (D.flow T w) < a := by
      rcases hw.2.2.2 with h' | h'
      · exact absurd hnn h'
      · exact h'
    have hopen : IsOpen {w' : W | C.base (D.flow T w') < a} :=
      isOpen_lt (C.base_cont.comp (flow_continuous D T)) continuous_const
    have hev : (fun _ : W => (0 : ℝ)) =ᶠ[𝓝 w] quot C D a T := by
      filter_upwards [hopen.mem_nhds hb] with w' hw'
      rw [quot, rho_eq_zero C D a T hw', zero_div]
    exact (continuousAt_const (y := (0 : ℝ))).congr hev
  · exact (rho_continuous C D a T).continuousAt.div
      (C.nn_cont.comp (flow_continuous D T)).continuousAt h

variable (hsat : ∀ l m w, 0 ≤ l → 0 ≤ m → w ∈ 𝒲 → C.sc l m w ∈ 𝒲)

include hS hsat in
theorem stretch_mem_setSx (hT : 0 ≤ T) {l : ℝ} (hl : 1 ≤ l) {w : W}
    (hw : w ∈ setSx C D 𝒲 a b T) : C.sc l 1 w ∈ setSx C D 𝒲 a b T := by
  have hl0 : 0 ≤ l := zero_le_one.trans hl
  refine ⟨by rw [C.np_sc l 1 w hl0 zero_le_one, hw.1, mul_zero],
    by rw [C.base_sc l 1 w hl0 zero_le_one]; exact hw.2.1,
    hsat l 1 w hl0 zero_le_one hw.2.2.1, ?_⟩
  rcases hw.2.2.2 with h | h
  · left
    rw [C.nn_sc l 1 w hl0 zero_le_one]
    exact mul_ne_zero (ne_of_gt (lt_of_lt_of_le one_pos hl)) h
  · right
    rw [hS.comm T l 1 w hT hl0 zero_le_one, C.base_sc l 1 _ hl0 zero_le_one]
    exact h

include hS hsat in
theorem stretch_mem_setS (hT : 0 ≤ T) {l : ℝ} (hl : 1 ≤ l) {w : W}
    (hw : w ∈ setS C D 𝒲 a b T) : C.sc l 1 w ∈ setS C D 𝒲 a b T := by
  have hl0 : 0 ≤ l := zero_le_one.trans hl
  refine ⟨by rw [C.np_sc l 1 w hl0 zero_le_one, hw.1, mul_zero],
    by rw [C.base_sc l 1 w hl0 zero_le_one]; exact hw.2.1,
    hsat l 1 w hl0 zero_le_one hw.2.2.1, ?_⟩
  rw [hS.comm T l 1 w hT hl0 zero_le_one]
  exact lt_of_le_of_lt (energy_stretch C hl _) hw.2.2.2

include hS hsat in
/-- Stretching by the full amount takes a point with nonzero negative part or base taken
below a to a point taken below a. -/
theorem stretch_end (hT : 0 ≤ T) {w : W} (hw : w ∈ setSx C D 𝒲 a b T) :
    C.sc (1 + quot C D a T w) 1 w ∈ setS C D 𝒲 a b T := by
  have hq := quot_nonneg C D a T w
  have hl : (1 : ℝ) ≤ 1 + quot C D a T w := le_add_of_nonneg_right hq
  have hl0 : 0 ≤ 1 + quot C D a T w := zero_le_one.trans hl
  have hx := stretch_mem_setSx hS hsat hT hl hw
  refine ⟨hx.1, hx.2.1, hx.2.2.1, ?_⟩
  rw [hS.comm T _ 1 w hT hl0 zero_le_one, energy_sc C _ 1 _ hl0 zero_le_one,
    np_flow_eq_zero hS hT hw.1, mul_zero]
  by_cases h : C.nn (D.flow T w) = 0
  · have hnn : C.nn w = 0 := le_antisymm ((hS.nn_flow T w hT).trans h.le) (C.nn_nonneg w)
    have hb : C.base (D.flow T w) < a := by
      rcases hw.2.2.2 with h' | h'
      · exact absurd hnn h'
      · exact h'
    rw [h, mul_zero]
    simpa using hb
  · have hpos : 0 < C.nn (D.flow T w) := lt_of_le_of_ne (C.nn_nonneg _) (Ne.symm h)
    have he : (1 + quot C D a T w) * C.nn (D.flow T w) =
        C.nn (D.flow T w) + rho C D a T w := by
      rw [quot]
      field_simp
    rw [he]
    have h1 := rho_sq C D a T w
    have h2 := rho_nonneg C D a T w
    nlinarith

/-- The homotopy stretching the negative part. -/
def stretchHomotopy (hT : 0 ≤ T) : (ContinuousMap.id (setSx C D 𝒲 a b T)).Homotopy
    ⟨fun w => ⟨C.sc (1 + quot C D a T w) 1 w,
        stretch_mem_setSx hS hsat hT (le_add_of_nonneg_right (quot_nonneg C D a T w)) w.2⟩,
      (C.cont.comp (((continuous_const.add (continuous_iff_continuousAt.2 fun w =>
        (quot_continuousAt hS hT w.2).comp continuous_subtype_val.continuousAt)).prodMk
        continuous_const).prodMk continuous_subtype_val)).subtype_mk _⟩ where
  toFun p := ⟨C.sc (1 + (p.1 : ℝ) * quot C D a T p.2) 1 p.2,
    stretch_mem_setSx hS hsat hT (le_add_of_nonneg_right
      (mul_nonneg p.1.2.1 (quot_nonneg C D a T p.2))) p.2.2⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    have hq : Continuous fun w : setSx C D 𝒲 a b T => quot C D a T (w : W) :=
      continuous_iff_continuousAt.2 fun w =>
        (quot_continuousAt hS hT w.2).comp continuous_subtype_val.continuousAt
    exact C.cont.comp (((continuous_const.add ((continuous_subtype_val.comp continuous_fst).mul
      (hq.comp continuous_snd))).prodMk continuous_const).prodMk
      (continuous_subtype_val.comp continuous_snd))
  map_zero_left w := by
    apply Subtype.ext
    change C.sc (1 + ((0 : unitInterval) : ℝ) * quot C D a T w) 1 (w : W) = (w : W)
    rw [show ((0 : unitInterval) : ℝ) = 0 from rfl, zero_mul, add_zero, C.one]
  map_one_left w := by
    apply Subtype.ext
    change C.sc (1 + ((1 : unitInterval) : ℝ) * quot C D a T w) 1 (w : W) =
      C.sc (1 + quot C D a T w) 1 (w : W)
    rw [show ((1 : unitInterval) : ℝ) = 1 from rfl, one_mul]

/-- Stretching the negative part deforms the points with nonzero negative part or base taken
below a into the points taken below a. -/
def stretchDeformation (hT : 0 ≤ T) :
    PairDeformation (setS C D 𝒲 a b T) (setS C D 𝒲 a b T) (setS C D 𝒲 a b T)
      (setSx C D 𝒲 a b T) where
  r := _
  H := stretchHomotopy hS hsat hT
  r_mem w := stretch_end hS hsat hT w.2
  r_sub w _ := stretch_end hS hsat hT w.2
  keep_sub' τ w hw := stretch_mem_setS hS hsat hT
    (le_add_of_nonneg_right (mul_nonneg τ.2.1 (quot_nonneg C D a T w))) hw
  keep τ w hw := stretch_mem_setS hS hsat hT
    (le_add_of_nonneg_right (mul_nonneg τ.2.1 (quot_nonneg C D a T w))) hw
  keep_sub τ w hw := stretch_mem_setS hS hsat hT
    (le_add_of_nonneg_right (mul_nonneg τ.2.1 (quot_nonneg C D a T w))) hw

include hS hsat in
/-- The cohomology of the points with nonzero negative part or base taken below a, relative
to the points taken below a, vanishes. -/
theorem stretch_eq_zero (hT : 0 ≤ T) (n : ℕ)
    (x : H (triv (pairOf (setS_sub_setSx hS hT : setS C D 𝒲 a b T ⊆ setSx C D 𝒲 a b T))) n) :
    x = 0 := by
  have hb := PairTriple.bijective_Hmap _ (fun k => bijective_nativePull_inclPair
    (subset_refl (setS C D 𝒲 a b T)) (setS_sub_setSx hS hT) (subset_refl _)
    (setS_sub_setSx hS hT) (stretchDeformation hS hsat hT) k) n
  apply hb.1
  rw [map_zero]
  exact H_self_eq_zero _ n _

include hS hsat in
/-- T_b relative to the points with nonzero negative part or base taken below a has the
cohomology of T_b relative to the points taken below a. -/
theorem stretch_bijective (hT : 0 ≤ T) (n : ℕ) :
    Function.Bijective (Hmap (trivHom (relPair (setS_sub_setSx hS hT)
      (setSx_sub_setTb C D 𝒲 a b T))) n) :=
  rel_bijective _ _ n (stretch_eq_zero hS hsat hT n) fun m _ => stretch_eq_zero hS hsat hT m

end Radial

/-- The cohomology of the lens pair in 𝒲 of a split descent is the cohomology of T_b relative
to its points with nonzero negative part or base taken below a in time T. -/
def coneEquiv (h𝒲 : IsOpen 𝒲)
    (hsat : ∀ l m w, 0 ≤ l → 0 ≤ m → w ∈ 𝒲 → C.sc l m w ∈ 𝒲)
    (htrap : ∀ w, w ∈ 𝒲 → C.energy w < b → a ≤ C.energy (D.flow T w) → ∀ s, 0 ≤ s →
      a ≤ C.energy (D.flow T (D.flow s w)) → D.flow s w ∈ 𝒲)
    {s₀ : ℝ} (hpush : ∀ w, w ∈ 𝒲 → C.np w = 0 → C.energy w < b →
      a ≤ C.energy (D.flow T w) → C.base (D.flow s₀ w) < b)
    (hT : 0 ≤ T) (hs₀ : 0 ≤ s₀) (n : ℕ) :
    H (triv (pairOf (setY_sub_setU C D 𝒲 a b T))) n ≃ₗ[ZMod 2]
      H (triv (pairOf (setSx_sub_setTb C D 𝒲 a b T))) n :=
  ((((LinearEquiv.ofBijective _ (shrink_bijective hS hsat hT n)).trans
    (LinearEquiv.ofBijective _ (exc_bijective h𝒲 n)).symm).trans
    (LinearEquiv.ofBijective _ (push_bijective hS htrap hpush hT hs₀ n))).trans
    (LinearEquiv.ofBijective _ (exc_tb_bijective h𝒲 n))).trans
    (LinearEquiv.ofBijective _ (stretch_bijective hS hsat hT n)).symm

end

end Finsler.ConeLens
