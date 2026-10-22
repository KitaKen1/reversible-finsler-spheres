module

public import Finsler.Topology.FlowLens

/-! Invariance of lens pairs under a small change of the function. Let g₀ and g₁ be continuous
functions on a space which differ by at most δ, and let a semiflow be a descent for both. Let
𝒲 be an open set, a, b cuts and T, τ ≥ 0 times such that the flow takes the sublevel of b + δ of
g₀ below b − δ and the sublevel of a + δ below a − δ in time τ, and such that the points of 𝒲
below b + δ which are not taken below a − δ in time T (for g₀) stay in 𝒲 as long as they are not
taken below a − δ. Then the lens pairs in 𝒲 of the two functions,

  ({g_i < b} ∩ 𝒲, {g_i < b, g_i ∘ flow_T < a} ∩ 𝒲),

have isomorphic cohomology. For each function the union of the part of the sublevel in 𝒲 and
the lens set is kept by the flow, and the lens pair in 𝒲 is an excision of this union relative
to the lens set; the time-τ map takes the union and the lens set of each function into those
of the other, and the two composites are homotopic to the identities along the flow. -/

@[expose] public section

namespace Finsler.LensContinuation

open CategoryTheory Set Topology Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop
open Finsler.BorelCrossing Finsler.BorelDeformation Finsler.PairTriple Finsler.FlowLens

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

section Inverse

variable {X Y : TopCat.{0}}

/-- Maps of pairs p : (t, s) → (t', s') and i : (t', s') → (t, s) whose composites are
homotopic to the identities through maps keeping the subsets: then p is bijective on
cohomology. -/
theorem bijective_Hmap_of_inverse {s t : Set X} {s' t' : Set Y} (hst : s ⊆ t) (hst' : s' ⊆ t')
    (p : C(t, t')) (i : C(t', t)) (hp : ∀ x : t, (x : X) ∈ s → (p x : Y) ∈ s')
    (hi : ∀ x : t', (x : Y) ∈ s' → (i x : X) ∈ s)
    (F : (i.comp p).Homotopy (ContinuousMap.id t))
    (hF : ∀ (τ : unitInterval) (x : t), (x : X) ∈ s → (F (τ, x) : X) ∈ s)
    (G : (p.comp i).Homotopy (ContinuousMap.id t'))
    (hG : ∀ (τ : unitInterval) (x : t'), (x : Y) ∈ s' → (G (τ, x) : Y) ∈ s') (n : ℕ) :
    Function.Bijective (Hmap (trivHom (pairMapX hst hst' p hp)) n) := by
  refine PairTriple.bijective_Hmap _ (fun k => ?_) n
  have e1 : pairMapX hst hst' p hp ≫ pairMapX hst' hst i hi =
      pairMapX hst hst (i.comp p) (fun x hx ↦ F.apply_zero x ▸ hF 0 x hx) :=
    (pairMapX_comp hst hst' hst p i hp hi).symm
  have e2 : 𝟙 (pairOf hst) =
      pairMapX hst hst (ContinuousMap.id t) (fun x hx ↦ F.apply_one x ▸ hF 1 x hx) :=
    (pairMapX_id hst).symm
  have H₁ : TopPair.Homotopy (pairMapX hst hst' p hp ≫ pairMapX hst' hst i hi)
      (𝟙 (pairOf hst)) := by
    rw [e1, e2]
    exact pairHomotopyX hst hst F hF
  have e3 : pairMapX hst' hst i hi ≫ pairMapX hst hst' p hp =
      pairMapX hst' hst' (p.comp i) (fun x hx ↦ G.apply_zero x ▸ hG 0 x hx) :=
    (pairMapX_comp hst' hst hst' i p hi hp).symm
  have e4 : 𝟙 (pairOf hst') =
      pairMapX hst' hst' (ContinuousMap.id t') (fun x hx ↦ G.apply_one x ▸ hG 1 x hx) :=
    (pairMapX_id hst').symm
  have H₂ : TopPair.Homotopy (pairMapX hst' hst i hi ≫ pairMapX hst hst' p hp)
      (𝟙 (pairOf hst')) := by
    rw [e3, e4]
    exact pairHomotopyX hst' hst' G hG
  exact BorelInvariance.bijective_nativePull_of_homotopyEquiv _ _ H₁ H₂ k

end Inverse

variable {W : TopCat.{0}} {g₀ g₁ : W → ℝ} (D : Descent W g₀)

/-- The same semiflow as a descent for another function which it does not increase. -/
def retarget (h : ∀ t w, 0 ≤ t → g₁ (D.flow t w) ≤ g₁ w) : Descent W g₁ where
  flow := D.flow
  cont := D.cont
  zero := D.zero
  add := D.add
  mono := h

variable (g : W → ℝ) (E : Descent W g) (𝒲 : Set W) (a b T : ℝ)

/-- The part of the sublevel of b in 𝒲. -/
def partU : Set W := {w | g w < b ∧ w ∈ 𝒲}

/-- The part of the lens set in 𝒲. -/
def partY : Set W := {w | g w < b ∧ g (E.flow T w) < a ∧ w ∈ 𝒲}

/-- The union of the part of the sublevel of b in 𝒲 and the lens set. -/
def unionL : Set W := partU g 𝒲 b ∪ lensY E a b T

theorem partY_sub_partU : partY g E 𝒲 a b T ⊆ partU g 𝒲 b := fun _ hw => ⟨hw.1, hw.2.2⟩

theorem partY_sub_lensY : partY g E 𝒲 a b T ⊆ lensY E a b T := fun _ hw => ⟨hw.1, hw.2.1⟩

theorem lensY_sub_unionL : lensY E a b T ⊆ unionL g E 𝒲 a b T := subset_union_right

variable {g E 𝒲 a b T}

/-- The lens pair in 𝒲 is an excision of the union relative to the lens set. -/
theorem exc_bijective (hg : Continuous g) (h𝒲 : IsOpen 𝒲) (n : ℕ) :
    Function.Bijective (Hmap (trivHom (inclPair (partY_sub_partU g E 𝒲 a b T)
      (lensY_sub_unionL g E 𝒲 a b T) (partY_sub_lensY g E 𝒲 a b T)
      (subset_union_left : partU g 𝒲 b ⊆ unionL g E 𝒲 a b T))) n) := by
  refine bijective_Hmap_excision _ _ _ _ ?_ (lensY E a b T) {w | g w < b ∧ w ∈ 𝒲}
    (lensY_isOpen E hg a b T) ((isOpen_lt hg continuous_const).inter h𝒲) ?_ ?_ ?_ n
  · exact fun w hw hw' => ⟨hw.1, hw'.2, hw.2⟩
  · rintro w (hw | hw)
    · exact Or.inr hw
    · exact Or.inl hw
  · exact fun w hw => hw.1
  · exact fun w hw => hw.1

/-- The flow keeps the union if the points of 𝒲 below b not taken below a stay in 𝒲 as long as
they are not taken below a. -/
theorem unionL_flow (hT : 0 ≤ T)
    (htrap : ∀ w, w ∈ 𝒲 → g w < b → a ≤ g (E.flow T w) → ∀ s, 0 ≤ s →
      a ≤ g (E.flow T (E.flow s w)) → E.flow s w ∈ 𝒲)
    (s : ℝ) (w : W) (hs : 0 ≤ s) (hw : w ∈ unionL g E 𝒲 a b T) :
    E.flow s w ∈ unionL g E 𝒲 a b T := by
  rcases hw with hw | hw
  · by_cases h : g (E.flow T (E.flow s w)) < a
    · exact Or.inr ⟨lt_of_le_of_lt (E.mono s w hs) hw.1, h⟩
    · have h' := not_lt.mp h
      exact Or.inl ⟨lt_of_le_of_lt (E.mono s w hs) hw.1,
        htrap w hw.2 hw.1 (h'.trans (mono_after E hs hT w)) s hs h'⟩
  · exact Or.inr (lensY_flow E hT s w hs hw)

section Main

variable {δ τ : ℝ} (h₁ : ∀ t w, 0 ≤ t → g₁ (D.flow t w) ≤ g₁ w)
  (hle : ∀ w, g₁ w ≤ g₀ w + δ) (hge : ∀ w, g₀ w ≤ g₁ w + δ) (hδ : 0 ≤ δ)
  (hT : 0 ≤ T) (hτ : 0 ≤ τ)
  (hpb : ∀ w, g₀ w < b + δ → g₀ (D.flow τ w) < b - δ)
  (hpa : ∀ w, g₀ w < a + δ → g₀ (D.flow τ w) < a - δ)
  (htrap : ∀ w, w ∈ 𝒲 → g₀ w < b + δ → a - δ ≤ g₀ (D.flow T w) → ∀ s, 0 ≤ s →
    a - δ ≤ g₀ (D.flow T (D.flow s w)) → D.flow s w ∈ 𝒲)

include hδ htrap in
theorem trap_zero (w : W) (hw : w ∈ 𝒲) (hb : g₀ w < b) (ha : a ≤ g₀ (D.flow T w)) (s : ℝ)
    (hs : 0 ≤ s) (ha' : a ≤ g₀ (D.flow T (D.flow s w))) : D.flow s w ∈ 𝒲 :=
  htrap w hw (by linarith) (by linarith) s hs (by linarith)

include hle hge htrap in
theorem trap_one (w : W) (hw : w ∈ 𝒲) (hb : g₁ w < b) (ha : a ≤ g₁ (D.flow T w)) (s : ℝ)
    (hs : 0 ≤ s) (ha' : a ≤ g₁ (D.flow T (D.flow s w))) : D.flow s w ∈ 𝒲 :=
  htrap w hw (by linarith [hge w]) (by linarith [hle (D.flow T w)]) s hs
    (by linarith [hle (D.flow T (D.flow s w))])

include hge hδ hT hτ hpb hpa htrap in
/-- The time-τ map takes the union and the lens set of g₁ into those of g₀. -/
theorem forward_mem (w : W) :
    (w ∈ unionL g₁ (retarget D h₁) 𝒲 a b T → D.flow τ w ∈ unionL g₀ D 𝒲 a b T) ∧
      (w ∈ lensY (retarget D h₁) a b T → D.flow τ w ∈ lensY D a b T) := by
  have hY : w ∈ lensY (retarget D h₁) a b T → D.flow τ w ∈ lensY D a b T := by
    intro hw
    have hw2 : g₁ (D.flow T w) < a := hw.2
    have e1 := hpb w (by linarith [hge w, hw.1])
    have e2 := hpa (D.flow T w) (by linarith [hge (D.flow T w)])
    rw [flow_comm D hT hτ] at e2
    exact ⟨by linarith, by linarith⟩
  refine ⟨?_, hY⟩
  rintro (hw | hw)
  · have e1 := hpb w (by linarith [hge w, hw.1])
    by_cases h : g₀ (D.flow T (D.flow τ w)) < a
    · exact Or.inr ⟨by linarith, h⟩
    · have h' := not_lt.mp h
      have h'' := h'.trans (mono_after D hτ hT w)
      exact Or.inl ⟨by linarith, htrap w hw.2 (by linarith [hge w, hw.1]) (by linarith) τ hτ
        (by linarith)⟩
  · exact Or.inr (hY hw)

include hle hδ hT hτ hpb hpa htrap in
/-- The time-τ map takes the union and the lens set of g₀ into those of g₁. -/
theorem backward_mem (w : W) :
    (w ∈ unionL g₀ D 𝒲 a b T → D.flow τ w ∈ unionL g₁ (retarget D h₁) 𝒲 a b T) ∧
      (w ∈ lensY D a b T → D.flow τ w ∈ lensY (retarget D h₁) a b T) := by
  have hY : w ∈ lensY D a b T → D.flow τ w ∈ lensY (retarget D h₁) a b T := by
    intro hw
    have e1 := hpb w (by linarith [hw.1])
    have e2 := hpa (D.flow T w) (by linarith [hw.2])
    rw [flow_comm D hT hτ] at e2
    exact ⟨by linarith [hle (D.flow τ w)], by
      change g₁ (D.flow T (D.flow τ w)) < a
      linarith [hle (D.flow T (D.flow τ w))]⟩
  refine ⟨?_, hY⟩
  rintro (hw | hw)
  · have e1 := hpb w (by linarith [hw.1])
    by_cases h : g₁ (D.flow T (D.flow τ w)) < a
    · exact Or.inr ⟨by linarith [hle (D.flow τ w)], h⟩
    · have h' := not_lt.mp h
      have e3 := hle (D.flow T (D.flow τ w))
      have e4 := mono_after D hτ hT w
      exact Or.inl ⟨by linarith [hle (D.flow τ w)], htrap w hw.2 (by linarith [hw.1])
        (by linarith) τ hτ (by linarith)⟩
  · exact Or.inr (hY hw)

/-- The time-τ map between two sets, each taken into the other. -/
def flowMap {u v : Set W} (τ : ℝ) (h : ∀ w, w ∈ u → D.flow τ w ∈ v) : C(u, v) :=
  ⟨fun w => ⟨D.flow τ w, h w w.2⟩,
    ((flow_continuous D τ).comp continuous_subtype_val).subtype_mk _⟩

/-- Flowing twice for decreasing times, as a homotopy from the composite of two time-τ maps to
the identity of a set kept by the flow. -/
def doubleHomotopy {u v : Set W} (hτ : 0 ≤ τ) (h : ∀ w, w ∈ u → D.flow τ w ∈ v)
    (h' : ∀ w, w ∈ v → D.flow τ w ∈ u) (hu : ∀ s w, 0 ≤ s → w ∈ u → D.flow s w ∈ u) :
    ((flowMap D τ h').comp (flowMap D τ h)).Homotopy (ContinuousMap.id u) where
  toFun p := ⟨D.flow ((1 - (p.1 : ℝ)) * τ) (D.flow ((1 - (p.1 : ℝ)) * τ) p.2),
    hu _ _ (mul_nonneg (sub_nonneg.mpr p.1.2.2) hτ)
      (hu _ _ (mul_nonneg (sub_nonneg.mpr p.1.2.2) hτ) p.2.2)⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    have hc : Continuous fun p : unitInterval × u => (1 - (p.1 : ℝ)) * τ :=
      (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul continuous_const
    exact D.cont.comp (hc.prodMk (D.cont.comp (hc.prodMk
      (continuous_subtype_val.comp continuous_snd))))
  map_zero_left w := by
    apply Subtype.ext
    change D.flow ((1 - ((0 : unitInterval) : ℝ)) * τ)
      (D.flow ((1 - ((0 : unitInterval) : ℝ)) * τ) (w : W)) = D.flow τ (D.flow τ (w : W))
    rw [show ((0 : unitInterval) : ℝ) = 0 from rfl, sub_zero, one_mul]
  map_one_left w := by
    apply Subtype.ext
    change D.flow ((1 - ((1 : unitInterval) : ℝ)) * τ)
      (D.flow ((1 - ((1 : unitInterval) : ℝ)) * τ) (w : W)) = (w : W)
    rw [show ((1 : unitInterval) : ℝ) = 1 from rfl, sub_self, zero_mul, D.zero, D.zero]

theorem doubleHomotopy_apply {u v : Set W} (hτ : 0 ≤ τ) (h : ∀ w, w ∈ u → D.flow τ w ∈ v)
    (h' : ∀ w, w ∈ v → D.flow τ w ∈ u) (hu : ∀ s w, 0 ≤ s → w ∈ u → D.flow s w ∈ u)
    (σ : unitInterval) (w : u) :
    (doubleHomotopy D hτ h h' hu (σ, w) : W) =
      D.flow ((1 - (σ : ℝ)) * τ) (D.flow ((1 - (σ : ℝ)) * τ) w) := rfl

include hle hge hδ hT hτ hpb hpa htrap in
/-- The time-τ map from the union of g₁ relative to its lens set to the union of g₀ relative
to its lens set is bijective on cohomology. -/
theorem flow_bijective (n : ℕ) :
    Function.Bijective (Hmap (trivHom (pairMapX
      (lensY_sub_unionL g₁ (retarget D h₁) 𝒲 a b T) (lensY_sub_unionL g₀ D 𝒲 a b T)
      (flowMap D τ fun w hw => (forward_mem D h₁ hge hδ hT hτ hpb hpa htrap w).1 hw)
      (fun w hw => (forward_mem D h₁ hge hδ hT hτ hpb hpa htrap w).2 hw))) n) := by
  have hu₁ : ∀ s w, 0 ≤ s → w ∈ unionL g₁ (retarget D h₁) 𝒲 a b T →
      D.flow s w ∈ unionL g₁ (retarget D h₁) 𝒲 a b T :=
    unionL_flow (E := retarget D h₁) hT (trap_one D hle hge htrap)
  have hu₀ : ∀ s w, 0 ≤ s → w ∈ unionL g₀ D 𝒲 a b T → D.flow s w ∈ unionL g₀ D 𝒲 a b T :=
    unionL_flow (E := D) hT (trap_zero D hδ htrap)
  have hf := fun w hw => (forward_mem D h₁ hge hδ hT hτ hpb hpa htrap w).1 hw
  have hb := fun w hw => (backward_mem D h₁ hle hδ hT hτ hpb hpa htrap w).1 hw
  refine bijective_Hmap_of_inverse _ _ (flowMap D τ hf) (flowMap D τ hb) _
    (fun w hw => (backward_mem D h₁ hle hδ hT hτ hpb hpa htrap w).2 hw)
    (doubleHomotopy D hτ hf hb hu₁) ?_ (doubleHomotopy D hτ hb hf hu₀) ?_ n
  · intro σ w hw
    have hs : 0 ≤ (1 - (σ : ℝ)) * τ := mul_nonneg (sub_nonneg.mpr σ.2.2) hτ
    exact lensY_flow (retarget D h₁) hT _ _ hs (lensY_flow (retarget D h₁) hT _ _ hs hw)
  · intro σ w hw
    have hs : 0 ≤ (1 - (σ : ℝ)) * τ := mul_nonneg (sub_nonneg.mpr σ.2.2) hτ
    exact lensY_flow D hT _ _ hs (lensY_flow D hT _ _ hs hw)

/-- The lens pairs in 𝒲 of two functions which differ by at most δ and have a common descent
have isomorphic cohomology, under the push and trapping hypotheses. -/
def continuationEquiv (hg₀ : Continuous g₀) (hg₁ : Continuous g₁) (h𝒲 : IsOpen 𝒲) (n : ℕ) :
    H (triv (pairOf (partY_sub_partU g₀ D 𝒲 a b T))) n ≃ₗ[ZMod 2]
      H (triv (pairOf (partY_sub_partU g₁ (retarget D h₁) 𝒲 a b T))) n :=
  ((LinearEquiv.ofBijective _ (exc_bijective (E := D) hg₀ h𝒲 n)).symm.trans
    (LinearEquiv.ofBijective _ (flow_bijective D h₁ hle hge hδ hT hτ hpb hpa htrap n))).trans
    (LinearEquiv.ofBijective _ (exc_bijective (E := retarget D h₁) hg₁ h𝒲 n))

end Main

end

end Finsler.LensContinuation
