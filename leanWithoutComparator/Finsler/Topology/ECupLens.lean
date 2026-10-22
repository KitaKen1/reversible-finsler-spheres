module

public import Finsler.Topology.ECup
public import Finsler.Topology.ConeLens
public import Finsler.Topology.LensCore
public import Finsler.Topology.LensParts
public import Finsler.Geometry.LevelCrossing

/-! The lens isomorphisms are linear over cup with a global class.

All isomorphisms of the lens machinery inside one space (moving the cuts through regular strips,
`LevelCrossing.cross_move`; the crossing and the lens pair of a trapping set,
`LensParts.crossingEquiv`; lens pairs with the same core, `LensCore`; the lens pair of a split
descent and its Thom pair, `ConeLens.coneEquiv`) are composites of maps of cohomology induced by
inclusions of pairs. Hence the injectivity of the cup with a global class transports along them
(`ECup.cupInjW_incl`, `ECup.cupInjW_rel`). -/

@[expose] public section

namespace Finsler.ECupLens

open CategoryTheory SphereOddDegree Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop
open Finsler.BorelCrossing Finsler.BorelDeformation Finsler.PairTriple Finsler.FlowLens
open Finsler.LensContinuation Finsler.LensFamily Finsler.LensLabels Finsler.LensParts
open Finsler.PairAdditive Finsler.CutMove Finsler.LensCore Finsler.ECup
open Set

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {W : TopCat.{0}} {p : ℕ} (c : cohomologyZMod2 W p)

/-! ### Moving the cuts -/

section Move

variable {g h : W → ℝ} (D : Descent W g)

/-- **Moving to tight cuts** (`LevelCrossing.cross_move`) for the cup with a global class. -/
theorem move_iff (hgc : Continuous g) {aw a c' bw : ℝ} (haw : aw ≤ a) (hac : a ≤ c')
    (hcb : c' ≤ bw) (hK₁ : IsCompact {w : W | aw ≤ g w ∧ g w ≤ a})
    (hK₂ : IsCompact {w : W | c' ≤ g w ∧ g w ≤ bw})
    (hs₁ : ∀ w, aw ≤ g w → g w ≤ a → g (D.flow 1 w) < g w)
    (hs₂ : ∀ w, c' ≤ g w → g w ≤ bw → g (D.flow 1 w) < g w)
    (hsa : sub h aw = sub g aw) (hsb : sub h bw = sub g bw) (habw : aw ≤ bw) (q : ℕ) :
    CupInjW c (sub_mono h habw) q ↔ CupInjW c (sub_mono g hac) q := by
  obtain ⟨s₂, hs₂0, hpush₂⟩ := exists_push_lt D hgc hK₂ hs₂
  obtain ⟨s₁, hs₁0, hpush₁⟩ := exists_push_lt D hgc hK₁ hs₁
  rw [← cupInjW_incl c (sub_mono h habw) (sub_mono g habw) _ _
    (eq_bijective (sub_mono h habw) (sub_mono g habw) hsa hsb q)
    (eq_bijective (sub_mono h habw) (sub_mono g habw) hsa hsb (p + q))]
  rw [cupInjW_incl c (sub_mono g (haw.trans hac)) (sub_mono g ((haw.trans hac).trans hcb))
    subset_rfl (sub_mono g hcb)
    (upper_bijective D (haw.trans hac) hcb hs₂0 hpush₂ q)
    (upper_bijective D (haw.trans hac) hcb hs₂0 hpush₂ (p + q))]
  exact (cupInjW_rel c (sub_mono g haw) (sub_mono g hac)
    (lower_bijective D haw hac hs₁0 hpush₁ q) (lower_bijective D haw hac hs₁0 hpush₁ (p + q))).symm

end Move

/-! ### The crossing and the lens pair of a trapping set -/

section Crossing

variable {g : W → ℝ} (D : Descent W g) {a' a b T : ℝ}

/-- **The crossing is the lens pair of a trapping set** (`LensParts.crossingEquiv`) for the cup
with a global class. -/
theorem crossing_iff {𝒲 : Set W} (hg : Continuous g) (hab : a ≤ b) (ha : a' < a)
    (hT : 0 ≤ T) (htrap : ∀ w, g w < b → a' ≤ g (D.flow T w) → w ∈ 𝒲) (q : ℕ) :
    CupInjW c ((sub_subset_lensY D hab hT).trans (lensY_subset D a b T)) q ↔
      CupInjW c (partY_sub_partU g D 𝒲 a b T) q := by
  have hpull : ∀ n, Function.Bijective (Hmap (trivHom (inclPair
      (part_sub (inter_subset_inter_right (lensN D a' T) (lensY_subset D a b T)) 𝒲)
      (inter_subset_inter_right (lensN D a' T) (lensY_subset D a b T))
      inter_subset_left inter_subset_left)) n) := fun n =>
    PairTriple.bijective_Hmap _ (fun k => Finsler.BorelLens.bijective_nativePull_of_eq
      (part_sub (inter_subset_inter_right (lensN D a' T) (lensY_subset D a b T)) 𝒲)
      (inter_subset_inter_right (lensN D a' T) (lensY_subset D a b T))
      inter_subset_left inter_subset_left
      (fun w hw => ⟨hw, htrap w hw.2.1 (le_of_lt hw.1)⟩)
      (fun w hw => ⟨hw, htrap w hw.2 (le_of_lt hw.1)⟩) k) n
  rw [← cupInjW_rel c (sub_subset_lensY D hab hT) (lensY_subset D a b T)
    (lens_bijective D hab hT q) (lens_bijective D hab hT (p + q))]
  rw [cupInjW_incl c (inter_subset_inter_right (lensN D a' T) (lensY_subset D a b T))
    (lensY_subset D a b T) inter_subset_right inter_subset_right
    (lensN_bijective D hg ha q) (lensN_bijective D hg ha (p + q))]
  rw [cupInjW_incl c
    (part_sub (inter_subset_inter_right (lensN D a' T) (lensY_subset D a b T)) 𝒲)
    (inter_subset_inter_right (lensN D a' T) (lensY_subset D a b T))
    inter_subset_left inter_subset_left (hpull q) (hpull (p + q))]
  exact (cupInjW_incl c
    (part_sub (inter_subset_inter_right (lensN D a' T) (lensY_subset D a b T)) 𝒲)
    (partY_sub_partU g D 𝒲 a b T) (piece_sub_partY D 𝒲) (piece_sub_partU D 𝒲)
    (piece_bijective D hg ha 𝒲 q) (piece_bijective D hg ha 𝒲 (p + q))).symm

/-- **Lens pairs with the same core** (`LensCore`) for the cup with a global class. -/
theorem core_iff (hg : Continuous g) (ha : a' < a) {𝒲 𝒲' : Set W}
    (hcore : ∀ w, g w < b → a' < g (D.flow T w) → (w ∈ 𝒲 ↔ w ∈ 𝒲')) (q : ℕ) :
    CupInjW c (partY_sub_partU g D 𝒲 a b T) q ↔ CupInjW c (partY_sub_partU g D 𝒲' a b T) q := by
  have hU : (lensN D a' T ∩ sub g b) ∩ 𝒲 = (lensN D a' T ∩ sub g b) ∩ 𝒲' := by
    ext w
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1, h2⟩, (hcore w h2 h1).mp h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1, h2⟩, (hcore w h2 h1).mpr h3⟩
  have hY : (lensN D a' T ∩ lensY D a b T) ∩ 𝒲 = (lensN D a' T ∩ lensY D a b T) ∩ 𝒲' := by
    ext w
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1, h2⟩, (hcore w h2.1 h1).mp h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1, h2⟩, (hcore w h2.1 h1).mpr h3⟩
  rw [cupInjW_incl c
    (part_sub (inter_subset_inter_right (lensN D a' T) (lensY_subset D a b T)) 𝒲)
    (partY_sub_partU g D 𝒲 a b T) (piece_sub_partY D 𝒲) (piece_sub_partU D 𝒲)
    (piece_bijective D (b := b) (T := T) hg ha 𝒲 q)
    (piece_bijective D (b := b) (T := T) hg ha 𝒲 (p + q))]
  rw [cupInjW_incl c
    (part_sub (inter_subset_inter_right (lensN D a' T) (lensY_subset D a b T)) 𝒲')
    (partY_sub_partU g D 𝒲' a b T) (piece_sub_partY D 𝒲') (piece_sub_partU D 𝒲')
    (piece_bijective D (b := b) (T := T) hg ha 𝒲' q)
    (piece_bijective D (b := b) (T := T) hg ha 𝒲' (p + q))]
  exact (cupInjW_incl c
    (part_sub (inter_subset_inter_right (lensN D a' T) (lensY_subset D a b T)) 𝒲)
    (part_sub (inter_subset_inter_right (lensN D a' T) (lensY_subset D a b T)) 𝒲')
    _ _ (eq_bijective _ _ hY hU q) (eq_bijective _ _ hY hU (p + q))).symm

end Crossing

/-! ### The lens pair of a split descent and its Thom pair -/

section Cone

open Finsler.ConeLens

variable {C : ConeLens.Cone W} {D : Descent W C.energy} {𝒲 : Set W} {a b T : ℝ}

/-- **The lens pair of a split descent is its Thom pair** (`ConeLens.coneEquiv`) for the cup
with a global class. -/
theorem cone_iff (hS : Split C D) (h𝒲 : IsOpen 𝒲)
    (hsat : ∀ l m w, 0 ≤ l → 0 ≤ m → w ∈ 𝒲 → C.sc l m w ∈ 𝒲)
    (htrap : ∀ w, w ∈ 𝒲 → C.energy w < b → a ≤ C.energy (D.flow T w) → ∀ s, 0 ≤ s →
      a ≤ C.energy (D.flow T (D.flow s w)) → D.flow s w ∈ 𝒲)
    {s₀ : ℝ} (hpush : ∀ w, w ∈ 𝒲 → C.np w = 0 → C.energy w < b →
      a ≤ C.energy (D.flow T w) → C.base (D.flow s₀ w) < b)
    (hT : 0 ≤ T) (hs₀ : 0 ≤ s₀) (q : ℕ) :
    CupInjW c (setY_sub_setU C D 𝒲 a b T) q ↔ CupInjW c (setSx_sub_setTb C D 𝒲 a b T) q := by
  rw [cupInjW_incl c (setY0_sub_setU0 C D 𝒲 a b T) (setY_sub_setU C D 𝒲 a b T)
    (setY0_sub_setY C D 𝒲 a b T) (setU0_sub_setU C 𝒲 b)
    (shrink_bijective hS hsat hT q) (shrink_bijective hS hsat hT (p + q))]
  rw [← cupInjW_incl c (setY0_sub_setU0 C D 𝒲 a b T)
    (subset_union_right : setYa C D a b T ⊆ setU0 C 𝒲 b ∪ setYa C D a b T)
    (setY0_sub_setYa C D 𝒲 a b T) subset_union_left
    (ConeLens.exc_bijective h𝒲 q) (ConeLens.exc_bijective h𝒲 (p + q))]
  rw [cupInjW_incl c (subset_union_right : setYa C D a b T ⊆ setTb C 𝒲 b ∪ setYa C D a b T)
    (subset_union_right : setYa C D a b T ⊆ setU0 C 𝒲 b ∪ setYa C D a b T) subset_rfl
    (union_subset_union_left _ (setTb_sub_setU0 C 𝒲 b))
    (push_bijective hS htrap hpush hT hs₀ q) (push_bijective hS htrap hpush hT hs₀ (p + q))]
  rw [cupInjW_incl c (setS_sub_setTb C D 𝒲 a b T)
    (subset_union_right : setYa C D a b T ⊆ setTb C 𝒲 b ∪ setYa C D a b T)
    (setS_sub_setYa C D 𝒲 a b T) subset_union_left
    (exc_tb_bijective h𝒲 q) (exc_tb_bijective h𝒲 (p + q))]
  exact (cupInjW_rel c (setS_sub_setSx hS hT) (setSx_sub_setTb C D 𝒲 a b T)
    (stretch_bijective hS hsat hT q) (stretch_bijective hS hsat hT (p + q))).symm

end Cone

end

end Finsler.ECupLens
