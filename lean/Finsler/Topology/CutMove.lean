module

public import Finsler.Topology.LensFamily

/-! Moving the cuts of a crossing through regular strips. Let a descent of g be given. If some
time takes the sublevel of a' below a (a ≤ a' ≤ b), flowing for that time deforms the pair
(sublevel of b, sublevel of a') into (sublevel of b, sublevel of a), so restriction from the
first pair to the second is bijective in cohomology. If some time takes the sublevel of b'
below b (a ≤ b ≤ b'), it deforms the sublevel of b' into the sublevel of b keeping the
sublevel of a, so restriction from (sublevel of b', sublevel of a) to (sublevel of b, sublevel
of a) is bijective. On a compact strip on which the time-one map decreases g strictly such a
time exists. Pairs of equal sets have isomorphic cohomology. Together: the crossing of g for
wide cuts is the crossing for tight cuts if g decreases strictly on the strips in between, and
two functions with the same sublevel sets at the cuts have the same crossing. -/

@[expose] public section

namespace Finsler.CutMove

open CategoryTheory Set Topology Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop
open Finsler.BorelCrossing Finsler.BorelDeformation Finsler.PairTriple Finsler.FlowLens
open Finsler.LensFamily Finsler.LensTrap

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {W : TopCat.{0}} {g : W → ℝ} (D : Descent W g)

/-- Flowing for a time which takes the sublevel of a' below a deforms (sublevel of b, sublevel
of a') into (sublevel of b, sublevel of a). -/
def lowerDeformation {a a' b s₀ : ℝ} (hs₀ : 0 ≤ s₀)
    (hpush : ∀ w, g w < a' → g (D.flow s₀ w) < a) :
    PairDeformation (sub g a) (sub g b) (sub g a') (sub g b) where
  r := ⟨fun w => ⟨D.flow s₀ w, sub_flow D b s₀ w hs₀ w.2⟩,
    ((flow_continuous D s₀).comp continuous_subtype_val).subtype_mk _⟩
  H := flowHomotopy D s₀ hs₀ (sub_flow D b)
  r_mem w := sub_flow D b s₀ w hs₀ w.2
  r_sub w hw := hpush w hw
  keep_sub' τ w hw := sub_flow D a' _ w (mul_nonneg τ.2.1 hs₀) hw
  keep τ w hw := sub_flow D b _ w (mul_nonneg τ.2.1 hs₀) hw
  keep_sub τ w hw := sub_flow D a _ w (mul_nonneg τ.2.1 hs₀) hw

/-- **Moving the lower cut.** -/
theorem lower_bijective {a a' b s₀ : ℝ} (haa : a ≤ a') (hab : a' ≤ b) (hs₀ : 0 ≤ s₀)
    (hpush : ∀ w, g w < a' → g (D.flow s₀ w) < a) (n : ℕ) :
    Function.Bijective (Hmap (trivHom (relPair (sub_mono g haa) (sub_mono g hab))) n) :=
  PairTriple.bijective_Hmap _ (fun k => bijective_nativePull_relPair (sub_mono g haa)
    (sub_mono g hab) (lowerDeformation D hs₀ hpush) k) n

/-- Flowing for a time which takes the sublevel of b' below b deforms the sublevel of b' into
the sublevel of b, keeping the sublevel of a. -/
def upperDeformation {a b b' s₀ : ℝ} (hs₀ : 0 ≤ s₀)
    (hpush : ∀ w, g w < b' → g (D.flow s₀ w) < b) :
    PairDeformation (sub g a) (sub g b) (sub g a) (sub g b') where
  r := ⟨fun w => ⟨D.flow s₀ w, sub_flow D b' s₀ w hs₀ w.2⟩,
    ((flow_continuous D s₀).comp continuous_subtype_val).subtype_mk _⟩
  H := flowHomotopy D s₀ hs₀ (sub_flow D b')
  r_mem w := hpush w w.2
  r_sub w hw := sub_flow D a s₀ w hs₀ hw
  keep_sub' τ w hw := sub_flow D a _ w (mul_nonneg τ.2.1 hs₀) hw
  keep τ w hw := sub_flow D b _ w (mul_nonneg τ.2.1 hs₀) hw
  keep_sub τ w hw := sub_flow D a _ w (mul_nonneg τ.2.1 hs₀) hw

/-- **Moving the upper cut.** -/
theorem upper_bijective {a b b' s₀ : ℝ} (hab : a ≤ b) (hbb : b ≤ b') (hs₀ : 0 ≤ s₀)
    (hpush : ∀ w, g w < b' → g (D.flow s₀ w) < b) (n : ℕ) :
    Function.Bijective (Hmap (trivHom (inclPair (sub_mono g hab) (sub_mono g (hab.trans hbb))
      subset_rfl (sub_mono g hbb))) n) :=
  PairTriple.bijective_Hmap _ (fun k => bijective_nativePull_inclPair (sub_mono g hab)
    (sub_mono g (hab.trans hbb)) subset_rfl (sub_mono g hbb) (upperDeformation D hs₀ hpush) k) n

omit D in
/-- The trivial deformation between pairs of equal sets. -/
def eqDeformation {s t s' t' : Set W} (hs : s' = s) (ht : t' = t) :
    PairDeformation s t s' t' where
  r := ContinuousMap.id t'
  H := ContinuousMap.Homotopy.refl (ContinuousMap.id t')
  r_mem x := ht ▸ x.2
  r_sub _ hx := hs ▸ hx
  keep_sub' _ _ hx := hx
  keep _ _ hx := hx
  keep_sub _ _ hx := hx

omit D in
/-- **Pairs of equal sets.** -/
theorem eq_bijective {s t s' t' : Set W} (hst : s ⊆ t) (hst' : s' ⊆ t') (hs : s = s')
    (ht : t = t') (n : ℕ) :
    Function.Bijective (Hmap (trivHom (inclPair hst hst' (hs ▸ subset_rfl) (ht ▸ subset_rfl))) n) :=
  PairTriple.bijective_Hmap _ (fun k => bijective_nativePull_inclPair hst hst'
    (hs ▸ subset_rfl) (ht ▸ subset_rfl) (eqDeformation hs.symm ht.symm) k) n

/-- **A push time on a regular strip.** If the strip {c₁ ≤ g ≤ c₂} is compact and the
time-one map decreases g strictly on it, some time takes the sublevel of c₂ (strictly below c₂)
below c₁. -/
theorem exists_push_lt (hg : Continuous g) {c₁ c₂ : ℝ}
    (hK : IsCompact {w : W | c₁ ≤ g w ∧ g w ≤ c₂})
    (hstrict : ∀ w, c₁ ≤ g w → g w ≤ c₂ → g (D.flow 1 w) < g w) :
    ∃ s₀ : ℝ, 0 ≤ s₀ ∧ ∀ w, g w < c₂ → g (D.flow s₀ w) < c₁ := by
  obtain ⟨s₀, hs₀, h⟩ := exists_push D hg hK hstrict
  exact ⟨s₀, hs₀, fun w hw => h w hw.le⟩

end

end Finsler.CutMove
