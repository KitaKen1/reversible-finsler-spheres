module

public import Finsler.Topology.BorelCrossing
public import Finsler.Topology.BorelQuasiIso
public import Finsler.Topology.BorelK

/-! The crossing sequence for K = ⟨r, τ⟩. The half-shift acts on the crossing pair (t_b, t_a) and
commutes with the reversal, so the crossing cochains carry a second commuting involution and the
map C(t_b, t_a) → C(t_b, M) commutes with it. The degreewise short exact sequence of the reflection
cochains therefore induces a degreewise short exact sequence of the iterated Borel complexes, and
the K-Borel cohomology has the long exact sequence
⋯ → H_K^q(t_b, t_a) → H_K^q(t_b, M) → H_K^q(t_a, M) → H_K^{q+1}(t_b, t_a) → ⋯,
whose connecting map commutes with multiplication by v. The tail pair (Λ, t_a) has the same
structure and the same sequence relating global K-classes to H_K(t_a, M). No localization or
fixed-point statement is made in this file. -/

@[expose] public section

namespace Finsler.BorelCrossingK

open CategoryTheory Set Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop
open Finsler.BorelIterate Finsler.BorelK Finsler.BorelCrossing
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.SobolevReverse

noncomputable section

variable {n : ℕ} (F : ReversibleMetric n) {a b : ℝ} (hab : a ≤ b)

/-- The half-shift of the crossing pair (t_b, t_a). -/
def halfCross : crossPair F hab ⟶ crossPair F hab :=
  pairMap _ _ (halfLev F b) (fun _ hx => half_mem_lev F hx)

theorem halfCross_sq : halfCross F hab ≫ halfCross F hab = 𝟙 (crossPair F hab) := by
  have h : (halfLev F b).comp (halfLev F b) = ContinuousMap.id (lev F b) := by
    ext u
    exact congrArg Subtype.val (Subtype.ext (half_half (u : SphereLoop n)) :
      (⟨half +ᵥ (half +ᵥ (u : SphereLoop n)), half_mem_lev F (half_mem_lev F u.2)⟩ : lev F b) = u)
  exact (pairMap_comp (lev_mono F hab) (lev_mono F hab) (lev_mono F hab)
    (halfLev F b) (halfLev F b) (fun _ hx => half_mem_lev F hx)
    (fun _ hx => half_mem_lev F hx)).symm.trans
    ((pairMap_congr _ _ h _ (fun _ hx => hx)).trans (pairMap_id _))

theorem halfCross_rev :
    halfCross F hab ≫ revCross F hab = revCross F hab ≫ halfCross F hab := by
  have h : (revLev F b).comp (halfLev F b) = (halfLev F b).comp (revLev F b) := by
    ext u
    exact congrArg Subtype.val (Subtype.ext (reverse_half (u : SphereLoop n)) :
      (⟨reverseSphere (half +ᵥ (u : SphereLoop n)), reverse_mem_lev F (half_mem_lev F u.2)⟩ :
        lev F b) = ⟨half +ᵥ reverseSphere (u : SphereLoop n), half_mem_lev F (reverse_mem_lev F u.2)⟩)
  exact (pairMap_comp _ _ _ (halfLev F b) (revLev F b) (fun _ hx => half_mem_lev F hx)
    (fun _ hx => reverse_mem_lev F hx)).symm.trans
    ((pairMap_congr _ _ h _ (fun _ hx => half_mem_lev F (reverse_mem_lev F hx))).trans
      (pairMap_comp _ _ _ (revLev F b) (halfLev F b) (fun _ hx => reverse_mem_lev F hx)
        (fun _ hx => half_mem_lev F hx)))

/-- The pullback of the half-shift commutes with the reversal on the crossing cochains. -/
def halfCommutingCross : Commuting (crossComplex F hab) where
  s j := ((pull (halfCross F hab)).f j).hom
  ss j x := by
    have h := pull_comp_apply (halfCross F hab) (halfCross F hab) j x
    have h' : ((pull (halfCross F hab ≫ halfCross F hab)).f j).hom x = x := by
      rw [halfCross_sq]
      exact pull_id_apply _ j x
    exact h.symm.trans h'
  sd j x := pull_comm_apply (halfCross F hab) j x
  st j x := by
    have h1 := pull_comp_apply (halfCross F hab) (revCross F hab) j
      (x : (cochains (crossPair F hab)).X j)
    have h2 := pull_comp_apply (revCross F hab) (halfCross F hab) j
      (x : (cochains (crossPair F hab)).X j)
    rw [halfCross_rev] at h1
    exact h1.symm.trans h2

/-- The K-Borel cochains of the crossing pair. -/
abbrev kCross : InvComplex := borelInv (halfCommutingCross F hab)

/-- The K-Borel cohomology of the crossing pair. -/
abbrev HKCross (q : ℕ) : Type := HR (kCross F hab) q

theorem relLev_half : relLev F hab ≫ halfCross F hab = halfPair F b ≫ relLev F hab := by
  ext : 2 <;> rfl

/-- The map C(t_b, t_a) → C(t_b, M) commutes with the half-shift. -/
def relComm : CommHom (halfCommutingCross F hab) (halfCommuting F b) where
  φ := relHom F hab
  comm_s j x := by
    have h1 := pull_comp_apply (relLev F hab) (halfCross F hab) j x
    have h2 := pull_comp_apply (halfPair F b) (relLev F hab) j x
    rw [relLev_half] at h1
    exact h1.symm.trans h2

/-- The K-Borel cochains of (t_b, t_a), (t_b, M) and (t_a, M) form a degreewise short exact
sequence of involutive complexes. -/
theorem shortExact :
    BorelExact.ShortExact (borelHom (relComm F hab)) (borelHom (cutComm F hab)) :=
  BorelQuasiIso.shortExact_iterated (relComm F hab) (cutComm F hab)
    (BorelCrossing.shortExact F hab)

/-- Exactness of the K-Borel crossing sequence at H_K(t_b, M). -/
theorem exact_crossing (q : ℕ) (x : HK F b q)
    (hx : HRmap (borelHom (cutComm F hab)) q x = 0) :
    ∃ z : HKCross F hab q, HRmap (borelHom (relComm F hab)) q z = x :=
  BorelExact.exact_mid (shortExact F hab) q x hx

theorem crossing_cut_zero (q : ℕ) (z : HKCross F hab q) :
    HRmap (borelHom (cutComm F hab)) q (HRmap (borelHom (relComm F hab)) q z) = 0 :=
  BorelExact.comp_zero (shortExact F hab) q z

/-- The connecting map H_K^q(t_a, M) → H_K^{q+1}(t_b, t_a). -/
def crossDelta (q : ℕ) : HK F a q →ₗ[ZMod 2] HKCross F hab (q + 1) :=
  BorelExact.delta (shortExact F hab) q

theorem crossDelta_cut (q : ℕ) (x : HK F b q) :
    crossDelta F hab q (HRmap (borelHom (cutComm F hab)) q x) = 0 :=
  BorelExact.delta_comp_zero (shortExact F hab) q x

/-- Exactness at H_K(t_a, M). -/
theorem exact_crossDelta (q : ℕ) (x : HK F a q) (hx : crossDelta F hab q x = 0) :
    ∃ y : HK F b q, HRmap (borelHom (cutComm F hab)) q y = x :=
  BorelExact.exact_delta (shortExact F hab) q x hx

theorem rel_crossDelta (q : ℕ) (x : HK F a q) :
    HRmap (borelHom (relComm F hab)) (q + 1) (crossDelta F hab q x) = 0 :=
  BorelExact.comp_delta_zero (shortExact F hab) q x

/-- Exactness at the K-crossing group in positive degree. -/
theorem exact_crossing_sub (q : ℕ) (y : HKCross F hab (q + 1))
    (hy : HRmap (borelHom (relComm F hab)) (q + 1) y = 0) :
    ∃ x : HK F a q, crossDelta F hab q x = y :=
  BorelExact.exact_sub (shortExact F hab) q y hy

/-- The connecting map commutes with multiplication by v. -/
theorem crossDelta_v (q : ℕ) (x : HK F a q) :
    crossDelta F hab (q + 1) (w _ q x) = w _ (q + 1) (crossDelta F hab q x) :=
  BorelExact.delta_w (shortExact F hab) q x

/-- The ordinary cohomology of the K-crossing cochains is the reflection crossing group. -/
def forgetTargetEquiv (q : ℕ) : H (kCross F hab) q ≃ₗ[ZMod 2] HR (crossComplex F hab) q :=
  cohomologyEquiv (halfCommutingCross F hab) q

/-- Forgetting τ is natural for the crossing map. -/
theorem forget_rel (q : ℕ) (z : HKCross F hab q) :
    BorelK.forgetTargetEquiv F b q (forget _ q (HRmap (borelHom (relComm F hab)) q z)) =
      HRmap (relHom F hab) q (forgetTargetEquiv F hab q (forget _ q z)) := by
  rw [← Hmap_forget]
  exact cohomologyEquiv_natural (relComm F hab) q _

section Tail

variable (a : ℝ)

/-- The half-shift of the tail pair (Λ, t_a). -/
def halfTail : tailPair F a ⟶ tailPair F a :=
  pairMap _ _ (halfFull n) (fun _ hx => half_mem_lev F hx)

theorem halfTail_sq : halfTail F a ≫ halfTail F a = 𝟙 (tailPair F a) := by
  have h : (halfFull n).comp (halfFull n) = ContinuousMap.id (univ : Set (Loops n)) := by
    ext u
    exact congrArg Subtype.val (Subtype.ext (half_half (u : SphereLoop n)) :
      (⟨half +ᵥ (half +ᵥ (u : SphereLoop n)), mem_univ _⟩ : (univ : Set (Loops n))) = u)
  exact (pairMap_comp (subset_univ (lev F a)) (subset_univ (lev F a)) (subset_univ (lev F a))
    (halfFull n) (halfFull n) (fun _ hx => half_mem_lev F hx)
    (fun _ hx => half_mem_lev F hx)).symm.trans
    ((pairMap_congr _ _ h _ (fun _ hx => hx)).trans (pairMap_id _))

theorem halfTail_rev : halfTail F a ≫ revTail F a = revTail F a ≫ halfTail F a := by
  have h : (revFull n).comp (halfFull n) = (halfFull n).comp (revFull n) := by
    ext u
    exact congrArg Subtype.val (Subtype.ext (reverse_half (u : SphereLoop n)) :
      (⟨reverseSphere (half +ᵥ (u : SphereLoop n)), mem_univ _⟩ : (univ : Set (Loops n))) =
        ⟨half +ᵥ reverseSphere (u : SphereLoop n), mem_univ _⟩)
  exact (pairMap_comp _ _ _ (halfFull n) (revFull n) (fun _ hx => half_mem_lev F hx)
    (fun _ hx => reverse_mem_lev F hx)).symm.trans
    ((pairMap_congr _ _ h _ (fun _ hx => half_mem_lev F (reverse_mem_lev F hx))).trans
      (pairMap_comp _ _ _ (revFull n) (halfFull n) (fun _ hx => reverse_mem_lev F hx)
        (fun _ hx => half_mem_lev F hx)))

/-- The pullback of the half-shift commutes with the reversal on the tail cochains. -/
def halfCommutingTail : Commuting (tailComplex F a) where
  s j := ((pull (halfTail F a)).f j).hom
  ss j x := by
    have h := pull_comp_apply (halfTail F a) (halfTail F a) j x
    have h' : ((pull (halfTail F a ≫ halfTail F a)).f j).hom x = x := by
      rw [halfTail_sq]
      exact pull_id_apply _ j x
    exact h.symm.trans h'
  sd j x := pull_comm_apply (halfTail F a) j x
  st j x := by
    have h1 := pull_comp_apply (halfTail F a) (revTail F a) j
      (x : (cochains (tailPair F a)).X j)
    have h2 := pull_comp_apply (revTail F a) (halfTail F a) j
      (x : (cochains (tailPair F a)).X j)
    rw [halfTail_rev] at h1
    exact h1.symm.trans h2

/-- The K-Borel cochains of the tail pair. -/
abbrev kTail : InvComplex := borelInv (halfCommutingTail F a)

/-- The K-Borel cohomology of the tail pair. -/
abbrev HKTail (q : ℕ) : Type := HR (kTail F a) q

theorem relFull_half : relFull F a ≫ halfTail F a = halfFullPair n ≫ relFull F a := by
  ext : 2 <;> rfl

/-- The map C(Λ, t_a) → C(Λ, M) commutes with the half-shift. -/
def tailComm : CommHom (halfCommutingTail F a) (halfCommutingFull n) where
  φ := tailHom F a
  comm_s j x := by
    have h1 := pull_comp_apply (relFull F a) (halfTail F a) j x
    have h2 := pull_comp_apply (halfFullPair n) (relFull F a) j x
    rw [relFull_half] at h1
    exact h1.symm.trans h2

/-- The K-Borel cochains of (Λ, t_a), (Λ, M) and (t_a, M) form a degreewise short exact
sequence of involutive complexes. -/
theorem shortExactTail :
    BorelExact.ShortExact (borelHom (tailComm F a)) (borelHom (resComm F a)) :=
  BorelQuasiIso.shortExact_iterated (tailComm F a) (resComm F a)
    (BorelCrossing.shortExactTail F a)

/-- A global K-class vanishing on t_a comes from the K-tail group. -/
theorem exact_tail (q : ℕ) (x : HR (kFull n) q)
    (hx : HRmap (borelHom (resComm F a)) q x = 0) :
    ∃ z : HKTail F a q, HRmap (borelHom (tailComm F a)) q z = x :=
  BorelExact.exact_mid (shortExactTail F a) q x hx

/-- The connecting map H_K^q(t_a, M) → H_K^{q+1}(Λ, t_a). -/
def tailDelta (q : ℕ) : HK F a q →ₗ[ZMod 2] HKTail F a (q + 1) :=
  BorelExact.delta (shortExactTail F a) q

/-- A K-class of (t_a, M) with zero connecting image is the restriction of a global K-class. -/
theorem exact_tailDelta (q : ℕ) (x : HK F a q) (hx : tailDelta F a q x = 0) :
    ∃ y : HR (kFull n) q, HRmap (borelHom (resComm F a)) q y = x :=
  BorelExact.exact_delta (shortExactTail F a) q x hx

/-- Exactness at the K-tail group in positive degree. -/
theorem exact_tail_sub (q : ℕ) (y : HKTail F a (q + 1))
    (hy : HRmap (borelHom (tailComm F a)) (q + 1) y = 0) :
    ∃ x : HK F a q, tailDelta F a q x = y :=
  BorelExact.exact_sub (shortExactTail F a) q y hy

/-- The tail connecting map commutes with multiplication by v. -/
theorem tailDelta_v (q : ℕ) (x : HK F a q) :
    tailDelta F a (q + 1) (w _ q x) = w _ (q + 1) (tailDelta F a q x) :=
  BorelExact.delta_w (shortExactTail F a) q x

end Tail

end

end Finsler.BorelCrossingK
