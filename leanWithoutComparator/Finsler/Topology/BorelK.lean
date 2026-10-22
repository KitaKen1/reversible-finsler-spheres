module

public import Finsler.Topology.BorelLoop
public import Finsler.Topology.BorelIterate
public import Finsler.Geometry.MilnorEquivariance
public import Finsler.Analysis.IntervalH1RotationContinuity
public import Finsler.Analysis.IntervalH1ShiftEnergy

/-! The group K = ⟨r, τ⟩ on the Finsler sublevel pairs. The half-shift τ is the circle action
by 1/2; it is an involution, preserves energy and fixes constant loops, so it acts on every pair
(t_a, M) and on (Λ, M), compatibly with the inclusions. Reversal and rotation satisfy
r(s + u) = (−s) + r(u), and −1/2 = 1/2 on the circle, so τ commutes with the reversal. The
pullback of τ is therefore a second cochain involution of the reflection cochains commuting with
the reversal, and the iterated Borel cochains compute the K-Borel cohomology of the sublevels. -/

@[expose] public section

namespace Finsler.BorelK

open CategoryTheory Set Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop
open Finsler.BorelIterate
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.SobolevEnergy
open Finsler.SobolevReverse Finsler.SobolevReflectionAction Finsler.MilnorHomotopy
open Finsler.MilnorEquivariance Finsler.SobolevCircleAction

noncomputable section

variable {n : ℕ} (F : ReversibleMetric n)

/-- Points of the circle differing by an integer agree. -/
theorem circle_eq_of_sub_int {x y : ℝ} (k : ℤ) (h : y - x = k) :
    ((x : ℝ) : SobolevCircleRepresentative.Circle) = ((y : ℝ) : SobolevCircleRepresentative.Circle) := by
  have h0 : ((y - x : ℝ) : SobolevCircleRepresentative.Circle) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨k, by rw [h, zsmul_eq_mul, mul_one]⟩
  rw [AddCircle.coe_sub, sub_eq_zero] at h0
  exact h0.symm

theorem pt_eq_of_sub_int (u : SphereLoop n) {x y : ℝ} (k : ℤ) (h : y - x = k) : pt u x = pt u y := by
  unfold pt
  rw [circle_eq_of_sub_int k h]

/-- Reversal and rotation: r(s + u) = (−s) + r(u). -/
theorem reverse_vadd (s : ℝ) (u : SphereLoop n) :
    reverseSphere (((s : ℝ) : SobolevCircleRepresentative.Circle) +ᵥ u) =
      (((-s : ℝ)) : SobolevCircleRepresentative.Circle) +ᵥ reverseSphere u := by
  apply sphereLoop_eq_of_representative_eq
  intro t
  apply Subtype.ext
  have ht := t.2
  change continuousRepresentative ((reverseSphere (((s : ℝ) :
      SobolevCircleRepresentative.Circle) +ᵥ u)).data : Space n) t =
    continuousRepresentative (((((-s : ℝ)) : SobolevCircleRepresentative.Circle) +ᵥ
      reverseSphere u).data : Space n) t
  rw [← pt_coe _ ht, ← pt_coe _ ht, pt_reverse _ ht, pt_vadd, pt_vadd]
  have hfl := Int.floor_le ((t : ℝ) + -s)
  have hfl' := Int.lt_floor_add_one ((t : ℝ) + -s)
  have hyI : (t : ℝ) + -s - ⌊(t : ℝ) + -s⌋ ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  rw [pt_eq_of_sub_int (reverseSphere u) (x := (t : ℝ) + -s)
    (y := (t : ℝ) + -s - ⌊(t : ℝ) + -s⌋) (-⌊(t : ℝ) + -s⌋) (by push_cast; ring),
    pt_reverse _ hyI]
  congr 1
  exact pt_eq_of_sub_int u ⌊(t : ℝ) + -s⌋ (by ring)

/-- The half phase. -/
abbrev half : SobolevCircleRepresentative.Circle := (((1 / 2 : ℝ)) : SobolevCircleRepresentative.Circle)

theorem half_add_half : half + half = 0 := by
  rw [← AddCircle.coe_add]
  have h : (1 / 2 : ℝ) + 1 / 2 = 1 := by norm_num
  rw [h, AddCircle.coe_period]

theorem neg_half : (((-(1 / 2) : ℝ)) : SobolevCircleRepresentative.Circle) = half :=
  circle_eq_of_sub_int 1 (by norm_num)

theorem half_half (u : SphereLoop n) : half +ᵥ (half +ᵥ u) = u := by
  rw [← add_vadd, half_add_half, zero_vadd]

theorem reverse_half (u : SphereLoop n) : reverseSphere (half +ᵥ u) = half +ᵥ reverseSphere u := by
  rw [reverse_vadd, neg_half]

theorem half_mem_consts {u : SphereLoop n} (hu : u ∈ consts n) : half +ᵥ u ∈ consts n := by
  obtain ⟨x, rfl⟩ := hu
  exact ⟨x, (constant_vadd half x).symm⟩

theorem half_mem_lev {a : ℝ} {u : SphereLoop n} (hu : u ∈ lev F a) : half +ᵥ u ∈ lev F a := by
  rcases hu with hu | hu
  · left
    change Real.sqrt (energy F (half +ᵥ u)) < a
    rw [Finsler.SobolevShiftEnergy.energy_vadd]
    exact hu
  · exact Or.inr (half_mem_consts hu)

theorem half_continuous : Continuous (fun u : SphereLoop n => half +ᵥ u) :=
  continuous_const_vadd half

/-- The half-shift on t_a. -/
def halfLev (a : ℝ) : C(lev F a, lev F a) :=
  ⟨fun u => ⟨half +ᵥ (u : SphereLoop n), half_mem_lev F u.2⟩,
    (half_continuous.comp continuous_subtype_val).subtype_mk _⟩

/-- The half-shift on Λ. -/
def halfFull (n : ℕ) : C((univ : Set (Loops n)), (univ : Set (Loops n))) :=
  ⟨fun u => ⟨half +ᵥ (u : SphereLoop n), mem_univ _⟩,
    (half_continuous.comp continuous_subtype_val).subtype_mk _⟩

/-- The half-shift as a map of pairs. -/
def halfPair (a : ℝ) : levPair F a ⟶ levPair F a :=
  pairMap _ _ (halfLev F a) (fun _ hx => half_mem_consts hx)

/-- The half-shift of (Λ, M). -/
def halfFullPair (n : ℕ) : fullPair n ⟶ fullPair n :=
  pairMap _ _ (halfFull n) (fun _ hx => half_mem_consts hx)

theorem halfPair_sq (a : ℝ) : halfPair F a ≫ halfPair F a = 𝟙 (levPair F a) := by
  have h : (halfLev F a).comp (halfLev F a) = ContinuousMap.id (lev F a) := by
    ext u
    exact congrArg Subtype.val (Subtype.ext (half_half (u : SphereLoop n)) :
      (⟨half +ᵥ (half +ᵥ (u : SphereLoop n)), half_mem_lev F (half_mem_lev F u.2)⟩ : lev F a) = u)
  exact (pairMap_comp (consts_subset_lev F a) (consts_subset_lev F a) (consts_subset_lev F a)
    (halfLev F a) (halfLev F a) (fun _ hx => half_mem_consts hx)
    (fun _ hx => half_mem_consts hx)).symm.trans
    ((pairMap_congr _ _ h _ (fun _ hx => hx)).trans (pairMap_id _))

theorem halfFullPair_sq (n : ℕ) : halfFullPair n ≫ halfFullPair n = 𝟙 (fullPair n) := by
  have h : (halfFull n).comp (halfFull n) = ContinuousMap.id (univ : Set (Loops n)) := by
    ext u
    exact congrArg Subtype.val (Subtype.ext (half_half (u : SphereLoop n)) :
      (⟨half +ᵥ (half +ᵥ (u : SphereLoop n)), mem_univ _⟩ : (univ : Set (Loops n))) = u)
  exact (pairMap_comp (subset_univ (consts n)) (subset_univ (consts n)) (subset_univ (consts n))
    (halfFull n) (halfFull n) (fun _ hx => half_mem_consts hx)
    (fun _ hx => half_mem_consts hx)).symm.trans
    ((pairMap_congr _ _ h _ (fun _ hx => hx)).trans (pairMap_id _))

theorem halfPair_rev (a : ℝ) : halfPair F a ≫ revPair F a = revPair F a ≫ halfPair F a := by
  have h : (revLev F a).comp (halfLev F a) = (halfLev F a).comp (revLev F a) := by
    ext u
    exact congrArg Subtype.val (Subtype.ext (reverse_half (u : SphereLoop n)) :
      (⟨reverseSphere (half +ᵥ (u : SphereLoop n)), reverse_mem_lev F (half_mem_lev F u.2)⟩ :
        lev F a) = ⟨half +ᵥ reverseSphere (u : SphereLoop n), half_mem_lev F (reverse_mem_lev F u.2)⟩)
  exact (pairMap_comp _ _ _ (halfLev F a) (revLev F a) (fun _ hx => half_mem_consts hx)
    (fun _ hx => reverse_mem_consts hx)).symm.trans
    ((pairMap_congr _ _ h _ (fun _ hx => half_mem_consts (reverse_mem_consts hx))).trans
      (pairMap_comp _ _ _ (revLev F a) (halfLev F a) (fun _ hx => reverse_mem_consts hx)
        (fun _ hx => half_mem_consts hx)))

/-- The pullback of the half-shift commutes with the reversal on the reflection cochains. -/
def halfCommuting (a : ℝ) : Commuting (levComplex F a) where
  s j := ((pull (halfPair F a)).f j).hom
  ss j x := by
    have h := pull_comp_apply (halfPair F a) (halfPair F a) j x
    have h' : ((pull (halfPair F a ≫ halfPair F a)).f j).hom x = x := by
      rw [halfPair_sq]
      exact pull_id_apply _ j x
    exact h.symm.trans h'
  sd j x := pull_comm_apply (halfPair F a) j x
  st j x := by
    have h1 := pull_comp_apply (halfPair F a) (revPair F a) j (x : (cochains (levPair F a)).X j)
    have h2 := pull_comp_apply (revPair F a) (halfPair F a) j (x : (cochains (levPair F a)).X j)
    rw [halfPair_rev] at h1
    exact h1.symm.trans h2

/-- The K-Borel cochains of (t_a, M): reflection Borel cochains with the half-shift. -/
abbrev kComplex (a : ℝ) : InvComplex := borelInv (halfCommuting F a)

/-- The K-Borel cohomology of (t_a, M). -/
abbrev HK (a : ℝ) (q : ℕ) : Type := HR (kComplex F a) q

/-- The sign sequence H_K^{q} →v→ H_K^{q+1} → H_R^{q+1}: exactness at H_K^{q+1}. -/
theorem exact_sign_forget (a : ℝ) (q : ℕ) (x : HK F a (q + 1)) :
    forget (kComplex F a) (q + 1) x = 0 ↔ ∃ y : HK F a q, w (kComplex F a) q y = x :=
  exact_forget (kComplex F a) q x

/-- The sign sequence: exactness at H_K^q between transfer and v. -/
theorem exact_sign_w (a : ℝ) (q : ℕ) (y : HK F a q) :
    w (kComplex F a) q y = 0 ↔ ∃ z : H (kComplex F a) q, transfer (kComplex F a) q z = y :=
  exact_w (kComplex F a) q y

/-- The ordinary cohomology of the K-cochains is the reflection Borel cohomology. -/
def forgetTargetEquiv (a : ℝ) (q : ℕ) : H (kComplex F a) q ≃ₗ[ZMod 2] HR (levComplex F a) q :=
  cohomologyEquiv (halfCommuting F a) q

theorem halfFullPair_rev (n : ℕ) :
    halfFullPair n ≫ revFullPair n = revFullPair n ≫ halfFullPair n := by
  have h : (revFull n).comp (halfFull n) = (halfFull n).comp (revFull n) := by
    ext u
    exact congrArg Subtype.val (Subtype.ext (reverse_half (u : SphereLoop n)) :
      (⟨reverseSphere (half +ᵥ (u : SphereLoop n)), mem_univ _⟩ : (univ : Set (Loops n))) =
        ⟨half +ᵥ reverseSphere (u : SphereLoop n), mem_univ _⟩)
  exact (pairMap_comp _ _ _ (halfFull n) (revFull n) (fun _ hx => half_mem_consts hx)
    (fun _ hx => reverse_mem_consts hx)).symm.trans
    ((pairMap_congr _ _ h _ (fun _ hx => half_mem_consts (reverse_mem_consts hx))).trans
      (pairMap_comp _ _ _ (revFull n) (halfFull n) (fun _ hx => reverse_mem_consts hx)
        (fun _ hx => half_mem_consts hx)))

/-- The half-shift on the cochains of (Λ, M). -/
def halfCommutingFull (n : ℕ) : Commuting (fullComplex n) where
  s j := ((pull (halfFullPair n)).f j).hom
  ss j x := by
    have h := pull_comp_apply (halfFullPair n) (halfFullPair n) j x
    have h' : ((pull (halfFullPair n ≫ halfFullPair n)).f j).hom x = x := by
      rw [halfFullPair_sq]
      exact pull_id_apply _ j x
    exact h.symm.trans h'
  sd j x := pull_comm_apply (halfFullPair n) j x
  st j x := by
    have h1 := pull_comp_apply (halfFullPair n) (revFullPair n) j x
    have h2 := pull_comp_apply (revFullPair n) (halfFullPair n) j x
    rw [halfFullPair_rev] at h1
    exact h1.symm.trans h2

theorem cutPair_half {a b : ℝ} (hab : a ≤ b) :
    cutPair F hab ≫ halfPair F b = halfPair F a ≫ cutPair F hab := by
  have h : (halfLev F b).comp (inclLev F hab) = (inclLev F hab).comp (halfLev F a) := by
    ext u
    rfl
  exact (pairMap_comp _ _ _ (inclLev F hab) (halfLev F b) (fun _ hx => hx)
    (fun _ hx => half_mem_consts hx)).symm.trans
    ((pairMap_congr _ _ h _ (fun _ hx => half_mem_consts hx)).trans
      (pairMap_comp _ _ _ (halfLev F a) (inclLev F hab) (fun _ hx => half_mem_consts hx)
        (fun _ hx => hx)))

theorem resPair_half (a : ℝ) :
    resPair F a ≫ halfFullPair n = halfPair F a ≫ resPair F a := by
  have h : (halfFull n).comp (inclFull F a) = (inclFull F a).comp (halfLev F a) := by
    ext u
    rfl
  exact (pairMap_comp _ _ _ (inclFull F a) (halfFull n) (fun _ hx => hx)
    (fun _ hx => half_mem_consts hx)).symm.trans
    ((pairMap_congr _ _ h _ (fun _ hx => half_mem_consts hx)).trans
      (pairMap_comp _ _ _ (halfLev F a) (inclFull F a) (fun _ hx => half_mem_consts hx)
        (fun _ hx => hx)))

/-- Restriction from (Λ, M) to (t_a, M) commutes with the half-shift. -/
def resComm (a : ℝ) : CommHom (halfCommutingFull n) (halfCommuting F a) where
  φ := resHom F a
  comm_s j x := by
    have h1 := pull_comp_apply (resPair F a) (halfFullPair n) j x
    have h2 := pull_comp_apply (halfPair F a) (resPair F a) j x
    rw [resPair_half] at h1
    exact h1.symm.trans h2

/-- Restriction from (t_b, M) to (t_a, M) commutes with the half-shift. -/
def cutComm {a b : ℝ} (hab : a ≤ b) : CommHom (halfCommuting F b) (halfCommuting F a) where
  φ := cutHom F hab
  comm_s j x := by
    have h1 := pull_comp_apply (cutPair F hab) (halfPair F b) j x
    have h2 := pull_comp_apply (halfPair F a) (cutPair F hab) j x
    rw [cutPair_half] at h1
    exact h1.symm.trans h2

/-- The K-cochains of (Λ, M). -/
abbrev kFull (n : ℕ) : InvComplex := borelInv (halfCommutingFull n)

theorem cut_res_k_f {a b : ℝ} (hab : a ≤ b) (j : ℕ) (x : (kFull n).C j) :
    (invHomComp (borelHom (resComm F b)) (borelHom (cutComm F hab))).f j x =
      (borelHom (resComm F a)).f j x := by
  apply Subtype.ext
  funext i
  exact cut_res_f F hab i _

/-- The sign Gysin system of the K-Borel cohomology of the Finsler sublevels: the same
filtered Gysin interface, now relating K-Borel and reflection Borel cohomology. -/
def signData :
    Finsler.FilteredGysin.Data (fun q => H (kFull n) q) (fun q => HR (kFull n) q)
      (fun a q => H (kComplex F a) q) (fun a q => HR (kComplex F a) q) where
  w q := (w (kFull n) q).toAddMonoidHom
  forget q := (forget (kFull n) q).toAddMonoidHom
  transfer q := (transfer (kFull n) q).toAddMonoidHom
  wB a q := (w (kComplex F a) q).toAddMonoidHom
  forgetB a q := (forget (kComplex F a) q).toAddMonoidHom
  transferB a q := (transfer (kComplex F a) q).toAddMonoidHom
  resA a q := (Hmap (borelHom (resComm F a)) q).toAddMonoidHom
  resB a q := (HRmap (borelHom (resComm F a)) q).toAddMonoidHom
  cutA a b hab q := (Hmap (borelHom (cutComm F hab)) q).toAddMonoidHom
  cutB a b hab q := (HRmap (borelHom (cutComm F hab)) q).toAddMonoidHom
  exact_forget q x := exact_forget (kFull n) q x
  exact_w q y := exact_w (kFull n) q y
  exact_wB a q y := exact_w (kComplex F a) q y
  natural_forget a q x := Hmap_forget (borelHom (resComm F a)) q x
  natural_w a q y := (HRmap_w (borelHom (resComm F a)) q y).symm
  natural_transfer a q z := HRmap_transfer (borelHom (resComm F a)) q z
  natural_cutA a b hab q z := by
    change Hmap (borelHom (cutComm F hab)) q (Hmap (borelHom (resComm F b)) q z) =
      Hmap (borelHom (resComm F a)) q z
    rw [← Hmap_comp]
    exact Hmap_congr (cut_res_k_f F hab) q z
  natural_cutB a b hab q y := by
    change HRmap (borelHom (cutComm F hab)) q (HRmap (borelHom (resComm F b)) q y) =
      HRmap (borelHom (resComm F a)) q y
    rw [← HRmap_comp]
    exact HRmap_congr (cut_res_k_f F hab) q y
  natural_cut_transfer a b hab q z := HRmap_transfer (borelHom (cutComm F hab)) q z

/-- The K-Borel cohomology of the Finsler sublevels realizes the filtered Gysin interface for
the sign sequence relating it to the reflection Borel cohomology. -/
theorem exists_signData :
    Nonempty (Finsler.FilteredGysin.Data (fun q => H (kFull n) q) (fun q => HR (kFull n) q)
      (fun a q => H (kComplex F a) q) (fun a q => HR (kComplex F a) q)) :=
  ⟨signData F⟩

end

end Finsler.BorelK
