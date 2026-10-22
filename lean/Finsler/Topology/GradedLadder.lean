module

public import Finsler.Topology.TotalExact
public import Finsler.Algebra.LadderBudget

/-! The change of the potential of a cutoff across a crossing, for graded families. The fixed
side is a long exact sequence of graded F₂-vector spaces W → V' → V → W[1] given degreewise; the
ambient side consists of two rows C → A' → A → C of vector spaces with comparison maps into the
graded pieces, given componentwise. With the products over all degrees as totals and the
truncation to the degrees at most j as projection, the two statements of `LadderBudget` give:
at a far cutoff the potential does not increase, and in general it changes by at most six times
a bound for the dimensions of the total of W and of two ambient crossing groups. Everything is
stated for families with given group and module structures on the pieces, so that no structure
on a product has to be found for particular families. -/

@[expose] public section

namespace Finsler.GradedLadder

open Module
open Finsler.TripleK Finsler.TotalExact Finsler.LadderBudget

noncomputable section

section Tot

variable {X : Type} [AddCommGroup X] [Module (ZMod 2) X] {G : ℕ → Type}
  [∀ q, AddCommGroup (G q)] [∀ q, Module (ZMod 2) (G q)]

/-- The map into the product of the pieces with given components. -/
def totMap (e : ∀ l, X →ₗ[ZMod 2] G l) : X →ₗ[ZMod 2] ((q : ℕ) → G q) := LinearMap.pi e

theorem totMap_apply (e : ∀ l, X →ₗ[ZMod 2] G l) (x : X) (l : ℕ) : totMap e x l = e l x := rfl

end Tot

section Defs

variable (G : ℕ → Type) [∀ q, AddCommGroup (G q)] [∀ q, Module (ZMod 2) (G q)]

/-- The product of the pieces is finite dimensional. -/
def FinTot : Prop := Module.Finite (ZMod 2) ((q : ℕ) → G q)

/-- The dimension of the product of the pieces. -/
def totRank : ℕ := finrank (ZMod 2) ((q : ℕ) → G q)

/-- Finite dimensional pieces which vanish from some degree on have a finite dimensional
product. -/
theorem finTot_of_vanish [∀ q, Module.Finite (ZMod 2) (G q)] {Q : ℕ}
    (hz : ∀ q, Q ≤ q → ∀ x : G q, x = 0) : FinTot G :=
  finite_total G hz

/-- If all pieces vanish, the product has dimension zero. -/
theorem totRank_eq_zero (hz : ∀ q (x : G q), x = 0) : totRank G = 0 := by
  have : Subsingleton ((q : ℕ) → G q) :=
    ⟨fun x y => funext fun q => (hz q (x q)).trans (hz q (y q)).symm⟩
  exact Module.finrank_zero_of_subsingleton

variable {Y X : Type} [AddCommGroup Y] [Module (ZMod 2) Y] [AddCommGroup X] [Module (ZMod 2) X]

/-- The potential of the cutoff j for the comparison maps of two consecutive degrees: with L the
truncated product, PE_Y and PE_X the truncated images,
(dim L − dim PE_Y) + (dim L − dim PE_X) + (dim Y − dim PE_Y). -/
def gphi (j : ℕ) (eY : ∀ l, Y →ₗ[ZMod 2] G l) (eX : ∀ l, X →ₗ[ZMod 2] G l) : ℤ :=
  potential (finrank (ZMod 2) (LinearMap.range (cut G j)))
    (finrank (ZMod 2) ((LinearMap.range (totMap eY)).map (cut G j)))
    (finrank (ZMod 2) ((LinearMap.range (totMap eX)).map (cut G j)))
    (finrank (ZMod 2) Y)

/-! ### The potential and its terms -/

/-- The potential is nonnegative. -/
theorem gphi_nonneg (hG : FinTot G) [Module.Finite (ZMod 2) Y] (j : ℕ)
    (eY : ∀ l, Y →ₗ[ZMod 2] G l) (eX : ∀ l, X →ₗ[ZMod 2] G l) : 0 ≤ gphi G j eY eX := by
  have : Module.Finite (ZMod 2) ((q : ℕ) → G q) := hG
  have h1 : (LinearMap.range (totMap eY)).map (cut G j) ≤ LinearMap.range (cut G j) := by
    rintro _ ⟨y, _, rfl⟩
    exact ⟨y, rfl⟩
  have h2 : (LinearMap.range (totMap eX)).map (cut G j) ≤ LinearMap.range (cut G j) := by
    rintro _ ⟨y, _, rfl⟩
    exact ⟨y, rfl⟩
  have h3 := Submodule.finrank_mono h1
  have h4 := Submodule.finrank_mono h2
  have h5 : finrank (ZMod 2) ((LinearMap.range (totMap eY)).map (cut G j)) ≤
      finrank (ZMod 2) Y := by
    rw [← LinearMap.range_comp]
    exact LinearMap.finrank_range_le _
  unfold gphi potential
  omega

/-- The dimension missing from the truncated image of the upper degree is at most the
potential. -/
theorem low_defect_le (hG : FinTot G) [Module.Finite (ZMod 2) Y] (j : ℕ)
    (eY : ∀ l, Y →ₗ[ZMod 2] G l) (eX : ∀ l, X →ₗ[ZMod 2] G l) :
    (finrank (ZMod 2) (LinearMap.range (cut G j)) : ℤ) -
        (finrank (ZMod 2) ((LinearMap.range (totMap eY)).map (cut G j)) : ℤ) ≤
      gphi G j eY eX := by
  have : Module.Finite (ZMod 2) ((q : ℕ) → G q) := hG
  have h2 : (LinearMap.range (totMap eX)).map (cut G j) ≤ LinearMap.range (cut G j) := by
    rintro _ ⟨y, _, rfl⟩
    exact ⟨y, rfl⟩
  have h4 := Submodule.finrank_mono h2
  have h5 : finrank (ZMod 2) ((LinearMap.range (totMap eY)).map (cut G j)) ≤
      finrank (ZMod 2) Y := by
    rw [← LinearMap.range_comp]
    exact LinearMap.finrank_range_le _
  unfold gphi potential
  omega

/-- The dimension of the image classes of the upper degree which vanish in the degrees at most
j is at most the potential. -/
theorem high_image_le (hG : FinTot G) [Module.Finite (ZMod 2) Y] (j : ℕ)
    (eY : ∀ l, Y →ₗ[ZMod 2] G l) (eX : ∀ l, X →ₗ[ZMod 2] G l) :
    (finrank (ZMod 2) (LinearMap.range (totMap eY) ⊓ LinearMap.ker (cut G j) :
        Submodule (ZMod 2) ((q : ℕ) → G q)) : ℤ) ≤ gphi G j eY eX := by
  have : Module.Finite (ZMod 2) ((q : ℕ) → G q) := hG
  have h1 : (LinearMap.range (totMap eY)).map (cut G j) ≤ LinearMap.range (cut G j) := by
    rintro _ ⟨y, _, rfl⟩
    exact ⟨y, rfl⟩
  have h2 : (LinearMap.range (totMap eX)).map (cut G j) ≤ LinearMap.range (cut G j) := by
    rintro _ ⟨y, _, rfl⟩
    exact ⟨y, rfl⟩
  have h3 := Submodule.finrank_mono h1
  have h4 := Submodule.finrank_mono h2
  have h5 := finrank_eq_inf_ker_add_map (cut G j) (LinearMap.range (totMap eY))
  have h6 := LinearMap.finrank_range_le (totMap eY)
  unfold gphi potential
  omega

end Defs

section Event

variable {Vg V'g Wg : ℕ → Type}
  [∀ q, AddCommGroup (Vg q)] [∀ q, Module (ZMod 2) (Vg q)]
  [∀ q, AddCommGroup (V'g q)] [∀ q, Module (ZMod 2) (V'g q)]
  [∀ q, AddCommGroup (Wg q)] [∀ q, Module (ZMod 2) (Wg q)]
  {A A' B B' C₀ C₁ C₂ : Type}
  [AddCommGroup A] [Module (ZMod 2) A] [AddCommGroup A'] [Module (ZMod 2) A']
  [AddCommGroup B] [Module (ZMod 2) B] [AddCommGroup B'] [Module (ZMod 2) B']
  [AddCommGroup C₀] [Module (ZMod 2) C₀] [AddCommGroup C₁] [Module (ZMod 2) C₁]
  [AddCommGroup C₂] [Module (ZMod 2) C₂]
  (fR : ∀ l, Wg l →ₗ[ZMod 2] V'g l) (iR : ∀ l, V'g l →ₗ[ZMod 2] Vg l)
  (dR : ∀ l, Vg l →ₗ[ZMod 2] Wg (l + 1))
  (d₀ : B →ₗ[ZMod 2] C₁) (g₁ : C₁ →ₗ[ZMod 2] A') (ρ : A' →ₗ[ZMod 2] A) (d₁ : A →ₗ[ZMod 2] C₂)
  (g₀ : C₀ →ₗ[ZMod 2] B') (ρ₀ : B' →ₗ[ZMod 2] B)
  (eA : ∀ l, A →ₗ[ZMod 2] Vg l) (eA' : ∀ l, A' →ₗ[ZMod 2] V'g l)
  (eB : ∀ l, B →ₗ[ZMod 2] Vg l) (eB' : ∀ l, B' →ₗ[ZMod 2] V'g l)
  (l₀ : ∀ l, C₀ →ₗ[ZMod 2] Wg l) (l₁ : ∀ l, C₁ →ₗ[ZMod 2] Wg l) (l₂ : ∀ l, C₂ →ₗ[ZMod 2] Wg l)

/-- A far cutoff: the potential does not increase. -/
theorem gphi_far (hV : FinTot Vg) (hV' : FinTot V'g) (hW : FinTot Wg)
    [Module.Finite (ZMod 2) A] [Module.Finite (ZMod 2) A'] [Module.Finite (ZMod 2) B]
    [Module.Finite (ZMod 2) C₁]
    (hfi : ∀ l w, iR l (fR l w) = 0) (hfi' : ∀ l y, iR l y = 0 → ∃ w, fR l w = y)
    (hid : ∀ l y, dR l (iR l y) = 0) (hid' : ∀ l x, dR l x = 0 → ∃ y, iR l y = x)
    (hf0 : Function.Injective (fR 0)) (hdf : ∀ l x, fR (l + 1) (dR l x) = 0)
    (hdf' : ∀ l w, fR (l + 1) w = 0 → ∃ x, dR l x = w)
    (hC₁ : LinearMap.ker g₁ = LinearMap.range d₀) (hA' : LinearMap.ker ρ = LinearMap.range g₁)
    (hA : LinearMap.ker d₁ = LinearMap.range ρ) (hB : LinearMap.ker d₀ = LinearMap.range ρ₀)
    (hiA : ∀ l a', iR l (eA' l a') = eA l (ρ a')) (hiB : ∀ l b', iR l (eB' l b') = eB l (ρ₀ b'))
    (hdA : ∀ l a, dR l (eA l a) = l₂ (l + 1) (d₁ a)) (hdA0 : ∀ a, l₂ 0 (d₁ a) = 0)
    (hdB : ∀ l b, dR l (eB l b) = l₁ (l + 1) (d₀ b)) (hdB0 : ∀ b, l₁ 0 (d₀ b) = 0)
    (hgA : ∀ l c, eA' l (g₁ c) = fR l (l₁ l c)) (hgB : ∀ l c, eB' l (g₀ c) = fR l (l₀ l c))
    (j : ℕ) (hd : ∀ x, dR j x = 0)
    (hl₀ : LinearMap.range (cut Wg j) ≤ LinearMap.range (totMap l₀))
    (hl₁ : Function.Injective (totMap l₁))
    (hl₁P : LinearMap.range (totMap l₁) = LinearMap.range (cut Wg j))
    (hl₂ : Function.Injective (totMap l₂))
    (hl₂P : LinearMap.range (totMap l₂) ≤ LinearMap.range (cut Wg j)) :
    gphi V'g j eA' eB' ≤ gphi Vg j eA eB := by
  have : Module.Finite (ZMod 2) ((q : ℕ) → Vg q) := hV
  have : Module.Finite (ZMod 2) ((q : ℕ) → V'g q) := hV'
  have : Module.Finite (ZMod 2) ((q : ℕ) → Wg q) := hW
  have h3A : ∀ a, shiftMap dR (totMap eA a) = totMap l₂ (d₁ a) := by
    intro a
    funext l
    cases l with
    | zero => exact (hdA0 a).symm
    | succ l => exact hdA l a
  have h3B : ∀ b, shiftMap dR (totMap eB b) = totMap l₁ (d₀ b) := by
    intro b
    funext l
    cases l with
    | zero => exact (hdB0 b).symm
    | succ l => exact hdB l b
  exact (far_potential (piMap fR) (piMap iR) (shiftMap dR) (cut Vg j) (cut V'g j) (cut Wg j)
    d₀ g₁ ρ d₁ g₀ ρ₀ (totMap eA) (totMap eA') (totMap eB) (totMap eB') (totMap l₀) (totMap l₁)
    (totMap l₂) (ker_piMap fR iR hfi hfi') (ker_shiftMap iR dR hid hid')
    (ker_piMap_shift dR fR hf0 hdf hdf') (cut_cut j) (cut_cut j) (cut_cut j)
    (piMap_cut fR j) (piMap_cut iR j) (shiftMap_cut dR j hd) hC₁ hA' hA hB
    (fun a' => funext fun l => hiA l a') (fun b' => funext fun l => hiB l b') h3A h3B
    (fun c => funext fun l => hgA l c) (fun c => funext fun l => hgB l c)
    hl₀ hl₁ hl₁P hl₂ hl₂P).2

/-- A general cutoff: the potential changes by at most six times a bound for the dimensions of
the total of W and of the two ambient crossing groups. -/
theorem gphi_near (hV : FinTot Vg) (hV' : FinTot V'g) (hW : FinTot Wg)
    [Module.Finite (ZMod 2) A] [Module.Finite (ZMod 2) A'] [Module.Finite (ZMod 2) B]
    [Module.Finite (ZMod 2) C₁] [Module.Finite (ZMod 2) C₂]
    (hfi : ∀ l w, iR l (fR l w) = 0) (hfi' : ∀ l y, iR l y = 0 → ∃ w, fR l w = y)
    (hid : ∀ l y, dR l (iR l y) = 0) (hid' : ∀ l x, dR l x = 0 → ∃ y, iR l y = x)
    (hA' : LinearMap.ker ρ = LinearMap.range g₁)
    (hA : LinearMap.ker d₁ = LinearMap.range ρ) (hB : LinearMap.ker d₀ = LinearMap.range ρ₀)
    (hiA : ∀ l a', iR l (eA' l a') = eA l (ρ a')) (hiB : ∀ l b', iR l (eB' l b') = eB l (ρ₀ b'))
    (j : ℕ) {M : ℕ} (hWM : totRank Wg ≤ M) (hM₁ : finrank (ZMod 2) C₁ ≤ M)
    (hM₂ : finrank (ZMod 2) C₂ ≤ M) :
    gphi V'g j eA' eB' ≤ gphi Vg j eA eB + 6 * (M : ℤ) ∧
      gphi Vg j eA eB ≤ gphi V'g j eA' eB' + 6 * (M : ℤ) := by
  have : Module.Finite (ZMod 2) ((q : ℕ) → Vg q) := hV
  have : Module.Finite (ZMod 2) ((q : ℕ) → V'g q) := hV'
  have : Module.Finite (ZMod 2) ((q : ℕ) → Wg q) := hW
  exact near_potential (piMap fR) (piMap iR) (shiftMap dR) (cut Vg j) (cut V'g j)
    d₀ g₁ ρ d₁ ρ₀ (totMap eA) (totMap eA') (totMap eB) (totMap eB')
    (ker_piMap fR iR hfi hfi') (ker_shiftMap iR dR hid hid') (cut_cut j) (piMap_cut iR j)
    hA' hA hB (fun a' => funext fun l => hiA l a') (fun b' => funext fun l => hiB l b')
    hWM hM₁ hM₂

end Event

end

end Finsler.GradedLadder
