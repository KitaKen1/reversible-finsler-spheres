module

public import Finsler.Topology.ECupSusp
public import Finsler.Topology.ECupLens
public import Finsler.Geometry.RoundModelLens

/-! The evaluation class along the model of a round crossing.

Let e_V = π^*[Sⁿ] on V₂ (π(x, u) = x) and e_M its pullback to the model space V₂ × Fib by the
projection. The cup with e_V annihilates no nonzero class of H⁰(V₂) if and only if the cup with
e_M annihilates no nonzero class of the lens pair of the model label set 𝒲_ρ in degree
l = (2m − 1)(n − 1): the chain lens pair of 𝒲_ρ → lens pair of the whole model → Thom pair →
negative bundle → (stabilization) trivial bundle → V₂ consists of inclusions inside the model,
the map of the Thom pair to the negative bundle and the stabilization homeomorphism (both over
V₂) and products with Euclidean pairs (`ECupSusp.prod_iff`). -/

@[expose] public section

namespace Finsler.ECupThom

open CategoryTheory SphereOddDegree Finsler.SphereGeometry Finsler.Geometry
open Finsler.RoundChart Finsler.RoundModel Finsler.RoundCone Finsler.RoundThom
open Finsler.RoundModelLens Finsler.ConeLens Finsler.FlowLens Finsler.LensContinuation
open Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop Finsler.PairTriple
open Finsler.PairSuspensionProduct Finsler.ECup Finsler.ECupSusp Finsler.ECupLens
open Set
open scoped Real

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {n : ℕ} {N : ℕ} [NeZero N] {m : ℕ}

/-- The projection V₂ → Sⁿ, (x, u) ↦ x. -/
def piV (n : ℕ) : V2T n ⟶ Finsler.BorelEvaluation.sphere n :=
  TopCat.ofHom ⟨fun z => ⟨z.1.1, mem_sphere_zero_iff_norm.mpr z.2.1⟩,
    (continuous_fst.comp continuous_subtype_val).subtype_mk _⟩

/-- The class π^*[Sⁿ] of V₂. -/
def eV (n : ℕ) (hn : 1 ≤ n) : cohomologyZMod2 (V2T n) n :=
  (cohPullback (piV n) n).hom (Finsler.SphereTopClass.topClass n hn)

/-- The projection of the model space to V₂. -/
def prM (n N m : ℕ) [NeZero N] : MS n N m ⟶ V2T n :=
  TopCat.ofHom ⟨fun w => ⟨w.1.1, w.2⟩, (continuous_fst.comp continuous_subtype_val).subtype_mk _⟩

/-- The projection of the negative bundle to V₂. -/
def baseNB (n N m : ℕ) [NeZero N] : NB n N m ⟶ V2T n :=
  TopCat.ofHom ⟨fun v => ⟨v.1.1.1, v.1.2⟩,
    ((continuous_fst.comp continuous_subtype_val).comp continuous_subtype_val).subtype_mk _⟩

variable (hm : 0 < m) (hmN : 2 * m < N)

theorem bigHomeo_proj :
    TopCat.ofHom (X := Prd (NB n N m) (2 * (2 * m - 1)))
      (Y := Prd (V2T n) ((2 * m - 1) * (n + 1))) ⟨bigHomeo hm hmN, (bigHomeo hm hmN).continuous⟩ ≫
        prdProj (V2T n) ((2 * m - 1) * (n + 1)) =
      prdProj (NB n N m) (2 * (2 * m - 1)) ≫ baseNB n N m := rfl

include hm hmN in
/-- **The stabilized negative bundle and the trivial bundle.** -/
theorem nb_iff (hn : 1 ≤ n) :
    CupInjW (eV n hn) (inter_subset_left : (univ : Set (V2T n)) ∩ ∅ ⊆ univ) 0 ↔
      CupInjW ((cohPullback (baseNB n N m) n).hom (eV n hn))
        (inter_subset_left : (univ : Set (NB n N m)) ∩ nbO ⊆ univ) ((2 * m - 1) * (n - 1)) := by
  have hL : (2 * m - 1) * (n - 1) + 2 * (2 * m - 1) = 0 + (2 * m - 1) * (n + 1) := by
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  rw [prod_iff (eV n hn) (univ : Set (V2T n)) isOpen_empty ((2 * m - 1) * (n + 1)) 0,
    prod_iff _ (univ : Set (NB n N m)) nbO_isOpen (2 * (2 * m - 1)) ((2 * m - 1) * (n - 1)), hL,
    ← Finsler.Cup.pullback_comp, ← bigHomeo_proj hm hmN, Finsler.Cup.pullback_comp]
  exact cupInjW_over (TopCat.ofHom ⟨bigHomeo hm hmN, (bigHomeo hm hmN).continuous⟩) _ _ rfl
    (bijective_Hmap_of_homeomorph _ _ (bigHomeo hm hmN)
      (fun _ => ⟨fun _ => mem_univ _, fun _ => mem_univ _⟩) (bigHomeo_mem hm hmN) _)
    (bijective_Hmap_of_homeomorph _ _ (bigHomeo hm hmN)
      (fun _ => ⟨fun _ => mem_univ _, fun _ => mem_univ _⟩) (bigHomeo_mem hm hmN) _)

variable {a c T : ℝ} (ha : a ≤ (2 * π * m) ^ 2) (hc : (2 * π * m) ^ 2 < c)

include ha hc in
/-- **The Thom pair of the model and the negative bundle.** -/
theorem thom_iff (hn : 1 ≤ n) (q : ℕ) :
    CupInjW ((cohPullback (baseNB n N m) n).hom (eV n hn))
        (inter_subset_left : (univ : Set (NB n N m)) ∩ nbO ⊆ univ) q ↔
      CupInjW ((cohPullback (prM n N m) n).hom (eV n hn))
        (setSx_sub_setTb (cone hm hmN) (descentM hm hmN) (univ : Set (MS n N m)) a c T) q :=
  cupInjW_common (prM n N m) (baseNB n N m) (eV n hn) _ rfl
    (thom_nb_bijective hm hmN ha hc q) (thom_nb_bijective hm hmN ha hc (n + q))

variable (hT : 0 ≤ T)

include ha hc hT in
/-- **The lens pair of the whole model and its Thom pair.** -/
theorem lens_iff (hn : 1 ≤ n) (q : ℕ) :
    CupInjW ((cohPullback (prM n N m) n).hom (eV n hn))
        (setY_sub_setU (cone hm hmN) (descentM hm hmN) (univ : Set (MS n N m)) a c T) q ↔
      CupInjW ((cohPullback (prM n N m) n).hom (eV n hn))
        (setSx_sub_setTb (cone hm hmN) (descentM hm hmN) (univ : Set (MS n N m)) a c T) q :=
  cone_iff _ (split hm hmN) isOpen_univ (fun _ _ _ _ _ _ => mem_univ _)
    (fun _ _ _ _ _ _ _ => mem_univ _) (s₀ := 0) (fun _ _ _ _ _ => hc) hT le_rfl q

include ha hc in
/-- **The model**: the cup with π^*[Sⁿ] is injective on H⁰(V₂) if and only if the cup with its
pullback is injective on the lens pair of the label set 𝒲_ρ in the degree of the index. -/
theorem model_iff (hn : 1 ≤ n) {a' ρ : ℝ} (ha'a : a' < a) (ha' : a' ≤ (2 * π * m) ^ 2)
    (hT1 : 1 ≤ T) (hρ : 4 * (c - a') < ρ ^ 2) :
    CupInjW (eV n hn) (inter_subset_left : (univ : Set (V2T n)) ∩ ∅ ⊆ univ) 0 ↔
      CupInjW ((cohPullback (prM n N m) n).hom (eV n hn))
        (partY_sub_partU (cone hm hmN).energy (descentM hm hmN)
          (labelM (n := n) (N := N) (m := m) ρ) a c T) ((2 * m - 1) * (n - 1)) := by
  rw [nb_iff hm hmN hn, thom_iff hm hmN ha hc hn, ← lens_iff hm hmN ha hc (zero_le_one.trans hT1) hn]
  exact (core_iff _ (descentM hm hmN) (energy_continuous (cone hm hmN)) ha'a
    (fun w hw hw' => ⟨fun _ => mem_univ _, fun _ => core_mem hm hmN hc.le ha' hT1 hρ w hw hw'⟩)
    _).symm

end

end Finsler.ECupThom
