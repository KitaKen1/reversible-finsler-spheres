module

public import Finsler.Topology.ConeLens
public import Finsler.Topology.PairSuspensionProduct
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-! The normal shift for a product model. Let ψ be a descent for a function h on a space B. On
the product of B with a Euclidean space of dimension k and a normed space V consider the
function h(z) − |u|² + |y|² and the flow (ψ_t z, e^t u, e^{-t} y): this is a split descent for a
cone structure. For cuts a, b and a time T > 0 put ε = (b − a) / (e^{2T} − 1). A point below b
which the product flow does not take below a in time T has base point below b + ε which ψ does
not take below a − ε in time T. Hence, if W is an open set of B in which the points below b + ε
not taken below a − ε stay as long as they are not taken below a − ε, and if ψ takes the points
of W below b + ε below b in some time s₀, the hypotheses of the lens theorem for cone
structures hold over W, and the pair it gives is the product of the lens pair of h in W with
the pair of the Euclidean space and its nonzero vectors. Therefore the lens pair of the
product over W has the cohomology of the lens pair of h in W shifted by k: the same dimension
in degree n + k as the latter in degree n, and no cohomology below degree k. -/

@[expose] public section

namespace Finsler.ProductModel

open CategoryTheory Set Topology Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop
open Finsler.PairTriple Finsler.FlowLens Finsler.ConeLens Finsler.PairSuspension
open Finsler.PairSuspensionProduct

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {B : TopCat.{0}} {h : B → ℝ} (k : ℕ) (V : Type) [NormedAddCommGroup V]
  [NormedSpace ℝ V]

/-- The product of the base with the negative and the positive fibre. -/
abbrev Model (B : TopCat.{0}) (k : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    TopCat.{0} :=
  TopCat.of (B × EuclideanSpace ℝ (Fin k) × V)

/-- The cone structure of the product. -/
def cone (hh : Continuous h) : Cone (Model B k V) where
  sc l m w := (w.1, l • w.2.1, m • w.2.2)
  cont := (continuous_fst.comp continuous_snd).prodMk
    (((continuous_fst.comp continuous_fst).smul
      (continuous_fst.comp (continuous_snd.comp continuous_snd))).prodMk
      ((continuous_snd.comp continuous_fst).smul
        (continuous_snd.comp (continuous_snd.comp continuous_snd))))
  one w := by
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · exact one_smul ℝ w.2.1
    · exact one_smul ℝ w.2.2
  nn w := ‖w.2.1‖
  np w := ‖w.2.2‖
  base w := h w.1
  nn_cont := continuous_norm.comp (continuous_fst.comp continuous_snd)
  np_cont := continuous_norm.comp (continuous_snd.comp continuous_snd)
  base_cont := hh.comp continuous_fst
  nn_nonneg _ := norm_nonneg _
  np_nonneg _ := norm_nonneg _
  nn_sc l _ w hl _ := by
    change ‖l • w.2.1‖ = l * ‖w.2.1‖
    rw [norm_smul, Real.norm_of_nonneg hl]
  np_sc _ m w _ hm := by
    change ‖m • w.2.2‖ = m * ‖w.2.2‖
    rw [norm_smul, Real.norm_of_nonneg hm]
  base_sc _ _ _ _ _ := rfl
  nn_zero w hw := by
    have h0 : w.2.1 = 0 := norm_eq_zero.mp hw
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · change (0 : ℝ) • w.2.1 = w.2.1
      rw [zero_smul, h0]
    · exact one_smul ℝ w.2.2

theorem cone_energy (hh : Continuous h) (w : Model B k V) :
    (cone k V hh).energy w = h w.1 - ‖w.2.1‖ ^ 2 + ‖w.2.2‖ ^ 2 := rfl

variable (ψ : Descent B h)

/-- The product flow. -/
def descent (hh : Continuous h) : Descent (Model B k V) (cone k V hh).energy where
  flow t w := (ψ.flow t w.1, Real.exp t • w.2.1, Real.exp (-t) • w.2.2)
  cont := (ψ.cont.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk
    (((Real.continuous_exp.comp continuous_fst).smul
      (continuous_fst.comp (continuous_snd.comp continuous_snd))).prodMk
      ((Real.continuous_exp.comp continuous_fst.neg).smul
        (continuous_snd.comp (continuous_snd.comp continuous_snd))))
  zero w := by
    refine Prod.ext (ψ.zero w.1) (Prod.ext ?_ ?_)
    · change Real.exp 0 • w.2.1 = w.2.1
      rw [Real.exp_zero, one_smul]
    · change Real.exp (-0) • w.2.2 = w.2.2
      rw [neg_zero, Real.exp_zero, one_smul]
  add s t w hs ht := by
    refine Prod.ext (ψ.add s t w.1 hs ht) (Prod.ext ?_ ?_)
    · change Real.exp (s + t) • w.2.1 = Real.exp s • Real.exp t • w.2.1
      rw [smul_smul, Real.exp_add]
    · change Real.exp (-(s + t)) • w.2.2 = Real.exp (-s) • Real.exp (-t) • w.2.2
      rw [smul_smul, ← Real.exp_add, neg_add]
  mono t w ht := by
    change h (ψ.flow t w.1) - ‖Real.exp t • w.2.1‖ ^ 2 + ‖Real.exp (-t) • w.2.2‖ ^ 2 ≤
      h w.1 - ‖w.2.1‖ ^ 2 + ‖w.2.2‖ ^ 2
    rw [norm_smul, norm_smul, Real.norm_of_nonneg (Real.exp_pos t).le,
      Real.norm_of_nonneg (Real.exp_pos (-t)).le]
    have h1 := ψ.mono t w.1 ht
    have h2 : ‖w.2.1‖ ^ 2 ≤ (Real.exp t * ‖w.2.1‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _)
        (le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_exp ht)) 2
    have h3 : (Real.exp (-t) * ‖w.2.2‖) ^ 2 ≤ ‖w.2.2‖ ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
        (mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht))) 2
    linarith

theorem descent_flow (hh : Continuous h) (t : ℝ) (w : Model B k V) :
    (descent k V ψ hh).flow t w = (ψ.flow t w.1, Real.exp t • w.2.1, Real.exp (-t) • w.2.2) :=
  rfl

/-- The product flow is a split descent. -/
theorem split (hh : Continuous h) : Split (cone k V hh) (descent k V ψ hh) where
  comm t l m w _ _ _ := by
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · change Real.exp t • l • w.2.1 = l • Real.exp t • w.2.1
      rw [smul_comm]
    · change Real.exp (-t) • m • w.2.2 = m • Real.exp (-t) • w.2.2
      rw [smul_comm]
  nn_flow t w ht := by
    change ‖w.2.1‖ ≤ ‖Real.exp t • w.2.1‖
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos t).le]
    exact le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_exp ht)
  np_flow t w ht := by
    change ‖Real.exp (-t) • w.2.2‖ ≤ ‖w.2.2‖
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos (-t)).le]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht))
  base_flow t w ht := ψ.mono t w.1 ht

/-- The energy of the product after the time T. -/
theorem energy_flow (hh : Continuous h) (T : ℝ) (w : Model B k V) :
    (cone k V hh).energy ((descent k V ψ hh).flow T w) =
      h (ψ.flow T w.1) - Real.exp (2 * T) * ‖w.2.1‖ ^ 2 + ‖w.2.2‖ ^ 2 / Real.exp (2 * T) := by
  change h (ψ.flow T w.1) - ‖Real.exp T • w.2.1‖ ^ 2 + ‖Real.exp (-T) • w.2.2‖ ^ 2 = _
  rw [norm_smul, norm_smul, Real.norm_of_nonneg (Real.exp_pos T).le,
    Real.norm_of_nonneg (Real.exp_pos (-T)).le, mul_pow, mul_pow, ← Real.exp_nat_mul,
    ← Real.exp_nat_mul]
  have h1 : Real.exp (((2 : ℕ) : ℝ) * -T) = (Real.exp (2 * T))⁻¹ := by
    rw [← Real.exp_neg]
    congr 1
    push_cast
    ring
  rw [h1]
  push_cast
  ring

/-- The estimates for a point below b which is not taken below a in time T: with
E = e^{2T}, X = |u|² and E z = |y|². -/
theorem estimates {E X z hb hT a b : ℝ} (hE : 1 < E) (hX : 0 ≤ X) (hz : 0 ≤ z)
    (hmono : hT ≤ hb) (h1 : hb - X + z * E < b) (h2 : a ≤ hT - E * X + z) :
    (hb - b) * (E - 1) < b - a ∧ (a - hT) * (E - 1) < b - a := by
  have hE0 : 0 < E := zero_lt_one.trans hE
  have s1 : E * (hb + z * E - b) < E * X := mul_lt_mul_of_pos_left (by linarith) hE0
  have s2 : 0 ≤ z * (E ^ 2 - 1) := mul_nonneg hz (by nlinarith)
  have s3 : 0 ≤ E * X := mul_nonneg hE0.le hX
  have s4 : a - hT ≤ z := by linarith
  constructor
  · nlinarith
  · have s5 : z * (E - 1) < b - a := by
      have s6 : (E - 1) * (a - z) ≤ (E - 1) * hb :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      nlinarith
    have s7 : (a - hT) * (E - 1) ≤ z * (E - 1) :=
      mul_le_mul_of_nonneg_right s4 (by linarith)
    linarith

variable {k V ψ}

/-- A point below b which the product flow does not take below a in time T has base point
below b + ε which ψ does not take below a − ε in time T, ε = (b − a) / (e^{2T} − 1). -/
theorem base_estimates (hh : Continuous h) {a b T : ℝ} (hT : 0 < T) {w : Model B k V}
    (hw : (cone k V hh).energy w < b)
    (hw' : a ≤ (cone k V hh).energy ((descent k V ψ hh).flow T w)) :
    h w.1 < b + (b - a) / (Real.exp (2 * T) - 1) ∧
      a - (b - a) / (Real.exp (2 * T) - 1) ≤ h (ψ.flow T w.1) := by
  have hE : 1 < Real.exp (2 * T) := Real.one_lt_exp_iff.mpr (by linarith)
  have hE1 : 0 < Real.exp (2 * T) - 1 := by linarith
  rw [energy_flow] at hw'
  rw [cone_energy] at hw
  have hz : ‖w.2.2‖ ^ 2 / Real.exp (2 * T) * Real.exp (2 * T) = ‖w.2.2‖ ^ 2 :=
    div_mul_cancel₀ _ (ne_of_gt (zero_lt_one.trans hE))
  obtain ⟨e1, e2⟩ := estimates (X := ‖w.2.1‖ ^ 2) (z := ‖w.2.2‖ ^ 2 / Real.exp (2 * T)) hE
    (sq_nonneg _) (div_nonneg (sq_nonneg _) (zero_lt_one.trans hE).le)
    (ψ.mono T w.1 hT.le) (by rw [hz]; exact hw) hw'
  constructor
  · have := (lt_div_iff₀ hE1).mpr e1
    linarith
  · have := (lt_div_iff₀ hE1).mpr e2
    linarith

variable (k V ψ) (WB : Set B) (a b T : ℝ)

/-- The points of the product over W. -/
def over : Set (Model B k V) := {w | w.1 ∈ WB}

/-- The part of the sublevel of b of h in W. -/
def baseP (h : B → ℝ) (WB : Set B) (b : ℝ) : Set B := {z | h z < b ∧ z ∈ WB}

/-- The points which ψ takes below a in time T. -/
def baseO : Set B := {z | h (ψ.flow T z) < a}

theorem baseO_isOpen (hh : Continuous h) : IsOpen (baseO ψ a T) :=
  isOpen_lt (hh.comp (flow_continuous ψ T)) continuous_const

variable {k V ψ WB a b T}

theorem over_isOpen (hW : IsOpen WB) : IsOpen (over k V WB) := hW.preimage continuous_fst

/-- The projection of the points with vanishing positive part onto the product of the base
with ℝ^k. -/
def tbMap (hh : Continuous h) :
    C(setTb (cone k V hh) (over k V WB) b, prodCyl (baseP h WB b) k) :=
  ⟨fun w => ⟨((w : Model B k V).1, EuclideanSpace.equiv (Fin k) ℝ (w : Model B k V).2.1),
      ⟨w.2.2.1, w.2.2.2⟩⟩,
    ((continuous_fst.comp continuous_subtype_val).prodMk
      ((EuclideanSpace.equiv (Fin k) ℝ).continuous.comp
        (continuous_fst.comp (continuous_snd.comp continuous_subtype_val)))).subtype_mk _⟩

/-- The inclusion of the product of the base with ℝ^k as the points with vanishing positive
part. -/
def tbInv (hh : Continuous h) :
    C(prodCyl (baseP h WB b) k, setTb (cone k V hh) (over k V WB) b) :=
  ⟨fun p => ⟨((p : Prd B k).1, (EuclideanSpace.equiv (Fin k) ℝ).symm (p : Prd B k).2, (0 : V)),
      ⟨norm_zero, p.2.1, p.2.2⟩⟩,
    ((continuous_fst.comp continuous_subtype_val).prodMk
      (((EuclideanSpace.equiv (Fin k) ℝ).symm.continuous.comp
        (continuous_snd.comp continuous_subtype_val)).prodMk continuous_const)).subtype_mk _⟩

/-- The pair given by the lens theorem for cone structures is the product of the lens pair of
the base in W with the pair of ℝ^k and its nonzero vectors. -/
theorem tb_bijective (hh : Continuous h) (n : ℕ) :
    Function.Bijective (Hmap (trivHom (pairMapX
      (setSx_sub_setTb (cone k V hh) (descent k V ψ hh) (over k V WB) a b T)
      (inter_subset_left : prodCyl (baseP h WB b) k ∩ prodOpen (baseO ψ a T) k ⊆
        prodCyl (baseP h WB b) k)
      (tbMap hh) (fun w hw => ⟨⟨hw.2.1, hw.2.2.1⟩, by
        rcases hw.2.2.2 with h' | h'
        · left
          intro h0
          apply h'
          have h1 : (w : Model B k V).2.1 = 0 :=
            (EuclideanSpace.equiv (Fin k) ℝ).map_eq_zero_iff.mp h0
          change ‖(w : Model B k V).2.1‖ = 0
          rw [h1, norm_zero]
        · exact Or.inr h'⟩))) n) := by
  refine bijective_Hmap_of_section _ _ (tbMap hh) (tbInv hh) _ ?_ ?_
    { toFun := fun q => q.2
      continuous_toFun := continuous_snd
      map_zero_left := fun w => ?_
      map_one_left := fun _ => rfl } (fun _ _ hw => hw) n
  · intro p hp
    refine ⟨norm_zero, hp.1.1, hp.1.2, ?_⟩
    rcases hp.2 with h' | h'
    · left
      intro h0
      apply h'
      have h1 : (EuclideanSpace.equiv (Fin k) ℝ).symm (p : Prd B k).2 = 0 := norm_eq_zero.mp h0
      exact (EuclideanSpace.equiv (Fin k) ℝ).symm.map_eq_zero_iff.mp h1
    · exact Or.inr h'
  · refine ContinuousMap.ext fun p => Subtype.ext (Prod.ext rfl ?_)
    exact (EuclideanSpace.equiv (Fin k) ℝ).apply_symm_apply _
  · apply Subtype.ext
    have h0 : (w : Model B k V).2.2 = 0 := norm_eq_zero.mp w.2.1
    refine Prod.ext rfl (Prod.ext ?_ h0)
    exact ((EuclideanSpace.equiv (Fin k) ℝ).symm_apply_apply _).symm

section Main

variable (hh : Continuous h) (hW : IsOpen WB) (hT : 0 < T) {s₀ : ℝ} (hs₀ : 0 ≤ s₀)
  (htrap : ∀ z, z ∈ WB → h z < b + (b - a) / (Real.exp (2 * T) - 1) →
    a - (b - a) / (Real.exp (2 * T) - 1) ≤ h (ψ.flow T z) → ∀ s, 0 ≤ s →
    a - (b - a) / (Real.exp (2 * T) - 1) ≤ h (ψ.flow T (ψ.flow s z)) → ψ.flow s z ∈ WB)
  (hpush : ∀ z, z ∈ WB → h z < b + (b - a) / (Real.exp (2 * T) - 1) → h (ψ.flow s₀ z) < b)

include hT htrap in
theorem model_trap (w : Model B k V) (hw : w ∈ over k V WB)
    (hE : (cone k V hh).energy w < b)
    (hE' : a ≤ (cone k V hh).energy ((descent k V ψ hh).flow T w)) (s : ℝ) (hs : 0 ≤ s)
    (hs' : a ≤ (cone k V hh).energy
      ((descent k V ψ hh).flow T ((descent k V ψ hh).flow s w))) :
    (descent k V ψ hh).flow s w ∈ over k V WB := by
  obtain ⟨e1, e2⟩ := base_estimates hh hT hE hE'
  obtain ⟨-, e4⟩ := base_estimates hh hT
    (lt_of_le_of_lt ((descent k V ψ hh).mono s w hs) hE) hs'
  exact htrap w.1 hw e1 e2 s hs e4

include hT hpush in
theorem model_push (w : Model B k V) (hw : w ∈ over k V WB)
    (hE : (cone k V hh).energy w < b)
    (hE' : a ≤ (cone k V hh).energy ((descent k V ψ hh).flow T w)) :
    (cone k V hh).base ((descent k V ψ hh).flow s₀ w) < b :=
  hpush w.1 hw (base_estimates hh hT hE hE').1

/-- The normal shift: the cohomology of the lens pair of h in W in degree n is the cohomology
of the lens pair of the product over W in degree n + k. -/
def modelEquiv (n : ℕ) :
    H (triv (pairOf (inter_subset_left : baseP h WB b ∩ baseO ψ a T ⊆ baseP h WB b))) n ≃ₗ[ZMod 2]
      H (triv (pairOf (setY_sub_setU (cone k V hh) (descent k V ψ hh) (over k V WB) a b T)))
        (n + k) :=
  ((prodEquiv (baseP h WB b) (baseO_isOpen ψ a T hh) k n).trans
    (LinearEquiv.ofBijective _ (tb_bijective (ψ := ψ) (a := a) (T := T) hh (n + k)))).trans
    (coneEquiv (split k V ψ hh) (over_isOpen hW)
      (fun _ _ _ _ _ hw => hw) (model_trap hh hT htrap)
      (fun w hw _ hE hE' => model_push hh hT hpush w hw hE hE') hT.le hs₀ (n + k)).symm

include hW hT hs₀ htrap hpush in
/-- The lens pair of the product over W has in degree n + k the dimension of the cohomology of
the lens pair of h in W in degree n. -/
theorem finrank_model (n : ℕ) :
    Module.finrank (ZMod 2)
        (H (triv (pairOf (setY_sub_setU (cone k V hh) (descent k V ψ hh) (over k V WB)
          a b T))) (n + k)) =
      Module.finrank (ZMod 2)
        (H (triv (pairOf (inter_subset_left : baseP h WB b ∩ baseO ψ a T ⊆ baseP h WB b))) n) :=
  (modelEquiv hh hW hT hs₀ htrap hpush n).finrank_eq.symm

include hW hT hs₀ htrap hpush in
/-- The lens pair of the product over W has no cohomology in the degrees below k. -/
theorem model_eq_zero (n : ℕ) (hn : n < k)
    (z : H (triv (pairOf (setY_sub_setU (cone k V hh) (descent k V ψ hh) (over k V WB)
      a b T))) n) : z = 0 := by
  let e := coneEquiv (split k V ψ hh) (over_isOpen hW)
    (fun _ _ _ _ _ hw => hw) (model_trap hh hT htrap)
    (fun w hw _ hE hE' => model_push hh hT hpush w hw hE hE') hT.le hs₀ n
  have h0 : e z = 0 := by
    obtain ⟨y, hy⟩ := (tb_bijective (ψ := ψ) (a := a) (T := T) hh n).2 (e z)
    rw [← hy, prod_eq_zero (baseP h WB b) (baseO_isOpen ψ a T hh) k n hn y, map_zero]
  calc z = e.symm (e z) := (e.symm_apply_apply z).symm
    _ = e.symm 0 := by rw [h0]
    _ = 0 := e.symm.map_zero

end Main

end

end Finsler.ProductModel
