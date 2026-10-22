module

public import Finsler.Geometry.ECupThom
public import Finsler.Geometry.RoundTransport

/-! The evaluation class along the transport of the lens pairs of the regular m-gons.

On the ambient polygons let e_Om be the pullback of [Sⁿ] by the evaluation at the vertex 0
(normalized). Along the homeomorphism of the ambient label set with the model label set the
classes e_Om and e_M (the pullback of π^*[Sⁿ] by the projection of the model to V₂) correspond:
the normalized vertex 0 of the chart of (z, sξ), s ∈ [0, 1], is a homotopy from the first vector
of z to the normalized vertex 0 of the polygon (the scaled points stay in the label set, whose
charts have nonzero vertices). Hence, for the lens pairs of the transport (`crossing_lens`), the
cup with e_Om is injective on the lens pair of the ambient label set in the degree of the index
as soon as the cup with π^*[Sⁿ] is injective on H⁰(V₂) (`ECupThom.model_iff`). -/

@[expose] public section

namespace Finsler.ECupTransport

open CategoryTheory SphereOddDegree Finsler.SphereGeometry Finsler.Geometry
open Finsler.RoundPolygon Finsler.RoundCoords Finsler.AmbientPenalty Finsler.RoundChart
open Finsler.RoundLabel Finsler.RoundModel Finsler.RoundCone Finsler.RoundThom
open Finsler.RoundModelLens Finsler.RoundTransport Finsler.ConeLens Finsler.FlowLens
open Finsler.LensContinuation Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop
open Finsler.PairTriple Finsler.AmbientDescent Finsler.ECup Finsler.ECupThom
open Set
open scoped Real NNReal

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {n : ℕ} {N : ℕ} [NeZero N] {m : ℕ}

/-- The normalized vertex 0 of the ambient polygons. -/
def evOm (n N : ℕ) [NeZero N] : Om n N ⟶ Finsler.BorelEvaluation.sphere n :=
  TopCat.ofHom ⟨fun Q => Finsler.SphereRetraction.normalize (Q.1 0),
    continuous_iff_continuousAt.mpr fun Q =>
      ContinuousAt.comp (g := Finsler.SphereRetraction.normalize)
        (Finsler.SphereRetraction.normalize_smoothAt (Q.2 0)).continuousAt
        ((continuous_apply 0).comp continuous_subtype_val).continuousAt⟩

/-- The evaluation class of the ambient polygons. -/
def eOm (n N : ℕ) [NeZero N] (hn : 1 ≤ n) : cohomologyZMod2 (Om n N) n :=
  (cohPullback (evOm n N) n).hom (Finsler.SphereTopClass.topClass n hn)

theorem pullback_comp4 {X Y Z U V : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ U) (k : U ⟶ V)
    (q : ℕ) (a : cohomologyZMod2 V q) :
    (cohPullback (f ≫ g ≫ h ≫ k) q).hom a =
      (cohPullback f q).hom ((cohPullback g q).hom ((cohPullback h q).hom
        ((cohPullback k q).hom a))) := by
  rw [Finsler.Cup.pullback_comp, Finsler.Cup.pullback_comp, Finsler.Cup.pullback_comp]

theorem regular_zero_index (x u : Ambient n) : regular N m x u 0 = x := by
  rw [regular, ZMod.val_zero, Nat.cast_zero, mul_zero, circ, Real.cos_zero, Real.sin_zero,
    one_smul, zero_smul, add_zero]

variable (hm : 0 < m) (hmN : 2 * m < N)

theorem scM_mem {ρ : ℝ} (x : labelM (n := n) (N := N) (m := m) ρ) (s : unitInterval) :
    scM hm hmN s s (x : MS n N m) ∈ labelM (n := n) (N := N) (m := m) ρ := by
  have hs2 : (s : ℝ) ^ 2 ≤ 1 := by
    have h0 := s.property.1
    have h1 := s.property.2
    nlinarith
  have hN := sqN_scale hm hmN (x : MS n N m).2 (x : MS n N m).1.2 (l := (s : ℝ)) (s : ℝ)
  have hP := sqP_scale hm hmN (x : MS n N m).2 (x : MS n N m).1.2 (s : ℝ) (s : ℝ)
  have hN0 := sqN_nonneg (x : MS n N m).1
  have hP0 := sqP_nonneg (x : MS n N m).1
  refine ⟨?_, ?_⟩
  · change sqN ((x : MS n N m).1.1, (s : ℝ) • negF hm hmN (x : MS n N m).1 +
      (s : ℝ) • posF hm hmN (x : MS n N m).1) < ρ ^ 2
    rw [hN]
    exact lt_of_le_of_lt (mul_le_of_le_one_left hN0 hs2) x.2.1
  · change sqP ((x : MS n N m).1.1, (s : ℝ) • negF hm hmN (x : MS n N m).1 +
      (s : ℝ) • posF hm hmN (x : MS n N m).1) < ρ ^ 2
    rw [hP]
    exact lt_of_le_of_lt (mul_le_of_le_one_left hP0 hs2) x.2.2

theorem chart_scM_ne {ρ : ℝ} (hρ : Small n N m ρ) (x : labelM (n := n) (N := N) (m := m) ρ)
    (s : unitInterval) : chart m (scM hm hmN s s (x : MS n N m)).1 0 ≠ 0 :=
  hρ.2.2 _ (scM hm hmN s s (x : MS n N m)).2 (scM_mem hm hmN x s).1 (scM_mem hm hmN x s).2 0

section Part

variable {ρ : ℝ} (hρ : Small n N m ρ) {g₁ : Om n N → ℝ}
  (hgv : ∀ w : labO (n := n) (N := N) hm hmN ρ,
    (cone hm hmN).energy (homeo hm hmN hρ w : MS n N m) = g₁ w) (c : ℝ)

/-- The scaling homotopy on the part of the ambient label set below c. -/
def partHom : TopCat.Homotopy
    (TopCat.ofHom (Finsler.LensTransport.partMap (homeo hm hmN hρ) hgv c) ≫
      incl (partU (cone hm hmN).energy (labelM (n := n) (N := N) (m := m) ρ) c) ≫
        prM n N m ≫ piV n)
    (incl (partU g₁ (labO hm hmN ρ) c) ≫ evOm n N) where
  toFun p := Finsler.SphereRetraction.normalize
    (chart m (scM hm hmN p.1 p.1 (homeo hm hmN hρ ⟨p.2.1, p.2.2.2⟩ : MS n N m)).1 0)
  continuous_toFun := by
    have hx : Continuous fun p : unitInterval × ↥(partU g₁ (labO hm hmN ρ) c) =>
        homeo hm hmN hρ ⟨p.2.1, p.2.2.2⟩ :=
      (homeo hm hmN hρ).continuous.comp ((continuous_subtype_val.comp continuous_snd).subtype_mk _)
    have hs : Continuous fun p : unitInterval × ↥(partU g₁ (labO hm hmN ρ) c) => (p.1 : ℝ) :=
      continuous_subtype_val.comp continuous_fst
    have hsc : Continuous fun p : unitInterval × ↥(partU g₁ (labO hm hmN ρ) c) =>
        scM hm hmN p.1 p.1 (homeo hm hmN hρ ⟨p.2.1, p.2.2.2⟩ : MS n N m) :=
      (scM_continuous hm hmN).comp ((hs.prodMk hs).prodMk (continuous_subtype_val.comp hx))
    have hv : Continuous fun p : unitInterval × ↥(partU g₁ (labO hm hmN ρ) c) =>
        chart m (scM hm hmN p.1 p.1 (homeo hm hmN hρ ⟨p.2.1, p.2.2.2⟩ : MS n N m)).1 0 :=
      (continuous_apply 0).comp ((chart_contDiff (n := n) (N := N) m).continuous.comp
        (continuous_subtype_val.comp hsc))
    refine continuous_iff_continuousAt.mpr fun p => ?_
    exact ContinuousAt.comp (g := Finsler.SphereRetraction.normalize)
      (Finsler.SphereRetraction.normalize_smoothAt
        (chart_scM_ne hm hmN hρ (homeo hm hmN hρ ⟨p.2.1, p.2.2.2⟩) p.1)).continuousAt hv.continuousAt
  map_zero_left w := by
    have h0 : (scM hm hmN ((0 : unitInterval) : ℝ) ((0 : unitInterval) : ℝ)
        (homeo hm hmN hρ ⟨w.1, w.2.2⟩ : MS n N m)).1 =
          (((homeo hm hmN hρ ⟨w.1, w.2.2⟩ : MS n N m) :
            (Ambient n × Ambient n) × Fib n N m).1, 0) := by
      change (_, ((0 : unitInterval) : ℝ) • _ + ((0 : unitInterval) : ℝ) • _) = _
      rw [show ((0 : unitInterval) : ℝ) = 0 from rfl, zero_smul, zero_smul, add_zero]
    change Finsler.SphereRetraction.normalize (chart m (scM hm hmN ((0 : unitInterval) : ℝ)
      ((0 : unitInterval) : ℝ) (homeo hm hmN hρ ⟨w.1, w.2.2⟩ : MS n N m)).1 0) = _
    rw [h0, chart_zero, regular_zero_index]
    exact Finsler.SphereRetraction.normalize_inclusion
      (⟨_, mem_sphere_zero_iff_norm.mpr (homeo hm hmN hρ ⟨w.1, w.2.2⟩ : MS n N m).2.1⟩ : Sphere n)
  map_one_left w := by
    change Finsler.SphereRetraction.normalize (chart m (scM hm hmN ((1 : unitInterval) : ℝ)
      ((1 : unitInterval) : ℝ) (homeo hm hmN hρ ⟨w.1, w.2.2⟩ : MS n N m)).1 0) =
        Finsler.SphereRetraction.normalize ((w : Om n N).1 0)
    rw [show ((1 : unitInterval) : ℝ) = 1 from rfl, scM_one, homeo_apply,
      chart_unchart hm hmN w.2.2.1]

/-- **The evaluation classes correspond on the lens parts.** -/
theorem part_class (hn : 1 ≤ n) :
    (cohPullback (TopCat.ofHom (Finsler.LensTransport.partMap (homeo hm hmN hρ) hgv c)) n).hom
        (res ((cohPullback (prM n N m) n).hom (eV n hn))
          (partU (cone hm hmN).energy (labelM (n := n) (N := N) (m := m) ρ) c)) =
      res (eOm n N hn) (partU g₁ (labO hm hmN ρ) c) := by
  unfold res eV eOm
  exact (pullback_comp4 _ _ _ _ n _).symm.trans
    ((Finsler.DiagonalCohomology.homotopy_pullback (partHom hm hmN hρ hgv c) n _).trans
      (Finsler.Cup.pullback_comp _ _ n _))


end Part

/-! ### The lens pair of the ambient label set -/

section Crossing

variable {V : (ZMod N → Ambient n) → ZMod N → Ambient n} {KL : ℝ≥0} (hL : LipschitzWith KL V)
  (hV0 : ∀ P : ZMod N → Ambient n, V P ≠ 0 → ∀ j, P j ≠ 0)
  {g : (ZMod N → Ambient n) → ℝ} {O : Set (ZMod N → Ambient n)}
  (hg : ∀ P ∈ O, DifferentiableAt ℝ g P) (hsupp : ∀ P, V P ≠ 0 → P ∈ O)
  (hle : ∀ P ∈ O, fderiv ℝ g P (V P) ≤ 0)

/-- **The evaluation class on the lens pair of the ambient label set at the m-gons.** -/
theorem crossing_lens_cup (hn : 1 ≤ n) {ρ ρ' : ℝ} (hρ : Small n N m ρ) (hρ'0 : 0 < ρ')
    (hρρ' : Real.exp 1 * ρ' ≤ ρ)
    (hVW : ∀ Q ∈ labA hm hmN ρ, V Q = fieldW hm hmN Q)
    (hgM : ∀ Q ∈ labA hm hmN ρ, g Q = model m (unchart hm hmN Q))
    {a₀a b₀a : ℝ} (ha₀ : a₀a < (2 * π * m) ^ 2) (hb₀ : (2 * π * m) ^ 2 < b₀a)
    (hgc : Continuous (fun Q : Om n N => g Q.1))
    (hK : IsCompact {Q : Om n N | a₀a ≤ g Q.1 ∧ g Q.1 ≤ b₀a})
    {R : Set (Om n N)} (hR : IsOpen R) (hdis : Disjoint (labO hm hmN ρ) R)
    (hstrict : ∀ Q : Om n N, a₀a ≤ g Q.1 → g Q.1 ≤ b₀a → Q ∉ labO hm hmN ρ' ∪ R →
      g ((descentOf hL hV0 hg hsupp hle).flow 1 Q).1 < g Q.1) :
    ∃ d : ℝ, 0 < d ∧ ∀ a c t : ℝ, 1 ≤ t → a < (2 * π * m) ^ 2 → (2 * π * m) ^ 2 < c →
      c - a < d →
      CupInjW (eV n hn) (inter_subset_left : (univ : Set (V2T n)) ∩ ∅ ⊆ univ) 0 →
        CupInjW (eOm n N hn) (partY_sub_partU (fun Q : Om n N => g Q.1)
          (descentOf hL hV0 hg hsupp hle) (labO hm hmN ρ) a c t) ((2 * m - 1) * (n - 1)) := by
  set D₁ := descentOf hL hV0 hg hsupp hle with hD₁
  have hρ0 : 0 < ρ := hρ.1
  have hρ' : ρ' ≤ ρ := (le_mul_of_one_le_left hρ'0.le (Real.one_le_exp zero_le_one)).trans hρρ'
  have hsub : labO (n := n) (N := N) hm hmN ρ' ⊆ labO hm hmN ρ :=
    fun Q hQ => labA_mono hm hmN hρ'0.le hρ' hQ
  obtain ⟨d₁, hd₁, htrap⟩ := Finsler.LensTrap.exists_trap D₁ hgc
    ((labO_isOpen hm hmN ρ').union hR) hK hstrict
  refine ⟨min d₁ (min ((2 * π * m) ^ 2 - a₀a) (min (b₀a - (2 * π * m) ^ 2) (ρ ^ 2 / 8))),
    lt_min hd₁ (lt_min (by linarith) (lt_min (by linarith) (by positivity))),
    fun a c t ht ha hc hd => ?_⟩
  have hd1 : c - a < d₁ := hd.trans_le (min_le_left _ _)
  have hd2 : c - a < (2 * π * m) ^ 2 - a₀a :=
    hd.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hd3 : c - a < b₀a - (2 * π * m) ^ 2 :=
    hd.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hd4 : c - a < ρ ^ 2 / 8 :=
    hd.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have haa : a₀a ≤ a := by linarith
  have hcb : c ≤ b₀a := by linarith
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  -- the trapping in unit time
  have htrap1 : ∀ w : Om n N, g w.1 < c → a ≤ g (D₁.flow 1 w).1 → w ∈ labO hm hmN ρ' ∪ R :=
    htrap a c 1 haa hcb hd1 le_rfl
  -- the trapping of the polygons
  have hS₁ : ∀ w, w ∈ labO hm hmN ρ → g w.1 < c → a ≤ g (D₁.flow t w).1 → ∀ s, 0 ≤ s → s ≤ t →
      D₁.flow s w ∈ labO hm hmN ρ := by
    intro w hw hwc hwa s hs hst
    set s₁ := max (s - 1) 0 with hs₁
    have hs₁0 : 0 ≤ s₁ := le_max_right _ _
    have hs₁s : s₁ ≤ s := max_le (by linarith) hs
    have hs₁t : 1 + s₁ ≤ t := by
      rcases le_total (s - 1) 0 with h | h
      · rw [hs₁, max_eq_right h]
        linarith
      · rw [hs₁, max_eq_left h]
        linarith
    have hs₂1 : s - s₁ ≤ 1 := by
      have : s - 1 ≤ s₁ := le_max_left _ _
      linarith
    have ha' : a ≤ g (D₁.flow 1 (D₁.flow s₁ w)).1 := by
      rw [← D₁.add 1 s₁ w zero_le_one hs₁0]
      exact hwa.trans (Finsler.LensTrap.mono_time D₁ (by linarith) hs₁t w)
    have hin : D₁.flow s₁ w ∈ labO hm hmN ρ :=
      Finsler.LensTrap.trap_piece D₁ zero_le_one (labO_isOpen hm hmN ρ) hR hdis
        (fun w' h1 h2 => (htrap1 w' h1 h2).elim (fun h => Or.inl (hsub h)) Or.inr)
        w hw hwc s₁ hs₁0 ha'
    have hin' : D₁.flow s₁ w ∈ labO hm hmN ρ' := by
      rcases htrap1 _ (lt_of_le_of_lt (D₁.mono s₁ w hs₁0) hwc) ha' with h | h
      · exact h
      · exact absurd h (Set.disjoint_left.mp hdis hin)
    have hsplit : D₁.flow s w = D₁.flow (s - s₁) (D₁.flow s₁ w) := by
      rw [← D₁.add (s - s₁) s₁ w (by linarith) hs₁0, sub_add_cancel]
    rw [hsplit]
    change (D₁.flow (s - s₁) (D₁.flow s₁ w)).1 ∈ labA hm hmN ρ
    rw [descentOf_flow_val hL hV0 hg hsupp hle (by linarith)]
    exact margin hm hmN hL hρ hVW hρ'0 hρρ' _ hin' (by linarith) hs₂1
  -- the trapping of the model
  have hρc : 4 * (c - a) < ρ ^ 2 := by linarith
  have hS₂ : ∀ w, w ∈ labelM (n := n) (N := N) (m := m) ρ → (cone hm hmN).energy w < c →
      a ≤ (cone hm hmN).energy ((descentM hm hmN).flow t w) → ∀ s, 0 ≤ s → s ≤ t →
      (descentM hm hmN).flow s w ∈ labelM ρ :=
    fun w hw hwc hwa s hs hst => model_trap hm hmN hc.le ha.le ht hρc w hw hwc hwa s hs hst
  -- the values correspond
  have hgv : ∀ w : labO (n := n) (N := N) hm hmN ρ,
      (cone hm hmN).energy (homeo hm hmN hρ w : MS n N m) = g (w : Om n N).1 := by
    intro w
    rw [cone_energy, homeo_apply]
    exact (hgM _ w.2).symm
  have hA₁ : ∀ w : labO (n := n) (N := N) hm hmN ρ,
      (∀ s, 0 ≤ s → s ≤ t → D₁.flow s (w : Om n N) ∈ labO hm hmN ρ) →
      (cone hm hmN).energy ((descentM hm hmN).flow t (homeo hm hmN hρ w : MS n N m)) =
        g (D₁.flow t (w : Om n N)).1 := by
    intro w hstay
    have hst : ∀ s ∈ Icc (0 : ℝ) t, ODE.globalSolution V hL w.1.1 s ∈ labA hm hmN ρ := by
      intro s hs
      have h := hstay s hs.1 hs.2
      change (D₁.flow s w).1 ∈ labA hm hmN ρ at h
      rwa [descentOf_flow_val hL hV0 hg hsupp hle hs.1] at h
    have h := unchart_flow_eq hm hmN hL hρ hVW w.1.1 w.2 hst t ⟨ht0, le_rfl⟩
    rw [cone_energy, descentOf_flow_val hL hV0 hg hsupp hle ht0,
      hgM _ (hst t ⟨ht0, le_rfl⟩), h]
    rfl
  have hA₂ : ∀ w : labO (n := n) (N := N) hm hmN ρ,
      (∀ s, 0 ≤ s → s ≤ t → (descentM hm hmN).flow s (homeo hm hmN hρ w : MS n N m) ∈ labelM ρ) →
      (cone hm hmN).energy ((descentM hm hmN).flow t (homeo hm hmN hρ w : MS n N m)) =
        g (D₁.flow t (w : Om n N)).1 := by
    intro w hstay
    have h := flow_eq_chart hm hmN hL hρ hVW (homeo hm hmN hρ w : MS n N m) (T := t)
      (fun s hs => hstay s hs.1 hs.2) t ⟨ht0, le_rfl⟩
    have hc0 : chart m (homeo hm hmN hρ w : MS n N m).1 = w.1.1 := by
      rw [homeo_apply]
      exact chart_unchart hm hmN w.2.1
    rw [hc0] at h
    obtain ⟨hmem, hun⟩ := chart_mem hm hmN hρ.1 hρ.2.1
      ((descentM hm hmN).flow t (homeo hm hmN hρ w : MS n N m)).2 (hstay t ht0 le_rfl).1
      (hstay t ht0 le_rfl).2
    rw [cone_energy, descentOf_flow_val hL hV0 hg hsupp hle ht0, h, hgM _ hmem, hun]
  -- the transport
  have hbij := fun q : ℕ => Finsler.LensTransport.part_bijective D₁ (descentM hm hmN)
    (homeo hm hmN hρ) hgv hS₁ hS₂ hA₁ hA₂ q
  -- the model
  intro hV
  have hM := (model_iff hm hmN ha.le hc hn (a' := a - ρ ^ 2 / 16) (ρ := ρ)
    (by linarith [sq_pos_of_pos hρ0]) (by linarith [sq_pos_of_pos hρ0]) ht (by linarith)).mp hV
  refine (cupInj_iff _ ?_ (hbij _) (hbij _)).mp hM
  exact part_class hm hmN hρ hgv c hn

end Crossing

end

end Finsler.ECupTransport
