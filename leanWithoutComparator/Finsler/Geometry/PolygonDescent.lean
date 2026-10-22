module

public import Finsler.Geometry.PolygonEnergyGlobal
public import Finsler.Geometry.EnergyDiagonal
public import Finsler.Analysis.PseudoGradient
public import Finsler.Analysis.SphereFlow
public import Finsler.Topology.FlowLens

/-! A descending semiflow on the space of sphere polygons. The polygon space is the compact
product of N copies of the sphere, with the polygon energy as a continuous function. Suppose
that the polygons of energy at most b₀ are short, so that the energy with normalized vertices
is C¹ at them, and let 𝒲 be an open set containing the polygons of energy in [a₀, b₀] which are
stationary along all curves of sphere polygons. On the compact set of the polygons of energy in
[a₀, b₀] outside 𝒲 the derivative of the energy does not vanish, so there is a pseudo-gradient
field; its tangential part is a smooth compactly supported field on the ambient space whose
global flow keeps the product of the spheres. The flow for nonnegative times is a descent for
the polygon energy, and its time-one map decreases the energy strictly at the polygons of
energy in [a₀, b₀] outside 𝒲. -/

@[expose] public section

namespace Finsler.PolygonDescent

open Finsler.SphereGeometry Finsler.Geometry Finsler.SphereRetraction
open Finsler.EnergySphereSmooth Finsler.PolygonCritical Finsler.PolygonLoop Finsler.PolygonSmooth
open Finsler.PolygonEnergyGlobal Finsler.EnergyDiagonal Finsler.PseudoGradient
open Finsler.SphereFlow Finsler.FlowLens
open Set Filter
open scoped Topology ContDiff NNReal

noncomputable section

variable {n : ℕ}

/-- The space of sphere polygons with N vertices. -/
abbrev Poly (n N : ℕ) : TopCat.{0} := TopCat.of (ZMod N → Sphere n)

/-- The ambient polygon of a sphere polygon. -/
def amb {N : ℕ} (q : ZMod N → Sphere n) : ZMod N → Ambient n := fun i => (q i : Ambient n)

theorem amb_continuous (N : ℕ) : Continuous (amb : (ZMod N → Sphere n) → ZMod N → Ambient n) :=
  continuous_pi fun i => continuous_subtype_val.comp (continuous_apply i)

theorem norm_amb {N : ℕ} (q : ZMod N → Sphere n) (i : ZMod N) : ‖amb q i‖ = 1 := norm_coe (q i)

/-- The polygon energy as a function on the polygon space. -/
def energy (F : ReversibleMetric n) (N : ℕ) (q : Poly n N) : ℝ := polyEnergy F N (amb q)

theorem energy_continuous (F : ReversibleMetric n) (hn : 1 ≤ n) (N : ℕ) :
    Continuous (energy F N) := polyEnergy_continuous F hn N

theorem energy_eq (F : ReversibleMetric n) (N : ℕ) (q : Poly n N) :
    energy F N q = polyEnergyN F N (amb q) := (polyEnergyN_eq F N (norm_amb q)).symm

section Flow

variable {N : ℕ} [NeZero N] {V : (ZMod N → Ambient n) → ZMod N → Ambient n} {K : ℝ≥0}
  (hVc : Continuous V) (hL : LipschitzWith K (tang V))

/-- The polygon at time max(t, 0) of the flow of the tangential field. -/
def flowP (t : ℝ) (q : Poly n N) : Poly n N :=
  fun j => ⟨ODE.globalSolution (tang V) hL (amb q) (max t 0) j,
    mem_sphere_zero_iff_norm.mpr
      (norm_globalSolution hVc hL (amb q) j (norm_amb q j) (le_max_right t 0))⟩

theorem amb_flowP (t : ℝ) (q : Poly n N) :
    amb (flowP hVc hL t q) = ODE.globalSolution (tang V) hL (amb q) (max t 0) := rfl

theorem flowP_continuous : Continuous fun p : ℝ × Poly n N => flowP hVc hL p.1 p.2 := by
  refine continuous_pi fun j => Continuous.subtype_mk ?_ _
  have h := ODE.continuous_globalSolution (tang V) hL
  have hpair : Continuous fun p : ℝ × Poly n N => (max p.1 0, amb p.2) :=
    (continuous_fst.max continuous_const).prodMk ((amb_continuous N).comp continuous_snd)
  exact (continuous_apply j).comp (h.comp hpair)

theorem flowP_zero (q : Poly n N) : flowP hVc hL 0 q = q := by
  funext j
  apply Subtype.ext
  change ODE.globalSolution (tang V) hL (amb q) (max 0 0) j = (q j : Ambient n)
  rw [max_self, ODE.globalSolution_zero]
  rfl

theorem flowP_add (s t : ℝ) (q : Poly n N) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    flowP hVc hL (s + t) q = flowP hVc hL s (flowP hVc hL t q) := by
  funext j
  apply Subtype.ext
  change ODE.globalSolution (tang V) hL (amb q) (max (s + t) 0) j =
    ODE.globalSolution (tang V) hL (amb (flowP hVc hL t q)) (max s 0) j
  rw [amb_flowP, max_eq_left (add_nonneg hs ht), max_eq_left hs, max_eq_left ht, add_comm s t,
    ODE.globalSolution_add]

end Flow

/-- A descending semiflow on the polygon space whose time-one map decreases the energy strictly
at the polygons of energy in [a₀, b₀] outside an open set containing the stationary ones. -/
theorem exists_descent (F : ReversibleMetric n) (hn : 1 ≤ n) {N : ℕ} [NeZero N] {δ : ℝ}
    (hδ : ∀ P Q : Sphere n, ‖(Q : Ambient n) - P‖ < δ →
      ContDiffAt ℝ 1 (ambientMinEnergy F) ((P : Ambient n), (Q : Ambient n)))
    {a₀ b₀ : ℝ} (hshort : ∀ q : ZMod N → Sphere n, energy F N q ≤ b₀ → ShortPolygon δ q)
    {𝒲 : Set (Poly n N)} (h𝒲 : IsOpen 𝒲)
    (hcrit : ∀ q : ZMod N → Sphere n, a₀ ≤ energy F N q → energy F N q ≤ b₀ →
      PolyCritical F N q → q ∈ 𝒲) :
    ∃ D : Descent (Poly n N) (energy F N), ∀ q : Poly n N, a₀ ≤ energy F N q →
      energy F N q ≤ b₀ → q ∉ 𝒲 → energy F N (D.flow 1 q) < energy F N q := by
  set O : Set (ZMod N → Ambient n) := {Q | ContDiffAt ℝ 1 (polyEnergyN F N) Q} with hOdef
  have hO : IsOpen O := by
    rw [isOpen_iff_mem_nhds]
    intro Q hQ
    exact ContDiffAt.eventually (show ContDiffAt ℝ 1 (polyEnergyN F N) Q from hQ) (by simp)
  have hfO : ContDiffOn ℝ 1 (polyEnergyN F N) O := fun Q hQ =>
    (show ContDiffAt ℝ 1 (polyEnergyN F N) Q from hQ).contDiffWithinAt
  have hdiff : ∀ P ∈ O, DifferentiableAt ℝ (polyEnergyN F N) P := fun P hP =>
    (show ContDiffAt ℝ 1 (polyEnergyN F N) P from hP).differentiableAt one_ne_zero
  set C : Set (Poly n N) := {q | a₀ ≤ energy F N q ∧ energy F N q ≤ b₀} ∩ 𝒲ᶜ with hCdef
  have hCc : IsCompact C :=
    ((isClosed_le continuous_const (energy_continuous F hn N)).inter
      (isClosed_le (energy_continuous F hn N) continuous_const)).inter
        h𝒲.isClosed_compl |>.isCompact
  have hA : IsCompact (amb '' C) := hCc.image (amb_continuous N)
  have hmemO : ∀ q : ZMod N → Sphere n, energy F N q ≤ b₀ → amb q ∈ O :=
    fun q hq => polyEnergyN_contDiffAt_one F hδ (hshort q hq)
  have hAO : amb '' C ⊆ O := by
    rintro _ ⟨q, hq, rfl⟩
    exact hmemO q hq.1.2
  have hne : ∀ Q ∈ amb '' C, fderiv ℝ (polyEnergyN F N) Q ≠ 0 := by
    rintro _ ⟨q, hq, rfl⟩ h0
    have hd := (hdiff _ (hmemO q hq.1.2)).hasFDerivAt
    rw [h0] at hd
    exact hq.2 (hcrit q hq.1.1 hq.1.2 (polyCritical_of_hasFDerivAt F hd))
  obtain ⟨V, hVs, hVcs, hVt, hVle, hVlt⟩ := exists_pseudoGradient hO hfO hA hAO hne
  have hXs : ContDiff ℝ ∞ (tang V) := tang_contDiff hVs
  have hXc : HasCompactSupport (tang V) := tang_hasCompactSupport hVcs
  obtain ⟨K, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hXc hXs (by simp)
  have hVc : Continuous V := hVs.continuous
  have hsupp : ∀ P, tang V P ≠ 0 → P ∈ O := by
    intro P hP
    apply hVt
    apply subset_tsupport
    intro h0
    apply hP
    funext j
    rw [tang_apply, h0]
    simp
  have hunit : ∀ (q : Poly n N) (s : ℝ), 0 ≤ s → ∀ j,
      ‖ODE.globalSolution (tang V) hL (amb q) s j‖ = 1 :=
    fun q s hs j => norm_globalSolution hVc hL (amb q) j (norm_amb q j) hs
  have hrad : ∀ P : ZMod N → Ambient n, P ∈ O → (∀ j, ‖P j‖ = 1) →
      fderiv ℝ (polyEnergyN F N) P (tang V P) = fderiv ℝ (polyEnergyN F N) P (V P) := by
    intro P hP hP1
    refine fderiv_tang (fun j => ?_) V
    exact fderiv_single_eq_zero (hdiff P hP) (polyEnergyN_rescale F N P (fun i h0 => by
      have h1 := hP1 i
      rw [h0, norm_zero] at h1
      exact zero_ne_one h1) j)
  have hsign : ∀ (q : Poly n N) (T : ℝ), ∀ s ∈ Icc (0 : ℝ) T,
      ODE.globalSolution (tang V) hL (amb q) s ∈ O →
      fderiv ℝ (polyEnergyN F N) (ODE.globalSolution (tang V) hL (amb q) s)
        (tang V (ODE.globalSolution (tang V) hL (amb q) s)) ≤ 0 := by
    intro q T s hs hsO
    rw [hrad _ hsO (hunit q s hs.1)]
    exact hVle _ hsO
  have henergy : ∀ (q : Poly n N) (t : ℝ), 0 ≤ t → energy F N (flowP hVc hL t q) =
      polyEnergyN F N (ODE.globalSolution (tang V) hL (amb q) t) := by
    intro q t ht
    rw [energy_eq, amb_flowP, max_eq_left ht]
  refine ⟨{ flow := flowP hVc hL
            cont := flowP_continuous hVc hL
            zero := flowP_zero hVc hL
            add := flowP_add hVc hL
            mono := ?_ }, ?_⟩
  · intro t q ht
    rw [henergy q t ht, energy_eq]
    have hanti := antitoneOn_along hL hdiff hsupp (hsign q t)
    have h := hanti ⟨le_rfl, ht⟩ ⟨ht, le_rfl⟩ ht
    have h' : polyEnergyN F N (ODE.globalSolution (tang V) hL (amb q) t) ≤
        polyEnergyN F N (ODE.globalSolution (tang V) hL (amb q) 0) := h
    rwa [ODE.globalSolution_zero] at h'
  · intro q ha hb hq
    change energy F N (flowP hVc hL 1 q) < energy F N q
    rw [henergy q 1 zero_le_one, energy_eq]
    have hqC : amb q ∈ amb '' C := ⟨q, ⟨⟨ha, hb⟩, hq⟩, rfl⟩
    have hneg : fderiv ℝ (polyEnergyN F N) (amb q) (tang V (amb q)) < 0 := by
      rw [hrad _ (hAO hqC) (norm_amb q)]
      exact hVlt _ hqC
    exact lt_along hL hdiff hsupp zero_lt_one (hsign q 1) hneg

end

end Finsler.PolygonDescent
