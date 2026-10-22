module

public import Finsler.Geometry.PolygonDescent
public import Finsler.Geometry.AmbientSymmetry
public import Finsler.Geometry.PolygonIterate
public import Finsler.Analysis.SphereDistance
public import Finsler.Analysis.EquivariantField

/-! A descending semiflow on the space of sphere polygons commuting with the reversal of the
vertices and with the rotation of the vertices by an element s of order two (the half rotation for
an even number of vertices). Both are continuous linear involutions of the space of ambient
polygons, they commute, and the polygon energy with normalized vertices is invariant under them
(the minimal energy of a segment is symmetric for a reversible metric). If the open set 𝒲
containing the stationary polygons of the energy band is invariant, the compact set of the band
outside 𝒲 is invariant, so the averaged pseudo-gradient field commutes with both involutions; its
tangential part does too, since they permute the vertices, and so does its global flow (uniqueness
of solutions). This is the descent of `PolygonDescent` made equivariant. -/

@[expose] public section

namespace Finsler.PolygonDescentK

open Finsler.SphereGeometry Finsler.Geometry Finsler.SphereRetraction
open Finsler.EnergySphereSmooth Finsler.PolygonCritical Finsler.PolygonLoop Finsler.PolygonSmooth
open Finsler.PolygonEnergyGlobal Finsler.EnergyDiagonal Finsler.PseudoGradient
open Finsler.SphereFlow Finsler.FlowLens Finsler.PolygonDescent Finsler.AmbientSymmetry
open Finsler.EquivariantField
open Set Filter
open scoped Topology ContDiff NNReal RealInnerProductSpace

noncomputable section

variable {n : ℕ}

/-- The reversal of the vertices of ambient polygons. -/
def revA (N : ℕ) : (ZMod N → Ambient n) →L[ℝ] (ZMod N → Ambient n) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (-i)

theorem revA_apply (N : ℕ) (Q : ZMod N → Ambient n) (i : ZMod N) : revA N Q i = Q (-i) := rfl

theorem revA_revA (N : ℕ) (Q : ZMod N → Ambient n) : revA N (revA N Q) = Q := by
  funext i
  rw [revA_apply, revA_apply, neg_neg]

theorem rotA_involutive {N : ℕ} {s : ZMod N} (hs : s + s = 0) (Q : ZMod N → Ambient n) :
    rotA N s (rotA N s Q) = Q := by
  rw [rotA_rotA, hs, rotA_zero]

theorem revA_rotA {N : ℕ} {s : ZMod N} (hs : s + s = 0) (Q : ZMod N → Ambient n) :
    revA N (rotA N s Q) = rotA N s (revA N Q) := by
  funext i
  rw [revA_apply, rotA_apply, rotA_apply, revA_apply]
  congr 1
  have : s = -s := eq_neg_of_add_eq_zero_left hs
  rw [neg_add, ← this]

/-- The minimal energy of a segment between ambient points is symmetric. -/
theorem ambientMinEnergy_swap (F : ReversibleMetric n) (x y : Ambient n) :
    ambientMinEnergy F (x, y) = ambientMinEnergy F (y, x) :=
  Finsler.SphereDistance.minEnergy_comm F _ _

/-- The polygon energy with normalized vertices is invariant under reversal of the vertices. -/
theorem polyEnergyN_revA (F : ReversibleMetric n) {N : ℕ} [NeZero N] (Q : ZMod N → Ambient n) :
    polyEnergyN F N (revA N Q) = polyEnergyN F N Q := by
  unfold polyEnergyN
  congr 1
  rw [← Finsler.PolygonIterate.sum_univ_eq_sum_range
      (fun i : ZMod N => ambientMinEnergy F (revA N Q i, revA N Q (i + 1))),
    ← Finsler.PolygonIterate.sum_univ_eq_sum_range
      (fun i : ZMod N => ambientMinEnergy F (Q i, Q (i + 1)))]
  rw [← Equiv.sum_comp ((Equiv.neg (ZMod N)).trans (Equiv.addRight (-1)))
    (fun i : ZMod N => ambientMinEnergy F (Q i, Q (i + 1)))]
  refine Finset.sum_congr rfl fun i _ => ?_
  change ambientMinEnergy F (Q (-i), Q (-(i + 1))) = ambientMinEnergy F (Q (-i + -1), Q (-i + -1 + 1))
  rw [ambientMinEnergy_swap]
  congr 2 <;> abel_nf

/-- The polygon energy with normalized vertices is invariant under rotation of the vertices. -/
theorem polyEnergyN_rotA (F : ReversibleMetric n) {N : ℕ} [NeZero N] (s : ZMod N)
    (Q : ZMod N → Ambient n) : polyEnergyN F N (rotA N s Q) = polyEnergyN F N Q :=
  Finsler.PolygonIterate.polyEnergyN_add F Q s

/-- The tangential part of a field commuting with the reversal of the vertices commutes with it. -/
theorem tang_revA {N : ℕ} {V : (ZMod N → Ambient n) → ZMod N → Ambient n}
    (hV : ∀ Q, V (revA N Q) = revA N (V Q)) (Q : ZMod N → Ambient n) :
    tang V (revA N Q) = revA N (tang V Q) := by
  funext j
  rw [tang_apply, hV, revA_apply, revA_apply, revA_apply, tang_apply]

theorem tang_rotA {N : ℕ} {s : ZMod N} {V : (ZMod N → Ambient n) → ZMod N → Ambient n}
    (hV : ∀ Q, V (rotA N s Q) = rotA N s (V Q)) (Q : ZMod N → Ambient n) :
    tang V (rotA N s Q) = rotA N s (tang V Q) := by
  funext j
  rw [tang_apply, hV, rotA_apply, rotA_apply, rotA_apply, tang_apply]

/-- The rotation of the vertices of sphere polygons by s. -/
def rotPoly {N : ℕ} (s : ZMod N) (q : ZMod N → Sphere n) : ZMod N → Sphere n := fun i => q (i + s)

theorem energy_reversePolygon (F : ReversibleMetric n) {N : ℕ} [NeZero N] (q : Poly n N) :
    energy F N (reversePolygon q) = energy F N q := by
  rw [energy_eq, energy_eq]
  exact polyEnergyN_revA F (amb q)

theorem energy_rotPoly (F : ReversibleMetric n) {N : ℕ} [NeZero N] (s : ZMod N) (q : Poly n N) :
    energy F N (rotPoly s q) = energy F N q := by
  rw [energy_eq, energy_eq]
  exact polyEnergyN_rotA F s (amb q)

theorem amb_reversePolygon {N : ℕ} (q : ZMod N → Sphere n) :
    amb (reversePolygon q) = revA N (amb q) := rfl

theorem amb_rotPoly {N : ℕ} (s : ZMod N) (q : ZMod N → Sphere n) :
    amb (rotPoly s q) = rotA N s (amb q) := rfl

theorem reversePolygon_reversePolygon {N : ℕ} (q : ZMod N → Sphere n) :
    reversePolygon (reversePolygon q) = q := by
  funext i
  change q (-(-i)) = q i
  rw [neg_neg]

theorem rotPoly_rotPoly {N : ℕ} {s : ZMod N} (hs : s + s = 0) (q : ZMod N → Sphere n) :
    rotPoly s (rotPoly s q) = q := by
  funext i
  change q (i + s + s) = q i
  rw [add_assoc, hs, add_zero]

/-- **An equivariant descending semiflow on the polygon space.** For an element s of order two of
ZMod N and an open set 𝒲 invariant under the reversal and the rotation by s containing the
stationary polygons of the energy band [a₀, b₀], there is a descent of the polygon energy commuting
with the reversal and the rotation by s whose time-one map decreases the energy strictly at the
polygons of the band outside 𝒲. -/
theorem exists_descent_K (F : ReversibleMetric n) (hn : 1 ≤ n) {N : ℕ} [NeZero N] {s : ZMod N}
    (hs : s + s = 0) {δ : ℝ}
    (hδ : ∀ P Q : Sphere n, ‖(Q : Ambient n) - P‖ < δ →
      ContDiffAt ℝ 1 (ambientMinEnergy F) ((P : Ambient n), (Q : Ambient n)))
    {a₀ b₀ : ℝ} (hshort : ∀ q : ZMod N → Sphere n, energy F N q ≤ b₀ → ShortPolygon δ q)
    {𝒲 : Set (Poly n N)} (h𝒲 : IsOpen 𝒲)
    (h𝒲r : ∀ q : ZMod N → Sphere n, q ∈ 𝒲 → reversePolygon q ∈ 𝒲)
    (h𝒲h : ∀ q : ZMod N → Sphere n, q ∈ 𝒲 → rotPoly s q ∈ 𝒲)
    (hcrit : ∀ q : ZMod N → Sphere n, a₀ ≤ energy F N q → energy F N q ≤ b₀ →
      PolyCritical F N q → q ∈ 𝒲) :
    ∃ D : Descent (Poly n N) (energy F N),
      (∀ t (q : ZMod N → Sphere n), D.flow t (reversePolygon q) = reversePolygon (D.flow t q)) ∧
      (∀ t (q : ZMod N → Sphere n), D.flow t (rotPoly s q) = rotPoly s (D.flow t q)) ∧
      ∀ q : Poly n N, a₀ ≤ energy F N q → energy F N q ≤ b₀ → q ∉ 𝒲 →
        energy F N (D.flow 1 q) < energy F N q := by
  set O : Set (ZMod N → Ambient n) := {Q | ContDiffAt ℝ 1 (polyEnergyN F N) Q} with hOdef
  have hO : IsOpen O := by
    rw [isOpen_iff_mem_nhds]
    intro Q hQ
    exact ContDiffAt.eventually (show ContDiffAt ℝ 1 (polyEnergyN F N) Q from hQ) (by simp)
  have hfO : ContDiffOn ℝ 1 (polyEnergyN F N) O := fun Q hQ =>
    (show ContDiffAt ℝ 1 (polyEnergyN F N) Q from hQ).contDiffWithinAt
  have hdiff : ∀ P ∈ O, DifferentiableAt ℝ (polyEnergyN F N) P := fun P hP =>
    (show ContDiffAt ℝ 1 (polyEnergyN F N) P from hP).differentiableAt one_ne_zero
  -- invariance of the energy and of O
  have hfr : ∀ Q, polyEnergyN F N (revA N Q) = polyEnergyN F N Q := polyEnergyN_revA F
  have hfh : ∀ Q, polyEnergyN F N (rotA N s Q) = polyEnergyN F N Q := polyEnergyN_rotA F s
  have hOr : ∀ Q ∈ O, revA N Q ∈ O := by
    intro Q hQ
    have e : polyEnergyN F N = polyEnergyN F N ∘ revA N := funext fun P => (hfr P).symm
    change ContDiffAt ℝ 1 (polyEnergyN F N) (revA N Q)
    rw [e]
    refine ContDiffAt.comp (revA N Q) ?_ (revA N).contDiff.contDiffAt
    rw [revA_revA]
    exact hQ
  have hOh : ∀ Q ∈ O, rotA N s Q ∈ O := by
    intro Q hQ
    have e : polyEnergyN F N = polyEnergyN F N ∘ rotA N s := funext fun P => (hfh P).symm
    change ContDiffAt ℝ 1 (polyEnergyN F N) (rotA N s Q)
    rw [e]
    refine ContDiffAt.comp (rotA N s Q) ?_ (rotA N s).contDiff.contDiffAt
    rw [rotA_involutive hs]
    exact hQ
  set C : Set (Poly n N) := {q | a₀ ≤ energy F N q ∧ energy F N q ≤ b₀} ∩ 𝒲ᶜ with hCdef
  have hCc : IsCompact C :=
    ((isClosed_le continuous_const (energy_continuous F hn N)).inter
      (isClosed_le (energy_continuous F hn N) continuous_const)).inter
        h𝒲.isClosed_compl |>.isCompact
  have hCr : ∀ q ∈ C, reversePolygon q ∈ C := by
    rintro q ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨?_, ?_⟩, fun h => h3 ?_⟩
    · rw [energy_reversePolygon]; exact h1
    · rw [energy_reversePolygon]; exact h2
    · have := h𝒲r _ h
      rwa [reversePolygon_reversePolygon] at this
  have hCh : ∀ q ∈ C, rotPoly s q ∈ C := by
    rintro q ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨?_, ?_⟩, fun h => h3 ?_⟩
    · rw [energy_rotPoly]; exact h1
    · rw [energy_rotPoly]; exact h2
    · have := h𝒲h _ h
      rwa [rotPoly_rotPoly hs] at this
  have hA : IsCompact (amb '' C) := hCc.image (amb_continuous N)
  have hmemO : ∀ q : ZMod N → Sphere n, energy F N q ≤ b₀ → amb q ∈ O :=
    fun q hq => polyEnergyN_contDiffAt_one F hδ (hshort q hq)
  have hAO : amb '' C ⊆ O := by
    rintro _ ⟨q, hq, rfl⟩
    exact hmemO q hq.1.2
  have hAr : ∀ Q ∈ amb '' C, revA N Q ∈ amb '' C := by
    rintro _ ⟨q, hq, rfl⟩
    exact ⟨reversePolygon q, hCr q hq, rfl⟩
  have hAh : ∀ Q ∈ amb '' C, rotA N s Q ∈ amb '' C := by
    rintro _ ⟨q, hq, rfl⟩
    exact ⟨rotPoly s q, hCh q hq, rfl⟩
  have hne : ∀ Q ∈ amb '' C, fderiv ℝ (polyEnergyN F N) Q ≠ 0 := by
    rintro _ ⟨q, hq, rfl⟩ h0
    have hd := (hdiff _ (hmemO q hq.1.2)).hasFDerivAt
    rw [h0] at hd
    exact hq.2 (hcrit q hq.1.1 hq.1.2 (polyCritical_of_hasFDerivAt F hd))
  obtain ⟨V, hVs, hVcs, hVt, hVle, hVlt, hVr, hVh⟩ :=
    exists_pseudoGradient_equivariant (revA_revA N) (rotA_involutive hs)
      (fun Q => (revA_rotA hs Q)) hfr hfh hO hfO hOr hOh hA hAO hAr hAh hne
  have hXs : ContDiff ℝ ∞ (tang V) := tang_contDiff hVs
  have hXc : HasCompactSupport (tang V) := tang_hasCompactSupport hVcs
  obtain ⟨K, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hXc hXs (by simp)
  have hVc : Continuous V := hVs.continuous
  have hsupp : ∀ P, tang V P ≠ 0 → P ∈ O := by
    intro P hP
    apply hVt
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
  have hflowr : ∀ (t : ℝ) (q : ZMod N → Sphere n),
      flowP hVc hL t (reversePolygon q) = reversePolygon (flowP hVc hL t q) := by
    intro t q
    funext j
    apply Subtype.ext
    change ODE.globalSolution (tang V) hL (revA N (amb q)) (max t 0) j =
      ODE.globalSolution (tang V) hL (amb q) (max t 0) (-j)
    rw [globalSolution_map (tang V) hL (revA N) (tang_revA hVr) (amb q) (max t 0)]
    rfl
  have hflowh : ∀ (t : ℝ) (q : ZMod N → Sphere n),
      flowP hVc hL t (rotPoly s q) = rotPoly s (flowP hVc hL t q) := by
    intro t q
    funext j
    apply Subtype.ext
    change ODE.globalSolution (tang V) hL (rotA N s (amb q)) (max t 0) j =
      ODE.globalSolution (tang V) hL (amb q) (max t 0) (j + s)
    rw [globalSolution_map (tang V) hL (rotA N s) (tang_rotA hVh) (amb q) (max t 0)]
    rfl
  refine ⟨{ flow := flowP hVc hL
            cont := flowP_continuous hVc hL
            zero := flowP_zero hVc hL
            add := flowP_add hVc hL
            mono := ?_ }, hflowr, hflowh, ?_⟩
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

end Finsler.PolygonDescentK
