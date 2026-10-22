module

public import Finsler.Algebra.FrameBlocks
public import Finsler.Geometry.CircleEigenFrames

/-! Smooth signed-equivariant fields near actual even critical circles and a uniform interface for both parities. -/

@[expose] public section

namespace Finsler.CircleEvenFields

open Set Module QuadraticMap
open Finsler.SphereGeometry Finsler.Geometry Finsler.PolygonDescent Finsler.PolygonModel
open Finsler.PolygonIterate Finsler.AmbientSymmetry Finsler.AmbientNormalIndex
open Finsler.AmbientRotation Finsler.SymmetricBlocks Finsler.NormalFamily
open Finsler.GeodesicFrames Finsler.CircleFrameField Finsler.CircleHalfRotation
open Finsler.GeodesicNormalData Finsler.InvolutionIndex Finsler.DefiniteFrames
open Finsler.SamplePhase Finsler.PhaseNullity Finsler.SmoothSobolev
open Finsler.FrameBlocks Finsler.CircleEigenFrames Finsler.CurveEquivFrames
open scoped ContDiff

noncomputable section
set_option maxSynthPendingDepth 5

variable {n : ℕ} {F : ReversibleMetric n}

/-- Assemble the two eigenspace blocks, descend to the actual circle, and smooth equivariantly.
The frame size is the negative index of the chosen signed normal form. -/
theorem exists_even_frame_field (g : Finsler.Geodesics.ClosedGeodesic F)
    (hprime : Finsler.Geodesics.Prime g) (s m : ℕ) [NeZero s] [NeZero m]
    (hgcd : Nat.gcd (s * m) (iterData g).L = Nat.gcd s (iterData g).L)
    (hpar : Even s ∨ Odd m) (heven : Even (m * s)) (ε : ℝ) (hε : ε ≠ 0) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ [NeZero N],
      Nonempty (SignedFrameField g s m N ε (sigNeg (LinearMap.BilinMap.toQuadraticMap
        (ε • formB m (s * (2 * N)) F (rootFamily g s N) 0)))) := by
  obtain ⟨M⟩ := exists_segmentData F
  obtain ⟨K₀, hK₀⟩ := exists_sample_facts_all M g
  obtain ⟨N₁, hN₁⟩ := exists_even_signed_eigen_frame g s m hgcd hpar heven ε hε
  obtain ⟨N₂, hN₂⟩ := exists_normal_families g s m hgcd
  refine ⟨K₀ + N₁ + N₂, fun N hN _ => ?_⟩
  have hf : ∀ a : ℝ, SampleFacts M (ofSmooth (Finsler.Loops.shift g.loop a)) (2 * N) := fun a =>
    hK₀ a (2 * N) (by omega)
  obtain ⟨Hp, hHp, hHpe, hHpn⟩ := hN₁ N (by omega) 1 (by norm_num)
  obtain ⟨Hm, hHm, hHme, hHmn⟩ := hN₁ N (by omega) (-1) (by norm_num)
  obtain ⟨hsm, hB, -, -⟩ := hN₂ N (by omega)
  let T := rotV (n := n) m (s * (2 * N)) (halfIndex m s N)
  let τ := rotA (n := n) (s * (2 * N)) (red m (s * (2 * N)) (halfIndex m s N))
  let B := fun a => ε • formB m (s * (2 * N)) F (rootFamily g s N) a
  have hsym : ∀ a v w, B a v w = B a w v := by
    intro a v w
    change ε * formB m (s * (2 * N)) F (rootFamily g s N) a v w =
      ε * formB m (s * (2 * N)) F (rootFamily g s N) a w v
    rw [hB.symm a v w]
  have hinv : ∀ a v w, B a (T v) (T w) = B a v w := by
    intro a v w
    change ε * formB m (s * (2 * N)) F (rootFamily g s N) a (T v) (T w) =
      ε * formB m (s * (2 * N)) F (rootFamily g s N) a v w
    rw [formB_half_even g m s N heven hsm]
  have hTT : ∀ v, T (T v) = v := normal_half_involutive m s N
  have hττ : ∀ z, τ (τ z) = z := root_half_involutive m s N
  let bp := sigNeg (LinearMap.BilinMap.toQuadraticMap (eigenForm T.toLinearMap 1 (B 0)))
  let bm := sigNeg (LinearMap.BilinMap.toQuadraticMap (eigenForm T.toLinearMap (-1) (B 0)))
  have hsize : sigNeg (LinearMap.BilinMap.toQuadraticMap (B 0)) = bp + bm :=
    sigNeg_eq_eigenspace_add T.toLinearMap hTT (B 0) (hsym 0) (hinv 0)
  change Nonempty (SignedFrameField g s m N ε (sigNeg (LinearMap.BilinMap.toQuadraticMap (B 0))))
  rw [hsize]
  let H : ℝ → Fin (bp + bm) → normal (rotL (n := n) m (s * (2 * N))) m := fun a =>
    Fin.append (fun i => (Hp a i : normal (rotL m (s * (2 * N))) m))
      (fun i => (Hm a i : normal (rotL m (s * (2 * N))) m))
  let d : Fin (bp + bm) → ℝ := Fin.append (fun _ => 1) (fun _ => -1)
  have hd : ∀ i, d i * d i = 1 := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [d]
  have hH : Continuous H := continuous_append
    (continuous_pi fun i => continuous_subtype_val.comp ((continuous_apply i).comp hHp))
    (continuous_pi fun i => continuous_subtype_val.comp ((continuous_apply i).comp hHm))
  have hHe : H 1 = H 0 := by
    dsimp only [H]
    rw [hHpe, hHme]
  have hHn : ∀ a ∈ Icc (0 : ℝ) 1, Neg (B a) (H a) := by
    intro a ha
    exact neg_eigen_append T.toLinearMap (B a) (hsym a) (hinv a) (hHpn a ha) (hHmn a ha)
  have hHS : ∀ a, signAction T d (H a) = H a := fun a => signAction_eigen_append T (Hp a) (Hm a)
  have hshift : ∀ a ∈ Icc (0 : ℝ) 1, ∃ a' ∈ Icc (0 : ℝ) 1,
      amb (rootFamily g s N a') = τ (amb (rootFamily g s N a)) ∧ H a' = signAction T d (H a) := by
    intro a ha
    exact ⟨a, ha, (root_half_even g m s N heven a).symm, (hHS a).symm⟩
  obtain ⟨G, U, hG, hGeq, hU, hcurve, hsub, hUτ, hneg⟩ :=
    exists_equivariant_field_on_curve τ (signAction T d) hττ (signAction_involutive T hTT d hd)
      (rootFamily_continuous g s N) hH (closed_frame_same_root M g hprime s m N hf H hHe)
      hshift (smoothSet_isOpen m (s * (2 * N)) F) (fun a _ => hsm a)
      (fun z => ε • normalForm m (s * (2 * N)) F z)
      (continuousOn_const.smul (normalForm_continuousOn m (s * (2 * N)) F)) hHn
  refine ⟨⟨d, G, U, hd, hG, hGeq, hU, ?_, hsub, hUτ, hneg⟩⟩
  intro a
  rw [rootFamily_fract]
  exact hcurve _ ⟨Int.fract_nonneg a, (Int.fract_lt_one a).le⟩

/-- Both smooth adapted fields for an actual even iterate, with the geometric index sizes. -/
theorem exists_even_frame_fields (g : Finsler.Geodesics.ClosedGeodesic F)
    (hprime : Finsler.Geodesics.Prime g) (s m : ℕ) [NeZero s] [NeZero m]
    (hgcd : Nat.gcd (s * m) (iterData g).L = Nat.gcd s (iterData g).L)
    (hpar : Even s ∨ Odd m) (heven : Even (m * s)) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ [NeZero N],
      Nonempty (SignedFrameField g s m N 1 ((iterData g).I (s * m) - (iterData g).I s)) ∧
      Nonempty (SignedFrameField g s m N (-1)
        (finrank ℝ (normal (rotL (n := n) m (s * (2 * N))) m) -
          ((iterData g).I (s * m) - (iterData g).I s))) := by
  obtain ⟨N₁, hN₁⟩ := exists_even_frame_field g hprime s m hgcd hpar heven 1 (by norm_num)
  obtain ⟨N₂, hN₂⟩ := exists_even_frame_field g hprime s m hgcd hpar heven (-1) (by norm_num)
  obtain ⟨N₃, hN₃⟩ := exists_normal_families g s m hgcd
  refine ⟨N₁ + N₂ + N₃, fun N hN _ => ?_⟩
  obtain ⟨-, hFn, hFp, hk⟩ := hN₃ N (by omega)
  obtain ⟨G, hG⟩ := hFn.ex 0
  obtain ⟨H, hH⟩ := hFp.ex 0
  have hb := sigNeg_eq_of_complementary _ (hFn.symm 0) (hk 0) hG hH
  have hp : sigNeg (LinearMap.BilinMap.toQuadraticMap
      (-formB m (s * (2 * N)) F (rootFamily g s N) 0)) =
        finrank ℝ (normal (rotL (n := n) m (s * (2 * N))) m) -
          ((iterData g).I (s * m) - (iterData g).I s) := by
    have h := Finsler.FormSemicontinuity.sigPos_add_sigNeg_add_ker (hFn.symm 0)
    rw [hk 0, finrank_bot, add_zero, hb] at h
    rw [LinearMap.BilinMap.toQuadraticMap_neg, sigNeg_neg]
    omega
  exact ⟨by simpa only [one_smul, hb] using hN₁ N (by omega),
    by simpa only [neg_one_smul, hp] using hN₂ N (by omega)⟩

/-- Uniform interface for both parities of the actual iterate. -/
theorem exists_adapted_frame_fields (g : Finsler.Geodesics.ClosedGeodesic F)
    (hprime : Finsler.Geodesics.Prime g) (s m : ℕ) [NeZero s] [NeZero m]
    (hgcd : Nat.gcd (s * m) (iterData g).L = Nat.gcd s (iterData g).L)
    (hpar : Even s ∨ Odd m) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ [NeZero N],
      Nonempty (SignedFrameField g s m N 1 ((iterData g).I (s * m) - (iterData g).I s)) ∧
      Nonempty (SignedFrameField g s m N (-1)
        (finrank ℝ (normal (rotL (n := n) m (s * (2 * N))) m) -
          ((iterData g).I (s * m) - (iterData g).I s))) := by
  rcases Nat.even_or_odd (m * s) with heven | hodd
  · exact exists_even_frame_fields g hprime s m hgcd hpar heven
  · exact exists_odd_frame_fields g hprime s m hgcd hodd

end

end Finsler.CircleEvenFields
