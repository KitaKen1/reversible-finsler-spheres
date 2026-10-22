module

public import Finsler.Geometry.RootFlowFixed
public import Finsler.Topology.SubspacePairs

/-! When the reduced root action is the identity, ordinary root support supplies the fixed root
support required by the actual label theorem, without computing another fixed crossing. -/

@[expose] public section

namespace Finsler.RootParitySupport

open Set Finsler.Geometry Finsler.SphereGeometry Finsler.AmbientSymmetry Finsler.AmbientPenalty
open Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop Finsler.PairTriple
open Finsler.FlowLens Finsler.LensFamily Finsler.PolygonIterate Finsler.CircleHalfRotation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

theorem support_of_eq_univ {B : TopCat.{0}} (P : Set B) (hP : P = univ) (h : B → ℝ)
    {a b : ℝ} (hab : a ≤ b) (A : ℕ)
    (hf : ∀ q, Module.Finite (ZMod 2) (crossH h hab q))
    (hz : ∀ q, A ≤ q → ∀ z : crossH h hab q, z = 0) :
    (∀ q, Module.Finite (ZMod 2) (crossH (fun z : TopCat.of P => h z) hab q)) ∧
      ∀ q, A ≤ q → ∀ z : crossH (fun z : TopCat.of P => h z) hab q, z = 0 := by
  subst P
  let e q := Finsler.SubspacePairs.equalHEquiv (inter_univ (sub h a)) (inter_univ (sub h b))
    (inter_subset_inter_left univ (sub_mono h hab)) (sub_mono h hab) q
  apply Finsler.SubspacePairs.support_inside univ (sub_mono h hab) A
  · intro q
    have := hf q
    exact Module.Finite.equiv (e q).symm
  · intro q hq z
    exact (e q).injective ((hz q hq ((e q) z)).trans (e q).map_zero.symm)

theorem even_support {n : ℕ} (F : ReversibleMetric n) (m s N : ℕ) [NeZero s] [NeZero N]
    (hm : Even m) {a b : ℝ} (hab : a ≤ b) (A : ℕ)
    (hf : ∀ q, Module.Finite (ZMod 2) (crossH (W := TopCat.of (Om n (s * (2 * N))))
      (fun z : Om n (s * (2 * N)) => (m : ℝ) ^ 2 * pen F (s * (2 * N)) (1 / m) z.1) hab q))
    (hz : ∀ q, A ≤ q → ∀ z : crossH (W := TopCat.of (Om n (s * (2 * N))))
      (fun z : Om n (s * (2 * N)) => (m : ℝ) ^ 2 * pen F (s * (2 * N)) (1 / m) z.1) hab q, z = 0) :
    (∀ q, Module.Finite (ZMod 2) (crossH
      (fun z : TopCat.of {z : Om n (s * (2 * N)) |
          rotA (s * (2 * N)) (red m (s * (2 * N)) (halfIndex m s N)) z.1 = z.1} =>
        (m : ℝ) ^ 2 * pen F (s * (2 * N)) (1 / m) z.1.1) hab q)) ∧
      ∀ q, A ≤ q → ∀ z : crossH
        (fun z : TopCat.of {z : Om n (s * (2 * N)) |
            rotA (s * (2 * N)) (red m (s * (2 * N)) (halfIndex m s N)) z.1 = z.1} =>
          (m : ℝ) ^ 2 * pen F (s * (2 * N)) (1 / m) z.1.1) hab q, z = 0 :=
  support_of_eq_univ (B := TopCat.of (Om n (s * (2 * N))))
    _ (Finsler.RootFlowFixed.fixed_even m s N hm)
    (fun z : Om n (s * (2 * N)) => (m : ℝ) ^ 2 * pen F (s * (2 * N)) (1 / m) z.1) hab A hf hz

end

end Finsler.RootParitySupport
