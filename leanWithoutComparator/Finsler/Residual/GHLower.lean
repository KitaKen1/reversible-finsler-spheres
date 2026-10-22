module

public import Finsler.Loop.NativeGHPowerTimeCupAssociativity
public import Finsler.Loop.NativeGHSpectralSupport
public import Finsler.Loop.CanonicalGHLengthSupport
public import Finsler.Loop.NativeHighPowerFilteredCut

/-! GH powers act injectively and raise vanishing lengths (Claude, full-HR prototype).

The r-th GH power multiplies every positive-degree class injectively (`power_mul_injective`):
restricted associativity writes power (r+1) ⊛ B as ω ⊛ (power r ⊛ B) and ω ⊛ is injective
(`NativeGHPowers.multiply_injective`). The product vanishes on every length sublevel below the
level of the power (`power_mul_vanish`, `CanonicalGHLengthSupport.product_restriction_zero` with
the empty sublevel of length 0 for the second factor). -/

@[expose] public section

namespace Finsler.GHLower

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.MeridianLoopFamily Finsler.StrictLengthEnergyBridge

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

theorem absoluteCast_injective (X : TopCat.{0}) {i j : ℕ} (h : i = j) :
    Function.Injective (CupUnit.absoluteCast X h) := by
  subst h
  intro a b hab
  exact hab

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (P : Sphere (m + 1))
  (v₀ : equator P)

theorem right_eq_left (r k : ℕ) :
    NativeNestedTimeCupAlignment.rightDegree m 0 r k = NativeNestedTimeCupAlignment.leftDegree m 0 r k := by
  show (m + NativeGHPowers.degree m 0) + ((m + NativeGHPowers.degree m r) + k) =
    (m + ((m + NativeGHPowers.degree m 0) + NativeGHPowers.degree m r)) + k
  omega

include hm F P v₀ in
/-- **The r-th GH power multiplies positive-degree classes injectively.** -/
theorem power_mul_injective (r k : ℕ) (hk : 1 ≤ k) :
    Function.Injective (fun B : cohomologyZMod2 (Loops (m + 1)) k =>
      CanonicalGlobalTimeCup.product m (NativeGHPowers.degree m r) k (NativeGHPowers.power m r) B) := by
  induction r with
  | zero => exact NativeGHPowers.multiply_injective m hm F P v₀ k
  | succ r ih =>
    intro B B' hBB
    have hR : NativeNestedTimeCupAlignment.rightDegree m 0 r k =
        NativeNestedTimeCupAlignment.leftDegree m 0 r k := right_eq_left m r k
    have hA := fun C : cohomologyZMod2 (Loops (m + 1)) k =>
      NativeGHPowerTimeCupAssociativity.associativity_at_degree m hm F 0 r k hk C
        (NativeNestedTimeCupAlignment.leftDegree m 0 r k) rfl hR
    have h1 : CanonicalGlobalTimeCup.product m (NativeGHPowers.degree m (r + 1)) k
        (NativeGHPowers.power m (r + 1)) B = _ := hA B
    have h2 : CanonicalGlobalTimeCup.product m (NativeGHPowers.degree m (r + 1)) k
        (NativeGHPowers.power m (r + 1)) B' = _ := hA B'
    have h3 := h1.symm.trans (hBB.trans h2)
    have h4 := absoluteCast_injective (Loops (m + 1)) hR h3
    exact ih (NativeGHPowers.multiply_injective m hm F P v₀ _ h4)

theorem restrict_zero_length (k : ℕ) (y : cohomologyZMod2 (Loops (m + 1)) k) :
    (cohPullback (LengthFilteredLoopRotation.full F 0) k).hom y = 0 := by
  have : IsEmpty (SelfCutOscillation.short F 0) := short_empty F 0 le_rfl
  rw [← cocycleClass_classRepr (Loops (m + 1)) k y, cohPullback_cocycleClass]
  have he : cochainPullback (LengthFilteredLoopRotation.full F 0) k
      (classRepr (Loops (m + 1)) k y) = 0 :=
    (EmptySingularChains.chains_zero (lengthSpace F 0) k).eq_of_src _ _
  simp only [he, cocycleClass_zero]

include hm in
/-- **power r ⊛ y vanishes below the level of the r-th GH power.** -/
theorem power_mul_vanish (r k : ℕ) (y : cohomologyZMod2 (Loops (m + 1)) k) {R : ℝ}
    (hR : R < NativeGHSpectralSupport.level m F r) :
    (cohPullback (LengthFilteredLoopRotation.full F R) ((m + NativeGHPowers.degree m r) + k)).hom
      (CanonicalGlobalTimeCup.product m (NativeGHPowers.degree m r) k (NativeGHPowers.power m r) y) =
      0 := by
  obtain ⟨L, hL, hRL⟩ := exists_lt_of_lt_csSup (NativeGHSpectralSupport.supports_nonempty m hm F r) hR
  exact CanonicalGHLengthSupport.product_restriction_zero (by omega) F _ k _ y hL
    (restrict_zero_length m F k y) (by linarith)

end

end Finsler.GHLower
