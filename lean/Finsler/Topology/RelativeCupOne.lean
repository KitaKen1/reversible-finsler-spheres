module

public import Finsler.Topology.CupOne

/-! Mixed absolute/relative cup-one in the actual relative singular-cochain complex. -/

@[expose] public section

namespace Finsler.RelativeCupOne

open CategoryTheory SphereOddDegree Finsler.CochainComparison
open SphereOddDegree.AlexanderWhitney Finsler.RelativeCupCochain

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

def rightCup (P : TopPair.{0}) (p q : ℕ) (ψ : relative P p)
    (φ : singularCochainGroup (ZMod 2) P.fst q) : relative P (p + q) :=
  Classical.choose (exists_lift P (p + q) (cochainCup p q (toAmbient P p ψ) φ) (by
    rw [cochainCup_naturality, restriction_toAmbient, cochainCup_zero_left]))

theorem toAmbient_rightCup (P : TopPair.{0}) (p q : ℕ) (ψ : relative P p)
    (φ : singularCochainGroup (ZMod 2) P.fst q) :
    toAmbient P (p + q) (rightCup P p q ψ φ) = cochainCup p q (toAmbient P p ψ) φ :=
  Classical.choose_spec (exists_lift P (p + q) (cochainCup p q (toAmbient P p ψ) φ) (by
    rw [cochainCup_naturality, restriction_toAmbient, cochainCup_zero_left]))

def one (P : TopPair.{0}) (p q n : ℕ) (h : p + q = n + 1)
    (φ : singularCochainGroup (ZMod 2) P.fst p) (ψ : relative P q) : relative P n :=
  Classical.choose (exists_lift P n (CupOne.cupOne P.fst p q n h φ (toAmbient P q ψ))
    (CupOne.restriction_zero P.map p q n h φ (toAmbient P q ψ)
      (Or.inr (restriction_toAmbient P q ψ))))

theorem toAmbient_one (P : TopPair.{0}) (p q n : ℕ) (h : p + q = n + 1)
    (φ : singularCochainGroup (ZMod 2) P.fst p) (ψ : relative P q) :
    toAmbient P n (one P p q n h φ ψ) = CupOne.cupOne P.fst p q n h φ (toAmbient P q ψ) :=
  Classical.choose_spec (exists_lift P n (CupOne.cupOne P.fst p q n h φ (toAmbient P q ψ))
    (CupOne.restriction_zero P.map p q n h φ (toAmbient P q ψ)
      (Or.inr (restriction_toAmbient P q ψ))))

theorem rightCup_naturality {P Q : TopPair.{0}} (f : P ⟶ Q) (p q : ℕ)
    (ψ : relative Q p) (φ : singularCochainGroup (ZMod 2) Q.fst q) :
    pullback f (p + q) (rightCup Q p q ψ φ) =
      rightCup P p q (pullback f p ψ) (cochainPullback (TopPair.Hom.fst f) q φ) := by
  apply toAmbient_injective P (p + q)
  rw [toAmbient_pullback, toAmbient_rightCup, cochainCup_naturality,
    toAmbient_rightCup, toAmbient_pullback]

theorem naturality {P Q : TopPair.{0}} (f : P ⟶ Q) (p q n : ℕ) (h : p + q = n + 1)
    (φ : singularCochainGroup (ZMod 2) Q.fst p) (ψ : relative Q q) :
    pullback f n (one Q p q n h φ ψ) =
      one P p q n h (cochainPullback (TopPair.Hom.fst f) p φ) (pullback f q ψ) := by
  apply toAmbient_injective P n
  rw [toAmbient_pullback, toAmbient_one, CupOne.naturality, toAmbient_one, toAmbient_pullback]

theorem zero_left (P : TopPair.{0}) (p q n : ℕ) (h : p + q = n + 1)
    (ψ : relative P q) : one P p q n h 0 ψ = 0 := by
  apply toAmbient_injective P n
  simp only [toAmbient_one, CupOne.zero_left, map_zero]

theorem zero_right (P : TopPair.{0}) (p q n : ℕ) (h : p + q = n + 1)
    (φ : singularCochainGroup (ZMod 2) P.fst p) : one P p q n h φ 0 = 0 := by
  apply toAmbient_injective P n
  simp only [toAmbient_one, map_zero, CupOne.zero_right]

private theorem cup_cast (X : TopCat.{0}) (p q n : ℕ) (h : p + q = n)
    (φ : singularCochainGroup (ZMod 2) X p) (ψ : singularCochainGroup (ZMod 2) X q) :
    cochainCast h (cochainCup p q φ ψ) = CupOne.cup X p q n h φ ψ := by
  subst n
  simpa only [cochainCast, eqToHom_refl, Category.id_comp] using
    (CupOne.cup_comparison X p q φ ψ).symm

/-- The full mixed absolute/relative homotopy identity in the genuine relative complex. -/
theorem boundary_formula (P : TopPair.{0}) (p q n : ℕ) (h : p + q = n + 1)
    (φ : singularCochainGroup (ZMod 2) P.fst p) (ψ : relative P q) :
    differential P n (one P p q n h φ ψ) +
        one P (p + 1) q (n + 1) (by omega) (cochainCoboundary (ZMod 2) P.fst p φ) ψ +
        one P p (q + 1) (n + 1) (by omega) φ (differential P q ψ) =
      cast P h (RelativeCupCochain.cup P p q φ ψ) -
        cast P (by omega : q + p = n + 1) (rightCup P q p ψ φ) := by
  apply toAmbient_injective P (n + 1)
  simp only [map_add, map_sub, toAmbient_differential, toAmbient_one,
    toAmbient_cast, toAmbient_cup, toAmbient_rightCup, cup_cast]
  exact CupOne.boundary_formula P.fst p q n h φ (toAmbient P q ψ)

theorem boundary_cocycles (P : TopPair.{0}) (p q n : ℕ) (h : p + q = n + 1)
    (φ : singularCochainGroup (ZMod 2) P.fst p) (ψ : relative P q)
    (hφ : cochainCoboundary (ZMod 2) P.fst p φ = 0) (hψ : differential P q ψ = 0) :
    differential P n (one P p q n h φ ψ) =
      cast P h (RelativeCupCochain.cup P p q φ ψ) -
        cast P (by omega : q + p = n + 1) (rightCup P q p ψ φ) := by
  have hd := boundary_formula P p q n h φ ψ
  rw [hφ, hψ, zero_left, zero_right, add_zero, add_zero] at hd
  exact hd

theorem rightCup_closed (P : TopPair.{0}) (p q : ℕ) (ψ : relative P p)
    (φ : singularCochainGroup (ZMod 2) P.fst q)
    (hψ : differential P p ψ = 0) (hφ : cochainCoboundary (ZMod 2) P.fst q φ = 0) :
    differential P (p + q) (rightCup P p q ψ φ) = 0 := by
  apply toAmbient_injective P (p + q + 1)
  rw [toAmbient_differential, toAmbient_rightCup, map_zero]
  apply cochainCupZMod2_respects_cocycles p q _ _ ?_ hφ
  rw [← toAmbient_differential, hψ, map_zero]


end
end Finsler.RelativeCupOne
