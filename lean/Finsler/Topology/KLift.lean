module

public import Finsler.Topology.KCup

/-! Lifting multiples of a class to K-Borel cohomology.

For a pair with two commuting involutions, forgetting both involutions takes K-Borel cohomology to
actual relative cohomology (`fN`). A class a of the ambient space has *K-lifted multiples* in
degree l (`Good`) if for every K-class x of degree l some K-class is forgotten to the cup of a with
the forgotten class of x. If a is the pullback of a sphere class along a map invariant under both
involutions, this holds (the K-Borel cup `KCup.kcup`). The property is pulled back along maps of
pairs commuting with both involutions which are onto in degree l on K-Borel cohomology
(`good_pull`), and pushed forward along such maps which are onto in degree p + l on K-Borel
cohomology and injective in degree p + l on actual relative cohomology (`good_push`). -/

@[expose] public section

namespace Finsler.KLift

open CategoryTheory SphereOddDegree Finsler.BorelCochain Finsler.BorelPair Finsler.BorelGraded
open Finsler.BorelIterate Finsler.BasisBudget Finsler.BorelComparison Finsler.KCup

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- The relative cup is natural for maps of pairs. -/
theorem native_cup_natural {P Q : TopPair.{0}} (f : P ⟶ Q) (p q : ℕ)
    (a : cohomologyZMod2 Q.fst p) (b : native Q q) :
    nativePull f (p + q) (Finsler.RelativeCup.cup Q p q a b) =
      Finsler.RelativeCup.cup P p q ((cohPullback (TopPair.Hom.fst f) p).hom a)
        (nativePull f q b) :=
  Finsler.RelativeCup.naturality f p q a b

section Def

variable {P : TopPair.{0}} {r τ : P ⟶ P} (hr : r ≫ r = 𝟙 P) (hτ : τ ≫ τ = 𝟙 P)
  (hc : τ ≫ r = r ≫ τ)

/-- Forgetting both involutions, to actual relative cohomology. -/
def fN (q : ℕ) :
    HR (borelInv (Finsler.BorelInvariance.commuting hr τ hτ hc)) q →ₗ[ZMod 2] native P q :=
  forgetNative P r hr q ∘ₗ fgtR (Finsler.BorelInvariance.commuting hr τ hτ hc) q

theorem fN_apply (q : ℕ) (x : HR (borelInv (Finsler.BorelInvariance.commuting hr τ hτ hc)) q) :
    fN hr hτ hc q x =
      forgetNative P r hr q (fgtR (Finsler.BorelInvariance.commuting hr τ hτ hc) q x) := rfl

/-- **K-lifted multiples**: for every K-class x of degree l some K-class is forgotten to the cup
of a with the forgotten class of x. -/
def Good {p : ℕ} (a : cohomologyZMod2 P.fst p) (l : ℕ) : Prop :=
  ∀ x : HR (borelInv (Finsler.BorelInvariance.commuting hr τ hτ hc)) l,
    ∃ y : HR (borelInv (Finsler.BorelInvariance.commuting hr τ hτ hc)) (p + l),
      fN hr hτ hc (p + l) y = Finsler.RelativeCup.cup P p l a (fN hr hτ hc l x)

theorem good_congr {p l : ℕ} {a a' : cohomologyZMod2 P.fst p} (h : Good hr hτ hc a l)
    (e : a = a') : Good hr hτ hc a' l :=
  e ▸ h

/-- **The multiples of the pullback of a sphere class along an invariant map lift.** -/
theorem good_of_invariant {Z : TopCat.{0}} (g : P.fst ⟶ Z) (hgr : TopPair.Hom.fst r ≫ g = g)
    (hgτ : TopPair.Hom.fst τ ≫ g = g) {p : ℕ} (s : cohomologyZMod2 Z p) (l : ℕ) :
    Good hr hτ hc ((cohPullback g p).hom s) l := by
  intro x
  refine ⟨kcup P hr hτ hc (cochainPullback g p (classRepr Z p s))
    (cochainPullback_cocycle _ _ _ (classRepr_isCocycle Z p s))
    (Finsler.BorelEvaluation.cochain_invariant r g hgr p _)
    (Finsler.BorelEvaluation.cochain_invariant τ g hgτ p _) l x, ?_⟩
  rw [fN_apply, fgtR_kcup, BorelCup.cup_forgetNative]
  congr 1
  have h1 := cohPullback_cocycleClass g p (classRepr Z p s) (classRepr_isCocycle Z p s)
  rw [cocycleClass_classRepr] at h1
  exact h1.symm

end Def

section Transport

variable {P Q : TopPair.{0}} {r τ : P ⟶ P} {s σ : Q ⟶ Q} (hr : r ≫ r = 𝟙 P) (hs : s ≫ s = 𝟙 Q)
  (f : P ⟶ Q) (hf : f ≫ s = r ≫ f) (hτ : τ ≫ τ = 𝟙 P) (hσ : σ ≫ σ = 𝟙 Q)
  (hcτ : τ ≫ r = r ≫ τ) (hcσ : σ ≫ s = s ≫ σ) (hfτ : f ≫ σ = τ ≫ f)

/-- Forgetting both involutions is natural. -/
theorem fN_natural (q : ℕ)
    (x : HR (borelInv (Finsler.BorelInvariance.commuting hs σ hσ hcσ)) q) :
    fN hr hτ hcτ q (HRmap (borelHom
      (Finsler.BorelInvariance.commHom hr hs f hf hτ hσ hcτ hcσ hfτ)) q x) =
      nativePull f q (fN hs hσ hcσ q x) := by
  rw [fN_apply, fN_apply, fgtR_natural]
  exact forgetNative_natural hr hs f hf q _

/-- **Pulling back K-lifted multiples** along a map onto in degree l on K-Borel cohomology. -/
theorem good_pull {p l : ℕ} (b : cohomologyZMod2 Q.fst p)
    (hsurj : Function.Surjective (HRmap (borelHom
      (Finsler.BorelInvariance.commHom hr hs f hf hτ hσ hcτ hcσ hfτ)) l))
    (hQ : Good hs hσ hcσ b l) :
    Good hr hτ hcτ ((cohPullback (TopPair.Hom.fst f) p).hom b) l := by
  intro x
  obtain ⟨x', rfl⟩ := hsurj x
  obtain ⟨y', hy'⟩ := hQ x'
  refine ⟨HRmap (borelHom
    (Finsler.BorelInvariance.commHom hr hs f hf hτ hσ hcτ hcσ hfτ)) (p + l) y', ?_⟩
  rw [fN_natural, fN_natural, hy', native_cup_natural]

/-- **Pushing forward K-lifted multiples** along a map onto in degree p + l on K-Borel
cohomology and injective in degree p + l on actual relative cohomology. -/
theorem good_push {p l : ℕ} (b : cohomologyZMod2 Q.fst p)
    (hsurj : Function.Surjective (HRmap (borelHom
      (Finsler.BorelInvariance.commHom hr hs f hf hτ hσ hcτ hcσ hfτ)) (p + l)))
    (hinj : Function.Injective (nativePull f (p + l)))
    (hP : Good hr hτ hcτ ((cohPullback (TopPair.Hom.fst f) p).hom b) l) :
    Good hs hσ hcσ b l := by
  intro x'
  obtain ⟨y, hy⟩ := hP (HRmap (borelHom
    (Finsler.BorelInvariance.commHom hr hs f hf hτ hσ hcτ hcσ hfτ)) l x')
  obtain ⟨y', rfl⟩ := hsurj y
  refine ⟨y', hinj ?_⟩
  rw [← fN_natural hr hs f hf hτ hσ hcτ hcσ hfτ, hy, fN_natural hr hs f hf hτ hσ hcτ hcσ hfτ,
    native_cup_natural]

end Transport

end

end Finsler.KLift
