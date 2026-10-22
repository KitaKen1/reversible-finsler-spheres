module

public import Finsler.Topology.CupOne
public import Finsler.Topology.CupUnit

/-! Graded commutativity over F₂, including degree zero, in the existing cohomology model. -/

@[expose] public section

namespace Finsler.CupCommutativity

open CategoryTheory MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.RelativeCap

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

abbrev genericCup (X : TopCat.{0}) (p q n : ℕ) (h : p + q = n)
    (a : (native X).homology p) (b : (native X).homology q) : (native X).homology n :=
  TauCeti.ChainComplex.cup (C := ModuleCat (ZMod 2)) (A := absolute X) (B := absolute X)
    (M := coeff) (N := coeff) (P := coeff) (ZMod 2) (diagonal X) (ρ_ coeff).hom p q n h a b

/-- Compare through the public cycle-class formulas, with no extra comparison hypothesis. -/
theorem singularCup_generic (X : TopCat.{0}) (p q n : ℕ) (h : p + q = n)
    (a : (native X).homology p) (b : (native X).homology q) :
    X.singularCup (ZMod 2) (λ_ (𝟙_ (ModuleCat (ZMod 2)))).inv
        (ρ_ coeff).hom p q n h a b = genericCup X p q n h a b := by
  obtain ⟨α, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective (native X) p a
  obtain ⟨β, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective (native X) q b
  exact (TopCat.singularCup_homologyπ X (ZMod 2) (λ_ (𝟙_ (ModuleCat (ZMod 2)))).inv
    (ρ_ coeff).hom p q n h α β).trans
      (TauCeti.ChainComplex.cup_homologyπ (diagonal X) (ρ_ coeff).hom p q n h α β).symm

private theorem sign_smul {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (p : ℕ) (v : V) : ((-1 : ℤ) ^ p) • v = v := by
  have hs : (((-1 : ℤ) ^ p : ℤ) : ZMod 2) = 1 := by
    simp only [Int.cast_pow, Int.cast_neg, Int.cast_one, ZMod.neg_eq_self_mod_two, one_pow]
  rw [← Int.cast_smul_eq_zsmul (ZMod 2), hs, one_smul]

theorem generic_comm (X : TopCat.{0}) (p q n : ℕ) (h : p + q = n)
    (a : (native X).homology p) (b : (native X).homology q) :
    genericCup X q p n (by omega) b a = genericCup X p q n h a b := by
  have hμ : (β_ coeff coeff).hom ≫ (ρ_ coeff).hom = (ρ_ coeff).hom := by
    change (β_ (𝟙_ (ModuleCat (ZMod 2))) (𝟙_ (ModuleCat (ZMod 2)))).hom ≫
        (ρ_ (𝟙_ (ModuleCat (ZMod 2)))).hom = (ρ_ (𝟙_ (ModuleCat (ZMod 2)))).hom
    rw [braiding_tensorUnit_left, Category.assoc, Iso.inv_hom_id, Category.comp_id, unitors_equal]
  have hκ := TauCeti.NatChainComplex.cup_koszulBraidingHom (absolute X) (absolute X)
    (M := coeff) (N := coeff) (P := coeff) (ZMod 2) (diagonal X) (ρ_ coeff).hom h a b
  rw [hμ] at hκ
  have hH := TauCeti.ChainComplex.cup_eq_of_homotopy (k := ZMod 2)
    (diagonal X ≫ CupOne.swap X) (ρ_ coeff).hom (CupOne.homotopy X) q p n (by omega) b a
  exact hH.symm.trans (hκ.trans (sign_smul (p * q) _))

private def nativeCast (X : TopCat.{0}) {m n : ℕ} (h : m = n)
    (a : (native X).homology m) : (native X).homology n := h ▸ a

private theorem comparison_cast (X : TopCat.{0}) {m n : ℕ} (h : m = n)
    (a : cohomologyZMod2 X m) :
    cohomologyEquiv X n (CupUnit.absoluteCast X h a) = nativeCast X h (cohomologyEquiv X m a) := by
  subst n
  rfl

private theorem generic_cast (X : TopCat.{0}) (p q n : ℕ) (h : p + q = n)
    (a : (native X).homology p) (b : (native X).homology q) :
    nativeCast X h (genericCup X p q (p + q) rfl a b) = genericCup X p q n h a b := by
  subst n
  rfl

/-- Commutativity of the actual project cup in every degree, including degree zero. -/
theorem comm (X : TopCat.{0}) (p q : ℕ)
    (a : cohomologyZMod2 X p) (b : cohomologyZMod2 X q) :
    CupUnit.absoluteCast X (Nat.add_comm q p) (cupZMod2 b a) = cupZMod2 a b := by
  apply (cohomologyEquiv X (p + q)).injective
  have hab := (PoolCupComparison.cohomology_comparison X p q a b).trans
    (singularCup_generic X p q (p + q) rfl (cohomologyEquiv X p a) (cohomologyEquiv X q b))
  have hba := (PoolCupComparison.cohomology_comparison X q p b a).trans
    (singularCup_generic X q p (q + p) rfl (cohomologyEquiv X q b) (cohomologyEquiv X p a))
  calc
    cohomologyEquiv X (p + q) (CupUnit.absoluteCast X (Nat.add_comm q p) (cupZMod2 b a)) =
        nativeCast X (Nat.add_comm q p) (cohomologyEquiv X (q + p) (cupZMod2 b a)) :=
      comparison_cast X (Nat.add_comm q p) (cupZMod2 b a)
    _ = nativeCast X (Nat.add_comm q p)
        (genericCup X q p (q + p) rfl (cohomologyEquiv X q b) (cohomologyEquiv X p a)) :=
      congrArg (nativeCast X (Nat.add_comm q p)) hba
    _ = genericCup X q p (p + q) (Nat.add_comm q p) (cohomologyEquiv X q b) (cohomologyEquiv X p a) :=
      generic_cast X q p (p + q) (Nat.add_comm q p) _ _
    _ = genericCup X p q (p + q) rfl (cohomologyEquiv X p a) (cohomologyEquiv X q b) :=
      generic_comm X p q (p + q) rfl _ _
    _ = cohomologyEquiv X (p + q) (cupZMod2 a b) := hab.symm


end
end Finsler.CupCommutativity
