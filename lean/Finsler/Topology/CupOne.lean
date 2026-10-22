module

public import Finsler.Topology.AWInterchange
public import Finsler.Topology.RelativeCap

/-! A natural cup-one operation in the actual F₂ singular-cochain model. -/

@[expose] public section

namespace Finsler.CupOne

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology
open SphereOddDegree Finsler.CochainComparison Finsler.RelativeCap

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

abbrev tensor (X : TopCat.{0}) := HomologicalComplex.tensorObj (absolute X) (absolute X)
abbrev swap (X : TopCat.{0}) := TauCeti.NatChainComplex.koszulBraidingHom (absolute X) (absolute X)

private theorem pairing_swap : (β_ coeff coeff).hom ≫ (ρ_ coeff).hom = (ρ_ coeff).hom := by
  change (β_ (𝟙_ (ModuleCat (ZMod 2))) (𝟙_ (ModuleCat (ZMod 2)))).hom ≫
      (ρ_ (𝟙_ (ModuleCat (ZMod 2)))).hom = (ρ_ (𝟙_ (ModuleCat (ZMod 2)))).hom
  rw [braiding_tensorUnit_left, Category.assoc, Iso.inv_hom_id, Category.comp_id, unitors_equal]

def homotopy (X : TopCat.{0}) : Homotopy (diagonal X ≫ swap X) (diagonal X) :=
  (AWInterchange.alexanderWhitneyDiagonalKoszulBraidingHomotopy X
    (λ_ (𝟙_ (ModuleCat (ZMod 2)))).inv).trans
    (Homotopy.ofEq (congrArg (X.alexanderWhitneyDiagonal)
      (show (λ_ (𝟙_ (ModuleCat (ZMod 2)))).inv ≫
          (β_ (𝟙_ (ModuleCat (ZMod 2))) (𝟙_ (ModuleCat (ZMod 2)))).hom =
        (λ_ (𝟙_ (ModuleCat (ZMod 2)))).inv by
          rw [braiding_tensorUnit_left, Iso.inv_hom_id_assoc, unitors_inv_equal])))

private theorem homotopy_hom (X : TopCat.{0}) (i j : ℕ) :
    (homotopy X).hom i j =
      (AWInterchange.alexanderWhitneyDiagonalKoszulBraidingHomotopy X
        (λ_ (𝟙_ (ModuleCat (ZMod 2)))).inv).hom i j := by
  simp only [homotopy, Homotopy.trans_hom, Homotopy.ofEq_hom, Pi.zero_apply, add_zero]

private theorem sign_smul {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (p : ℕ) (v : V) : ((-1 : ℤ) ^ p) • v = v := by
  have hs : (((-1 : ℤ) ^ p : ℤ) : ZMod 2) = 1 := by
    simp only [Int.cast_pow, Int.cast_neg, Int.cast_one, ZMod.neg_eq_self_mod_two, one_pow]
  rw [← Int.cast_smul_eq_zsmul (ZMod 2), hs, one_smul]

abbrev cup (X : TopCat.{0}) (p q n : ℕ) (h : p + q = n)
    (φ : singularCochainGroup (ZMod 2) X p) (ψ : singularCochainGroup (ZMod 2) X q) :
    singularCochainGroup (ZMod 2) X n :=
  TauCeti.ChainComplex.cupCochain (A := absolute X) (B := absolute X)
    (M := coeff) (N := coeff) (P := coeff) (ZMod 2) (diagonal X) (ρ_ coeff).hom p q n h φ ψ

def cupOne (X : TopCat.{0}) (p q n : ℕ) (_ : p + q = n + 1)
    (φ : singularCochainGroup (ZMod 2) X p) (ψ : singularCochainGroup (ZMod 2) X q) :
    singularCochainGroup (ZMod 2) X n :=
  (homotopy X).hom n (n + 1) ≫
    TauCeti.ChainComplex.tensorCochain (ρ_ coeff).hom ψ φ (n + 1)

/-- The products in the homotopy formula are the project's existing actual cup products. -/
theorem cup_comparison (X : TopCat.{0}) (p q : ℕ)
    (φ : singularCochainGroup (ZMod 2) X p) (ψ : singularCochainGroup (ZMod 2) X q) :
    cup X p q (p + q) rfl φ ψ = cochainCup p q φ ψ := by
  exact PoolCupComparison.cochain_comparison X p q φ ψ

private theorem swap_cup (X : TopCat.{0}) (p q n : ℕ) (h : p + q = n)
    (φ : singularCochainGroup (ZMod 2) X p) (ψ : singularCochainGroup (ZMod 2) X q) :
    (diagonal X ≫ swap X).f n ≫
        TauCeti.ChainComplex.tensorCochain (ρ_ coeff).hom ψ φ n = cup X p q n h φ ψ := by
  have hs := TauCeti.NatChainComplex.cupCochain_koszulBraidingHom (absolute X) (absolute X)
    (M := coeff) (N := coeff) (P := coeff) (ZMod 2) (diagonal X) (ρ_ coeff).hom h φ ψ
  rw [pairing_swap] at hs
  rw [TauCeti.ChainComplex.cupCochain_apply] at hs
  exact hs.trans (sign_smul (p * q) _)

/-- The full cochain homotopy identity, with both coboundary terms retained. -/
theorem boundary_formula (X : TopCat.{0}) (p q n : ℕ) (h : p + q = n + 1)
    (φ : singularCochainGroup (ZMod 2) X p) (ψ : singularCochainGroup (ZMod 2) X q) :
    cochainCoboundary (ZMod 2) X n (cupOne X p q n h φ ψ) +
        cupOne X (p + 1) q (n + 1) (by omega)
          (cochainCoboundary (ZMod 2) X p φ) ψ +
        cupOne X p (q + 1) (n + 1) (by omega)
          φ (cochainCoboundary (ZMod 2) X q ψ) =
      cup X p q (n + 1) h φ ψ - cup X q p (n + 1) (by omega) ψ φ := by
  let t := TauCeti.ChainComplex.tensorCochain (A := absolute X) (B := absolute X)
    (ρ_ coeff).hom ψ φ (n + 1)
  have ht : (homotopy X).hom (n + 1) (n + 2) ≫ ((tensor X).d (n + 2) (n + 1) ≫ t) =
      cupOne X p (q + 1) (n + 1) (by omega) φ (cochainCoboundary (ZMod 2) X q ψ) +
        cupOne X (p + 1) q (n + 1) (by omega) (cochainCoboundary (ZMod 2) X p φ) ψ := by
    have hd := TauCeti.ChainComplex.d_comp_tensorCochain (A := absolute X) (B := absolute X)
      (ρ_ coeff).hom ψ φ (n + 1)
    change (tensor X).d (n + 2) (n + 1) ≫ t = _ at hd
    rw [hd, Preadditive.comp_add, Preadditive.comp_zsmul, sign_smul]
    rfl
  have hb := congrArg (· ≫ t) ((homotopy X).comm (n + 1))
  simp only [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex,
    Preadditive.add_comp, Category.assoc] at hb
  have hr : cup X q p (n + 1) (by omega) ψ φ = (diagonal X).f (n + 1) ≫ t :=
    TauCeti.ChainComplex.cupCochain_apply (diagonal X) (ρ_ coeff).hom q p (n + 1) (by omega) ψ φ
  rw [← hr] at hb
  have hs := swap_cup X p q (n + 1) h φ ψ
  have he : cup X p q (n + 1) h φ ψ =
      cochainCoboundary (ZMod 2) X n (cupOne X p q n h φ ψ) +
        (cupOne X p (q + 1) (n + 1) (by omega) φ (cochainCoboundary (ZMod 2) X q ψ) +
          cupOne X (p + 1) q (n + 1) (by omega) (cochainCoboundary (ZMod 2) X p φ) ψ) +
        cup X q p (n + 1) (by omega) ψ φ := by
    exact hs.symm.trans (hb.trans (congrArg
      (fun z : singularCochainGroup (ZMod 2) X (n + 1) =>
        cochainCoboundary (ZMod 2) X n (cupOne X p q n h φ ψ) + z +
        cup X q p (n + 1) (by omega) ψ φ) ht))
  apply (eq_sub_iff_add_eq).mpr
  rw [he]
  abel

theorem zero_left (X : TopCat.{0}) (p q n : ℕ) (h : p + q = n + 1)
    (ψ : singularCochainGroup (ZMod 2) X q) : cupOne X p q n h 0 ψ = 0 := by
  have ht := TauCeti.ChainComplex.tensorCochain_smul_right (k := ZMod 2)
    (A := absolute X) (B := absolute X) (ρ_ coeff).hom (0 : ZMod 2) ψ
      (0 : singularCochainGroup (ZMod 2) X p) (n + 1)
  simpa only [zero_smul, cupOne, comp_zero] using
    congrArg (fun z => (homotopy X).hom n (n + 1) ≫ z) ht

theorem zero_right (X : TopCat.{0}) (p q n : ℕ) (h : p + q = n + 1)
    (φ : singularCochainGroup (ZMod 2) X p) : cupOne X p q n h φ 0 = 0 := by
  have ht := TauCeti.ChainComplex.tensorCochain_smul_left (k := ZMod 2)
    (A := absolute X) (B := absolute X) (ρ_ coeff).hom (0 : ZMod 2)
      (0 : singularCochainGroup (ZMod 2) X q) φ (n + 1)
  simpa only [zero_smul, cupOne, comp_zero] using
    congrArg (fun z => (homotopy X).hom n (n + 1) ≫ z) ht

/-- Pullback commutes with cup-one at the level of actual cochains. -/
theorem naturality {X Y : TopCat.{0}} (f : X ⟶ Y) (p q n : ℕ) (h : p + q = n + 1)
    (φ : singularCochainGroup (ZMod 2) Y p) (ψ : singularCochainGroup (ZMod 2) Y q) :
    cochainPullback f n (cupOne Y p q n h φ ψ) =
      cupOne X p q n h (cochainPullback f p φ) (cochainPullback f q ψ) := by
  let sf := SSet.chainComplexMap (TopCat.toSSet.map f) coeff
  let t := TauCeti.ChainComplex.tensorCochain (A := absolute Y) (B := absolute Y)
    (ρ_ coeff).hom ψ φ (n + 1)
  have hh : sf.f n ≫ (homotopy Y).hom n (n + 1) =
      (homotopy X).hom n (n + 1) ≫ (HomologicalComplex.tensorHom sf sf).f (n + 1) := by
    rw [homotopy_hom, homotopy_hom]
    exact AWInterchange.diagonal_hom_naturality f
      (λ_ (𝟙_ (ModuleCat (ZMod 2)))).inv n (n + 1)
  have ht : (HomologicalComplex.tensorHom sf sf).f (n + 1) ≫ t =
      TauCeti.ChainComplex.tensorCochain (A := absolute X) (B := absolute X) (ρ_ coeff).hom
        (cochainPullback f q ψ) (cochainPullback f p φ) (n + 1) :=
    TauCeti.ChainComplex.tensorHom_f_comp_tensorCochain (ρ_ coeff).hom sf sf ψ φ (n + 1)
  change sf.f n ≫ ((homotopy Y).hom n (n + 1) ≫ t) = _
  exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ t) hh)).trans
    ((Category.assoc _ _ _).trans (congrArg ((homotopy X).hom n (n + 1) ≫ ·) ht))

/-- Restriction of cup-one vanishes wherever either input cochain restricts to zero. -/
theorem restriction_zero {X Y : TopCat.{0}} (f : X ⟶ Y)
    (p q n : ℕ) (h : p + q = n + 1)
    (φ : singularCochainGroup (ZMod 2) Y p) (ψ : singularCochainGroup (ZMod 2) Y q)
    (hz : cochainPullback f p φ = 0 ∨ cochainPullback f q ψ = 0) :
    cochainPullback f n (cupOne Y p q n h φ ψ) = 0 := by
  rw [naturality]
  rcases hz with hz | hz
  · rw [hz, zero_left]
  · rw [hz, zero_right]

theorem boundary_cocycles (X : TopCat.{0}) (p q n : ℕ) (h : p + q = n + 1)
    (φ : singularCochainGroup (ZMod 2) X p) (ψ : singularCochainGroup (ZMod 2) X q)
    (hφ : cochainCoboundary (ZMod 2) X p φ = 0)
    (hψ : cochainCoboundary (ZMod 2) X q ψ = 0) :
    cochainCoboundary (ZMod 2) X n (cupOne X p q n h φ ψ) =
      cup X p q (n + 1) h φ ψ - cup X q p (n + 1) (by omega) ψ φ := by
  have hd := boundary_formula X p q n h φ ψ
  rw [hφ, hψ, zero_left, zero_right, add_zero, add_zero] at hd
  exact hd


end
end Finsler.CupOne
