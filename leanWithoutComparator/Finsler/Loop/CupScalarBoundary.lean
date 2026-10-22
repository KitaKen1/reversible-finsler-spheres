module

public import Finsler.Loop.CupCapOrder

/-! Transport an actual scalar primitive through either retained cup
factor. The full cochain differential is used and the F2 sign is proved. -/
@[expose] public section
namespace Finsler.CupScalarBoundary
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 900000

theorem sub_left (X : TopCat.{0}) (p q N : ℕ) (h : p + q = N)
    (T U : singularCochainGroup (ZMod 2) X p) (B : singularCochainGroup (ZMod 2) X q) :
    CupOne.cup X p q N h (T - U) B = CupOne.cup X p q N h T B - CupOne.cup X p q N h U B :=
  map_sub ((TauCeti.ChainComplex.cupCochain (ZMod 2) (Finsler.RelativeCap.diagonal X)
    (ρ_ coeff).hom p q N h).flip B) T U

theorem sub_right (X : TopCat.{0}) (p q N : ℕ) (h : p + q = N)
    (T : singularCochainGroup (ZMod 2) X p) (B C : singularCochainGroup (ZMod 2) X q) :
    CupOne.cup X p q N h T (B - C) = CupOne.cup X p q N h T B - CupOne.cup X p q N h T C :=
  map_sub ((TauCeti.ChainComplex.cupCochain (ZMod 2) (Finsler.RelativeCap.diagonal X)
    (ρ_ coeff).hom p q N h) T) B C

theorem right_closed (X : TopCat.{0}) (p q N : ℕ) (h : p + q = N)
    (T : singularCochainGroup (ZMod 2) X p) (B : singularCochainGroup (ZMod 2) X q)
    (hB : cochainCoboundary (ZMod 2) X q B = 0) :
    cochainCoboundary (ZMod 2) X N (CupOne.cup X p q N h T B) =
      CupOne.cup X (p + 1) q (N + 1) (by omega) (cochainCoboundary (ZMod 2) X p T) B := by
  have hb := TauCeti.ChainComplex.d_comp_cupCochain (k := ZMod 2)
    (Finsler.RelativeCap.diagonal X) (ρ_ coeff).hom p q N h T B
  change cochainCoboundary (ZMod 2) X N (CupOne.cup X p q N h T B) =
    CupOne.cup X (p + 1) q (N + 1) (by omega) (cochainCoboundary (ZMod 2) X p T) B +
      ((-1 : ℤ) ^ p) • CupOne.cup X p (q + 1) (N + 1) (by omega) T
        (cochainCoboundary (ZMod 2) X q B) at hb
  rw [hB] at hb
  have hz : CupOne.cup X p (q + 1) (N + 1) (by omega) T 0 = 0 := map_zero _
  rw [hz, smul_zero, add_zero] at hb
  exact hb

theorem left_closed (X : TopCat.{0}) (p q N : ℕ) (h : p + q = N)
    (T : singularCochainGroup (ZMod 2) X p) (B : singularCochainGroup (ZMod 2) X q)
    (hT : cochainCoboundary (ZMod 2) X p T = 0) :
    cochainCoboundary (ZMod 2) X N (CupOne.cup X p q N h T B) =
      CupOne.cup X p (q + 1) (N + 1) (by omega) T (cochainCoboundary (ZMod 2) X q B) := by
  have hb := TauCeti.ChainComplex.d_comp_cupCochain (k := ZMod 2)
    (Finsler.RelativeCap.diagonal X) (ρ_ coeff).hom p q N h T B
  change cochainCoboundary (ZMod 2) X N (CupOne.cup X p q N h T B) =
    CupOne.cup X (p + 1) q (N + 1) (by omega) (cochainCoboundary (ZMod 2) X p T) B +
      ((-1 : ℤ) ^ p) • CupOne.cup X p (q + 1) (N + 1) (by omega) T
        (cochainCoboundary (ZMod 2) X q B) at hb
  rw [hT] at hb
  have hz : CupOne.cup X (p + 1) q (N + 1) (by omega) 0 B = 0 :=
    map_zero ((TauCeti.ChainComplex.cupCochain (ZMod 2) (Finsler.RelativeCap.diagonal X)
      (ρ_ coeff).hom (p + 1) q (N + 1) (by omega)).flip B)
  rw [hz, zero_add] at hb
  have hs : (((-1 : ℤ) ^ p : ℤ) : ZMod 2) = 1 := by
    simp only [Int.cast_pow, Int.cast_neg, Int.cast_one, ZMod.neg_eq_self_mod_two, one_pow]
  rw [← Int.cast_smul_eq_zsmul (ZMod 2), hs, one_smul] at hb
  exact hb

end
end Finsler.CupScalarBoundary
