module

public import Finsler.Residual.UFData
public import Finsler.Residual.SecondNaturality
public import Finsler.Loop.StrictLengthProductFullNaturality

/-! Uniform filling in the low degrees (Claude, UF prototype).

For a globally null class x of low degree q at length a, the product S • x with a lift of a high
Theta power is a globally null class of high degree, so it dies after the uniform extra length D
(`UFData.uf_high`); by naturality of the product in the second factor the product of S with the
enlarged class x' = enl_{a → a + D} x is already zero. The S-first identity at the length a + D
(left unit, unit of the cut of S, filtered interchange) writes x' as the product-then-cut of
S × x', which vanishes since its product does. Hence x dies after a uniform extra length. -/

@[expose] public section

namespace Finsler.UFLow

open CategoryTheory AlgebraicTopology SphereOddDegree MonoidalCategory
open Finsler.SphereGeometry Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.MeridianLoopFamily Finsler.StrictLengthEnergyBridge Finsler.SplitPairHomologyKernel
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.FarNormalizedDiagonalCap

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 3000000

theorem cross_cast (X Y : TopCat.{0}) (i j N N' : ℕ) (h : i + j = N) (h' : i + j = N') (e : N = N')
    (x : PoolCap.homology X i) (y : PoolCap.homology Y j) :
    (eqToHom (congrArg (fun k => (chains (TopCat.of (X × Y))).homology k) e)).hom
      (FilteredBilinearLoopProduct.cross X Y i j N h x y) =
      FilteredBilinearLoopProduct.cross X Y i j N' h' x y := by
  subst e
  rfl

variable {m : ℕ} (F : ReversibleMetric (m + 1))

theorem cross_cast_chains {a b : ℝ} (i j N N' : ℕ) (h : i + j = N) (h' : i + j = N') (e : N = N')
    (x : PoolCap.homology (lengthSpace F a) i) (y : PoolCap.homology (lengthSpace F b) j) :
    (eqToHom (congrArg (fun k => (chains (StrictLengthLoopProduct.pairSpace F a b)).homology k) e)).hom
      (FilteredBilinearLoopProduct.cross (lengthSpace F a) (lengthSpace F b) i j N h x y) =
      FilteredBilinearLoopProduct.cross (lengthSpace F a) (lengthSpace F b) i j N' h' x y := by
  subst e
  rfl

/-- The product-then-cut operation vanishes on a cross product whose product vanishes. -/
theorem op_zero (hm : 1 ≤ m) {a b A L ε : ℝ} (hab : a + b < A) (hε : 0 < ε) (p : ℕ)
    (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p)
    (hT : cochainCoboundary (ZMod 2) (Loops (m + 1)) p T = 0)
    (hs : cochainPullback (SupportedCap.subspaceMap (Loops (m + 1)) (SelfCutOscillation.short F L)) p T = 0)
    (i j k : ℕ) (hij : i + j = ((m + 1) + (m + p)) + k) (hij' : i + j = (m + 1) + ((m + p) + k))
    (x : PoolCap.homology (lengthSpace F a) i) (y : PoolCap.homology (lengthSpace F b) j)
    (h0 : StrictLengthLoopProduct.product F (dim_pos m) hε i j ((m + p) + k) hij' x y = 0) :
    ((CanonicalAfterLengthProduct.operation F hab hε p T hT hs).homology k).hom
      (FilteredBilinearLoopProduct.cross (lengthSpace F a) (lengthSpace F b) i j
        (((m + 1) + (m + p)) + k) hij x y) = 0 := by
  rw [CanonicalAfterLengthProduct.operation, DegreeLoweringHomology.Map.post_homology,
    DegreeLoweringComposition.homology]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  erw [cross_cast_chains F i j _ _ hij hij' (Nat.add_assoc (m + 1) (m + p) k)]
  rw [OriginalLengthProductBudget.operation, DegreeLoweringHomology.Map.post_homology]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [← StrictLengthProductCompatibility.chain_apply F (dim_pos m) hε i j ((m + p) + k) hij' x y, h0]
  simp only [map_zero]

/-- **Killing a low-degree class** through a high-degree product. -/
theorem low_kill (hm : 2 ≤ m) {ε : ℝ} (hε : 0 < ε) (r : ℕ) (d : UFHigh.CutData m F ε hε r)
    {a : ℝ} (ha : 0 < a) (q : ℕ) (x : PoolCap.homology (lengthSpace F a) q)
    (hx : (homologyPushZMod2 (LengthFilteredLoopRotation.full F a) q).hom x = 0)
    {Dh : ℝ} (hDh : 0 ≤ Dh)
    (huf : ∀ (a' : ℝ) (_ : 0 < a')
      (y : PoolCap.homology (lengthSpace F a') ((m + NativeGHPowers.degree m r) + q)),
      (homologyPushZMod2 (LengthFilteredLoopRotation.full F a') _).hom y = 0 →
        ∀ h : a' ≤ a' + Dh, UFCore.enl F h _ y = 0)
    (M : ℝ) (hM1 : d.B + ((a + Dh) + ε) ≤ M) (hM2 : ((a + Dh) + d.s + ε) - d.L + 5 * ε ≤ M) :
    UFCore.enl F (by linarith [d.hB, hε, hDh] : a ≤ M) q x = 0 := by
  have hij : ((m + NativeGHPowers.degree m r) + (m + 1)) + q =
      (m + 1) + ((m + NativeGHPowers.degree m r) + q) := by omega
  set P := StrictLengthLoopProduct.product F (dim_pos m) hε ((m + NativeGHPowers.degree m r) + (m + 1)) q
    ((m + NativeGHPowers.degree m r) + q) hij d.S x with hP
  -- the product is globally null
  have hPn : (homologyPushZMod2 (LengthFilteredLoopRotation.full F (d.s + (a + ε))) _).hom P = 0 := by
    obtain ⟨b, hab, h0b, hb⟩ := StrictLengthHomologyStabilization.exists_equal F q x
      (0 : homologyZMod2 (lengthSpace F a) q) (by rw [hx, map_zero])
    rw [map_zero] at hb
    have hfn := StrictLengthProductFullNaturality.product_naturality F d.hs0 d.hs0 ha (ha.trans_le hab) hε hε
      le_rfl hab (dim_pos m) _ _ _ hij d.S x
    erw [hb, map_zero] at hfn
    exact hfn.symm.trans (map_zero _)
  -- it dies after Dh
  have hPd := huf _ (by linarith [d.hs0]) P hPn (by linarith)
  -- the product with the enlarged class vanishes
  have hDa : a ≤ a + Dh := by linarith
  have hx'0 : StrictLengthLoopProduct.product F (dim_pos m) hε ((m + NativeGHPowers.degree m r) + (m + 1)) q
      ((m + NativeGHPowers.degree m r) + q) hij d.S (UFCore.enl F hDa q x) = 0 := by
    have hN := StrictLengthProductSecondNaturality.product_naturality F d.hs0 ha (by linarith) hε hDa
      (dim_pos m) _ _ _ hij d.S x
    erw [hN]
    exact UFBLF.enl_zero_mono m F (by linarith) (by linarith : d.s + (a + ε) + Dh ≤ d.s + ((a + Dh) + ε))
      _ P hPd
  -- the S-first identity at the length a + Dh
  set x' := UFCore.enl F hDa q x with hx'
  have hba : d.s + (a + Dh) < (a + Dh) + d.s + ε := by linarith
  have hopz := op_zero F (by omega) hba hε _ d.T d.hT d.hsh _ q q (by omega) hij d.S x' hx'0
  have hI := FilteredCanonicalInterchange.value F hε (by omega) (NativeGHPowers.degree m r) d.L d.s (a + Dh)
    ((a + Dh) + d.s + ε) d.T d.hT d.hsh hba (m + 1) q q (by omega) (by omega) d.S x'
  rw [hopz] at hI
  -- hI : 0 = product_budget (cut S) x'
  have h2 : UFCore.enl F (by linarith : ((a + Dh) + d.s + ε) - d.L + 5 * ε ≤ M) q
      (StrictLengthProductBudget.product F (L := d.L) hba hε (dim_pos m) (m + 1) q q (by omega)
        (((FilteredPrismSelfCut.canonicalOperation m (NativeGHPowers.degree m r) F hε d.T d.hT d.hsh
          (a := d.s)).homology (m + 1)).hom d.S) x') = UFCore.enl F (by linarith [d.hB, hε] : a + Dh ≤ M) q x' := by
    rw [StrictLengthProductBudget.product_apply]
    erw [UFCore.enl_outputInclusion F hba hε hM2]
    have hle : (d.s - d.L + 3 * ε) + ((a + Dh) + ε) ≤ d.B + ((a + Dh) + ε) := by linarith [d.hBs]
    rw [← UFCore.enl_enl F hle hM1]
    have hN := StrictLengthProductFirstNaturality.product_naturality F d.hsa d.hB (by linarith) hε d.hBs
      (dim_pos m) (m + 1) q q (by omega)
      (((FilteredPrismSelfCut.canonicalOperation m (NativeGHPowers.degree m r) F hε d.T d.hT d.hsh
        (a := d.s)).homology (m + 1)).hom d.S) x'
    erw [← hN, d.hunit, StrictLengthFilteredUnit.left_unit F (by omega) d.hB (by linarith) hε q x',
      UFCore.enl_enl]
  rw [← hI, map_zero] at h2
  rw [hx', UFCore.enl_enl] at h2
  exact h2.symm

/-- **Uniform filling (paper Theorem 6.1) in every degree** with finitely many prime closed geodesic
images: a class of a length sublevel t_a dying in the loop space dies in t_{a + D}. -/
theorem uf_all (hm : 2 ≤ m) (hfin : (Finsler.Geodesics.primeImages F).Finite) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (a : ℝ) (_ha : 0 < a) (q : ℕ) (x : PoolCap.homology (lengthSpace F a) q),
      (homologyPushZMod2 (LengthFilteredLoopRotation.full F a) q).hom x = 0 →
        ∀ h : a ≤ a + D, UFCore.enl F h q x = 0 := by
  obtain ⟨Dh, hDh, q₁, hUF⟩ := UFData.uf_high m F hm hfin
  obtain ⟨P, ⟨v₀⟩⟩ := HRBridge.exists_point m
  obtain ⟨C, hC⟩ := GHSlope.gh_exact_rate m hm F P v₀ hfin
  have hε : (0 : ℝ) < 1 := one_pos
  obtain ⟨data, Δ, Bs, hΔ, hBs, hL⟩ := UFData.exists_data m hm F P v₀ hfin hε (fun r => (hC r).1)
  have hΔ0 : -3 < Δ := by
    have := (data 0).hsa
    linarith [hΔ 0]
  have hBs0 : 0 < Bs := (data 0).hB.trans_le (hBs 0)
  refine ⟨Dh + max (Bs + 1) (Δ + 6), by
    have := le_max_left (Bs + 1) (Δ + 6); linarith, fun a ha q x hx h => ?_⟩
  by_cases hq : q₁ ≤ q
  · have h1 := hUF a ha q hq x hx (by linarith)
    exact UFBLF.enl_zero_mono m F _ (by have := le_max_left (Bs + 1) (Δ + 6); linarith) q x h1
  · have hr : q₁ ≤ (m + NativeGHPowers.degree m q₁) + q := by
      rw [NativeGHPowers.degree_formula]
      nlinarith
    have hk := low_kill F hm hε q₁ (data q₁) ha q x hx hDh
      (fun a' ha' y hy h' => hUF a' ha' _ (by omega) y hy h')
      (a + (Dh + max (Bs + 1) (Δ + 6)))
      (by have := hBs q₁; have := le_max_left (Bs + 1) (Δ + 6); linarith)
      (by have := hΔ q₁; have := le_max_right (Bs + 1) (Δ + 6); linarith)
    exact hk

end

end Finsler.UFLow
