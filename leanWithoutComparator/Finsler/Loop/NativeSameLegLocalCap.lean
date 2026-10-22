module

public import Finsler.Loop.NativeSameLegThomPrimitive
public import Finsler.Loop.SupportedExactThomCap
public import Finsler.Loop.SupportedCapCochainCongruence
public import Finsler.Topology.SelfCutEndpoints

/-! The ACTUAL source-local first normalized Thom cap on each same-leg
family is exact after every genuine closed neighborhood output cochain.
The primitive cap uses the coherent transported primitive and the SAME
source-local cover/subdivision. Its seam pullback is literally zero.
Comparison to the original ambient cut remains explicit and separate. -/
@[expose] public section
namespace Finsler.NativeSameLegLocalCap
open CategoryTheory CategoryTheory.Limits SphereOddDegree AlgebraicTopology
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.MeridianLoopFamily Finsler.CochainComparison
open Finsler.SameMeridianTransverseEscape Finsler.SupportedCapNaturality
open Finsler.NativeSameLegThomPrimitive
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

def exterior {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) (isLong : Bool) (ρ : ℝ) : Set (localSpace P v₀ k) :=
  family P v₀ k isLong ⁻¹' SupportedSelfCut.exterior n ρ

def near {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) (isLong : Bool) (r : ℝ) : Set (localSpace P v₀ k) :=
  family P v₀ k isLong ⁻¹' SupportedSelfCut.neighborhood n r

theorem exterior_open {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) (isLong : Bool) (ρ : ℝ) :
    IsOpen (exterior P v₀ k isLong ρ) :=
  (SupportedSelfCut.exterior_open n ρ).preimage (family P v₀ k isLong).hom.continuous

theorem near_open {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) (isLong : Bool) (r : ℝ) :
    IsOpen (near P v₀ k isLong r) :=
  (SupportedSelfCut.neighborhood_open n r).preimage (family P v₀ k isLong).hom.continuous

theorem cover {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) (isLong : Bool) {ρ r : ℝ} (hρr : ρ < r) :
    exterior P v₀ k isLong ρ ∪ near P v₀ k isLong r = Set.univ := by
  change _ ⁻¹' SupportedSelfCut.exterior n ρ ∪ _ ⁻¹' SupportedSelfCut.neighborhood n r = _
  rw [← Set.preimage_union, SupportedSelfCut.cover n hρr, Set.preimage_univ]

def cocycle (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (k : Fin 3) (isLong : Bool) {ρ : ℝ} (hρ : 0 < ρ) :=
  cochainPullback (family P v₀ k isLong) (m + 1) (NormalizedSelfCut.cocycle (m + 1) (by omega) hρ)

theorem cocycle_supported (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (k : Fin 3) (isLong : Bool)
    {ρ : ℝ} (hρ : 0 < ρ) :
    cochainPullback (SupportedCap.subspaceMap (localSpace P v₀ k) (exterior P v₀ k isLong ρ)) (m + 1)
      (cocycle m P v₀ k isLong hρ) = 0 :=
  pullback_support (family P v₀ k isLong) _ _ (fun _ h => h) (m + 1) _
    (NormalizedSelfCut.cocycle_supported (m + 1) (by omega) hρ)

theorem primitive_supported (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (k : Fin 3) (isLong : Bool)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    cochainPullback (SupportedCap.subspaceMap (localSpace P v₀ k) (exterior P v₀ k isLong ρ)) m
      (primitive (by omega) P v₀ k isLong hρ hρ1) = 0 :=
  primitive_far_family_zero (by omega) P v₀ k isLong hρ hρ1 _ (fun z => z.property.le)

theorem thom_boundary (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (k : Fin 3) (isLong : Bool)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    cochainCoboundary (ZMod 2) (localSpace P v₀ k) m (primitive (by omega) P v₀ k isLong hρ hρ1) =
      cocycle m P v₀ k isLong hρ :=
  NativeSameLegThomPrimitive.primitive_d (by omega) P v₀ k isLong hρ hρ1

def cochain (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (k : Fin 3) (isLong : Bool)
    {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (q : ℕ)
    (ψ : singularCochainGroup (ZMod 2) (TopCat.of (near P v₀ k isLong r)) q) :=
  SupportedCap.cut (localSpace P v₀ k) (exterior P v₀ k isLong ρ) (near P v₀ k isLong r)
    (exterior_open P v₀ k isLong ρ) (near_open P v₀ k isLong r) (cover P v₀ k isLong hρr)
    (m + 1) q (m + q + 1) (by omega) (cocycle m P v₀ k isLong hρ)
    (cocycle_supported m P v₀ k isLong hρ) ≫ ψ

def correction (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (k : Fin 3) (isLong : Bool)
    {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hρ1 : ρ ≤ 1) (q : ℕ)
    (ψ : singularCochainGroup (ZMod 2) (TopCat.of (near P v₀ k isLong r)) q) :=
  SupportedExactThomCap.correction (localSpace P v₀ k) (exterior P v₀ k isLong ρ) (near P v₀ k isLong r)
    (exterior_open P v₀ k isLong ρ) (near_open P v₀ k isLong r) (cover P v₀ k isLong hρr)
    m (primitive (by omega) P v₀ k isLong hρ hρ1) (primitive_supported m hm P v₀ k isLong hρ hρ1) q ψ

theorem correction_boundary (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (k : Fin 3) (isLong : Bool)
    {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hρ1 : ρ ≤ 1) (q : ℕ)
    (ψ : singularCochainGroup (ZMod 2) (TopCat.of (near P v₀ k isLong r)) q)
    (hψ : cochainCoboundary (ZMod 2) (TopCat.of (near P v₀ k isLong r)) q ψ = 0) :
    cochainCoboundary (ZMod 2) (localSpace P v₀ k) (m + q) (correction m hm P v₀ k isLong hρ hρr hρ1 q ψ) =
      cochain m P v₀ k isLong hρ hρr q ψ := by
  have he := SupportedExactThomCap.correction_boundary (localSpace P v₀ k) (exterior P v₀ k isLong ρ) (near P v₀ k isLong r)
    (exterior_open P v₀ k isLong ρ) (near_open P v₀ k isLong r) (cover P v₀ k isLong hρr)
    m (primitive (by omega) P v₀ k isLong hρ hρ1) (primitive_supported m hm P v₀ k isLong hρ hρ1) q ψ hψ
  dsimp only [SupportedExactThomCap.cochain] at he
  have hc := SupportedCapCochainCongruence.cut_eq (localSpace P v₀ k) (exterior P v₀ k isLong ρ) (near P v₀ k isLong r)
    (exterior_open P v₀ k isLong ρ) (near_open P v₀ k isLong r) (cover P v₀ k isLong hρr)
    (m + 1) q (m + q + 1) (by omega) _ _
    (SupportedExactThomCap.coboundary_supported (localSpace P v₀ k) (exterior P v₀ k isLong ρ) m
      (primitive (by omega) P v₀ k isLong hρ hρ1) (primitive_supported m hm P v₀ k isLong hρ hρ1))
    (cocycle_supported m P v₀ k isLong hρ) (thom_boundary m hm P v₀ k isLong hρ hρ1)
  exact he.trans (congrArg (fun a => a ≫ ψ) hc)

theorem cochain_closed (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (k : Fin 3) (isLong : Bool)
    {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hρ1 : ρ ≤ 1) (q : ℕ)
    (ψ : singularCochainGroup (ZMod 2) (TopCat.of (near P v₀ k isLong r)) q)
    (hψ : cochainCoboundary (ZMod 2) (TopCat.of (near P v₀ k isLong r)) q ψ = 0) :
    cochainCoboundary (ZMod 2) (localSpace P v₀ k) (m + q + 1) (cochain m P v₀ k isLong hρ hρr q ψ) = 0 := by
  rw [← correction_boundary m hm P v₀ k isLong hρ hρr hρ1 q ψ hψ]
  exact CochainClass.closed_boundary (cochainCxZMod2 (localSpace P v₀ k)) (m + q) (m + q + 1) _

theorem cochain_class_zero (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (k : Fin 3) (isLong : Bool)
    {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hρ1 : ρ ≤ 1) (q : ℕ)
    (ψ : singularCochainGroup (ZMod 2) (TopCat.of (near P v₀ k isLong r)) q)
    (hψ : cochainCoboundary (ZMod 2) (TopCat.of (near P v₀ k isLong r)) q ψ = 0) :
    CochainClass.classOf (cochainCxZMod2 (localSpace P v₀ k)) (m + q + 1) (cochain m P v₀ k isLong hρ hρr q ψ)
      (cochain_closed m hm P v₀ k isLong hρ hρr hρ1 q ψ hψ) = 0 := by
  have he := correction_boundary m hm P v₀ k isLong hρ hρr hρ1 q ψ hψ
  have hb := CochainClass.closed_boundary (cochainCxZMod2 (localSpace P v₀ k)) (m + q) (m + q + 1)
    (correction m hm P v₀ k isLong hρ hρr hρ1 q ψ)
  exact (CochainClass.classOf_congr (cochainCxZMod2 (localSpace P v₀ k)) (m + q + 1) he.symm _ hb).trans
    (CochainClass.classOf_boundary (cochainCxZMod2 (localSpace P v₀ k)) (m + q) (m + q + 1) _ hb)

theorem correction_seam_zero (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (k : Fin 3) (isLong : Bool)
    {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hρ1 : ρ ≤ 1) (q : ℕ)
    (ψ : singularCochainGroup (ZMod 2) (TopCat.of (near P v₀ k isLong r)) q) :
    cochainPullback (SupportedCap.subspaceMap (localSpace P v₀ k) (seam P v₀ k isLong)) (m + q)
      (correction m hm P v₀ k isLong hρ hρr hρ1 q ψ) = 0 := by
  have hz := SelfCutEndpoints.cut_map_zero (exterior P v₀ k isLong ρ) (near P v₀ k isLong r) (seam P v₀ k isLong)
    (exterior_open P v₀ k isLong ρ) (near_open P v₀ k isLong r) (cover P v₀ k isLong hρr) m q
    (primitive (by omega) P v₀ k isLong hρ hρ1) (primitive_supported m hm P v₀ k isLong hρ hρ1)
    (primitive_seam_family_zero (by omega) P v₀ k isLong hρ hρ1 _ (fun z => z.property))
    (SupportedCap.subspaceMap (localSpace P v₀ k) (seam P v₀ k isLong)) (fun z => z.property)
  change (push (SupportedCap.subspaceMap (localSpace P v₀ k) (seam P v₀ k isLong))).f (m + q) ≫
    (_ ≫ ψ) = 0
  rw [← Category.assoc, hz, zero_comp]

end
end Finsler.NativeSameLegLocalCap
