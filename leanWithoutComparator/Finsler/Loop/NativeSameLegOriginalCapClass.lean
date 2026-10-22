module

public import Finsler.Loop.NativeSameLegLocalCap
public import Finsler.Loop.SupportedExactThomCapDegree

/-! Return from the source-local exact cap to the ORIGINAL ambient
supported cap via actual source-small naturality and the real
subdivision-prism cochain comparison. The original complete cut
cochain has ZERO absolute class on the actual local direction patch.
This is not yet a relative-face or global scalar vanishing theorem. -/
@[expose] public section
namespace Finsler.NativeSameLegOriginalCapClass
open CategoryTheory CategoryTheory.Limits SphereOddDegree AlgebraicTopology
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.MeridianLoopFamily Finsler.CochainComparison
open Finsler.SameMeridianTransverseEscape Finsler.SupportedCapNaturality
open Finsler.NativeSameLegThomPrimitive
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

def nearMap {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) (isLong : Bool) (r : ℝ) :
    TopCat.of (NativeSameLegLocalCap.near P v₀ k isLong r) ⟶ TopCat.of (SupportedSelfCut.neighborhood n r) :=
  restriction (family P v₀ k isLong) (NativeSameLegLocalCap.near P v₀ k isLong r)
    (SupportedSelfCut.neighborhood n r) (fun _ h => h)

def original (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (k : Fin 3) (isLong : Bool)
    {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (q : ℕ)
    (ψ : singularCochainGroup (ZMod 2) (TopCat.of (SupportedSelfCut.neighborhood (m + 1) r)) q) :=
  SupportedCapPullbackClass.original (family P v₀ k isLong)
    (SupportedSelfCut.exterior (m + 1) ρ) (SupportedSelfCut.neighborhood (m + 1) r)
    (SupportedSelfCut.exterior_open (m + 1) ρ) (SupportedSelfCut.neighborhood_open (m + 1) r)
    (SupportedSelfCut.cover (m + 1) hρr) (m + 1) q (NormalizedSelfCut.cocycle (m + 1) (by omega) hρ)
    (NormalizedSelfCut.cocycle_supported (m + 1) (by omega) hρ) ψ

theorem original_closed (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (k : Fin 3) (isLong : Bool)
    {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (q : ℕ)
    (ψ : singularCochainGroup (ZMod 2) (TopCat.of (SupportedSelfCut.neighborhood (m + 1) r)) q)
    (hψ : cochainCoboundary (ZMod 2) (TopCat.of (SupportedSelfCut.neighborhood (m + 1) r)) q ψ = 0) :
    cochainCoboundary (ZMod 2) (localSpace P v₀ k) ((m + 1) + q) (original m P v₀ k isLong hρ hρr q ψ) = 0 :=
  SupportedCapPullbackClass.original_closed (family P v₀ k isLong)
    (SupportedSelfCut.exterior (m + 1) ρ) (SupportedSelfCut.neighborhood (m + 1) r)
    (SupportedSelfCut.exterior_open (m + 1) ρ) (SupportedSelfCut.neighborhood_open (m + 1) r)
    (SupportedSelfCut.cover (m + 1) hρr) (m + 1) q (NormalizedSelfCut.cocycle (m + 1) (by omega) hρ)
    (NormalizedSelfCut.cocycle_supported (m + 1) (by omega) hρ)
    (NormalizedSelfCut.cocycle_closed (m + 1) (by omega) hρ) ψ hψ

theorem original_class_zero (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (k : Fin 3) (isLong : Bool)
    {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hρ1 : ρ ≤ 1) (q : ℕ)
    (ψ : singularCochainGroup (ZMod 2) (TopCat.of (SupportedSelfCut.neighborhood (m + 1) r)) q)
    (hψ : cochainCoboundary (ZMod 2) (TopCat.of (SupportedSelfCut.neighborhood (m + 1) r)) q ψ = 0) :
    CochainClass.classOf (cochainCxZMod2 (localSpace P v₀ k)) ((m + 1) + q)
      (original m P v₀ k isLong hρ hρr q ψ) (original_closed m P v₀ k isLong hρ hρr q ψ hψ) = 0 := by
  let X := localSpace P v₀ k
  let f := family P v₀ k isLong
  let A := NativeSameLegLocalCap.exterior P v₀ k isLong ρ
  let B := NativeSameLegLocalCap.near P v₀ k isLong r
  let C := SupportedSelfCut.exterior (m + 1) ρ
  let D := SupportedSelfCut.neighborhood (m + 1) r
  let hA := NativeSameLegLocalCap.exterior_open P v₀ k isLong ρ
  let hB := NativeSameLegLocalCap.near_open P v₀ k isLong r
  let hC := SupportedSelfCut.exterior_open (m + 1) ρ
  let hD := SupportedSelfCut.neighborhood_open (m + 1) r
  let hcX := NativeSameLegLocalCap.cover P v₀ k isLong hρr
  let hcY := SupportedSelfCut.cover (m + 1) hρr
  let τ := NormalizedSelfCut.cocycle (m + 1) (by omega) hρ
  let hsτ := NormalizedSelfCut.cocycle_supported (m + 1) (by omega) hρ
  let hτ := NormalizedSelfCut.cocycle_closed (m + 1) (by omega) hρ
  let κ : singularCochainGroup (ZMod 2) X m := NativeSameLegThomPrimitive.primitive (by omega) P v₀ k isLong hρ hρ1
  let hsκ := NativeSameLegLocalCap.primitive_supported m hm P v₀ k isLong hρ hρ1
  let Ψ := cochainPullback (nearMap P v₀ k isLong r) q ψ
  have hΨ : cochainCoboundary (ZMod 2) (TopCat.of B) q Ψ = 0 := pullback_closed _ q ψ hψ
  have he := SupportedCapPullbackClass.class_equality f A B C D hA hB hcX hC hD hcY
    (fun _ h => h) (fun _ h => h) (m + 1) q τ hsτ hτ ψ hψ (by omega)
  have hd : cochainPullback f (m + 1) τ = cochainCoboundary (ZMod 2) X m κ :=
    (NativeSameLegLocalCap.thom_boundary m hm P v₀ k isLong hρ hρ1).symm
  have hg := SupportedCapCochainCongruence.cut_eq X A B hA hB hcX (m + 1) q ((m + 1) + q) rfl
    (cochainPullback f (m + 1) τ) (cochainCoboundary (ZMod 2) X m κ)
    (pullback_support f A C (fun _ h => h) (m + 1) τ hsτ)
    (SupportedExactThomCap.coboundary_supported X A m κ hsκ) hd
  have hc : SupportedCapPullbackClass.localCochain f A B C D hA hB hcX (fun _ h => h) (fun _ h => h)
      (m + 1) q τ hsτ ψ = SupportedExactThomCapDegree.cochain X A B hA hB hcX m q κ hsκ Ψ :=
    congrArg (fun a => a ≫ Ψ) hg
  have hclass := CochainClass.classOf_congr (cochainCxZMod2 X) ((m + 1) + q) hc
    (SupportedCapPullbackClass.local_closed f A B C D hA hB hcX (fun _ h => h) (fun _ h => h)
      (m + 1) q τ hsτ hτ ψ hψ)
    (SupportedExactThomCapDegree.cochain_closed X A B hA hB hcX m q κ hsκ Ψ hΨ)
  exact he.trans (hclass.trans (SupportedExactThomCapDegree.cochain_class_zero X A B hA hB hcX m q κ hsκ Ψ hΨ))

end
end Finsler.NativeSameLegOriginalCapClass
