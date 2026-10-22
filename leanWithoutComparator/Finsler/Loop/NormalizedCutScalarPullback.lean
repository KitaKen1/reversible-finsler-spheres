module

public import Finsler.Loop.SupportedCapPullbackPrimitive
public import Finsler.Loop.GeometricTimeCupCochain
public import Finsler.Loop.NativeOrderedDoubleCutSupported

/-! Explicit comparison with the ORIGINAL normalized cut after an actual
parameter map. The original retraction remains on its original ambient
space; its pullback is compared with the source retraction by the same
small-chain subdivision primitive. The two output factors are retained. -/
@[expose] public section
namespace Finsler.NormalizedCutScalarPullback
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.NativeOrderedDoubleCutSupported Finsler.SupportedSelfCut
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

theorem pre_cut (X : TopCat.{0}) (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (hc : A ∪ B = Set.univ) (p q i j : ℕ) (hi : p + q = i) (hj : p + q = j) (h : i = j)
    (θ : singularCochainGroup (ZMod 2) X p)
    (hs : cochainPullback (SupportedCap.subspaceMap X A) p θ = 0)
    (ψ : singularCochainGroup (ZMod 2) (TopCat.of B) q) :
    CochainDegreeTransport.pre X h (SupportedCap.cut X A B hA hB hc p q j hj θ hs ≫ ψ) =
      SupportedCap.cut X A B hA hB hc p q i hi θ hs ≫ ψ := by
  subst i j
  simp only [CochainDegreeTransport.pre, eqToHom_refl, Category.id_comp]

theorem pre_pullback {X Y : TopCat.{0}} (f : X ⟶ Y) {i j : ℕ} (h : i = j)
    (T : singularCochainGroup (ZMod 2) Y j) :
    CochainDegreeTransport.pre X h (cochainPullback f j T) =
      cochainPullback f i (CochainDegreeTransport.pre Y h T) := by
  subst j
  simp only [CochainDegreeTransport.pre, eqToHom_refl, Category.id_comp]

variable (m : ℕ) {X : TopCat.{0}} (f : X ⟶ SelfCutThomCocycle.parameters (m + 1))
  {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (p q : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (Finsler.IntervalSobolev.SphereLoop (m + 1))) p)
  (B : singularCochainGroup (ZMod 2) (TopCat.of (Finsler.IntervalSobolev.SphereLoop (m + 1))) q)

def nearMap : TopCat.of (near f r) ⟶ TopCat.of (neighborhood (m + 1) r) :=
  restriction f (near f r) (neighborhood (m + 1) r) (fun _ h => h)

def localValue : singularCochainGroup (ZMod 2) X ((m + 1) + (p + q)) :=
  (NativeOrderedDoubleCutSupported.operation f (by omega) hρ hρr).component (p + q) ≫
    cochainPullback (nearMap m f) (p + q) (GeometricTimeCupCochain.splitCup m p hr T q B)

def originalValue : singularCochainGroup (ZMod 2) X ((m + 1) + (p + q)) :=
  cochainPullback f ((m + 1) + (p + q))
    ((NormalizedSelfCut.operation (m + 1) (by omega) hρ hρr).component (p + q) ≫
      GeometricTimeCupCochain.splitCup m p hr T q B)

def primitive : singularCochainGroup (ZMod 2) X (m + (p + q)) :=
  SupportedCapPullbackPrimitive.primitive f (far f ρ) (near f r)
    (exterior (m + 1) ρ) (neighborhood (m + 1) r)
    (far_open f ρ) (near_open f r) (NativeOrderedDoubleCutSupported.cover f hρr)
    (exterior_open (m + 1) ρ) (neighborhood_open (m + 1) r) (SupportedSelfCut.cover (m + 1) hρr)
    (fun _ h => h) (fun _ h => h) (m + 1) (p + q)
    (NormalizedSelfCut.cocycle (m + 1) (by omega) hρ)
    (NormalizedSelfCut.cocycle_supported (m + 1) (by omega) hρ)
    (GeometricTimeCupCochain.splitCup m p hr T q B) (m + (p + q)) (by omega)

theorem split_closed
    (hT : cochainCoboundary (ZMod 2) _ p T = 0)
    (hB : cochainCoboundary (ZMod 2) _ q B = 0) :
    cochainCoboundary (ZMod 2) (TopCat.of (neighborhood (m + 1) r)) (p + q)
      (GeometricTimeCupCochain.splitCup m p hr T q B) = 0 :=
  cochainCupZMod2_respects_cocycles p q _ _
    (NormalizedSelfCut.testedCocycle_closed (m + 1) p hr T hT)
    (pullback_closed _ q B hB)

theorem original_chain_cut (hT : cochainCoboundary (ZMod 2) _ p T = 0) :
    originalValue m f hρ hρr hr p q T B =
      cochainPullback f ((m + 1) + (p + q))
        (NormalizedSelfCut.chainCut (m + 1) p (by omega) hρ hρr hr T hT q ≫ B) := by
  unfold originalValue NormalizedSelfCut.chainCut
  rw [Category.assoc, GeometricTimeCupCochain.tested_cap_dual]

theorem boundary (hT : cochainCoboundary (ZMod 2) _ p T = 0)
    (hB : cochainCoboundary (ZMod 2) _ q B = 0) :
    cochainCoboundary (ZMod 2) X (m + (p + q)) (primitive m f hρ hρr hr p q T B) =
      CochainDegreeTransport.pre X (show m + (p + q) + 1 = (m + 1) + (p + q) by omega)
        (localValue m f hρ hρr hr p q T B - originalValue m f hρ hρr hr p q T B) := by
  have h := SupportedCapPullbackPrimitive.boundary f (far f ρ) (near f r)
    (exterior (m + 1) ρ) (neighborhood (m + 1) r)
    (far_open f ρ) (near_open f r) (NativeOrderedDoubleCutSupported.cover f hρr)
    (exterior_open (m + 1) ρ) (neighborhood_open (m + 1) r) (SupportedSelfCut.cover (m + 1) hρr)
    (fun _ h => h) (fun _ h => h) (m + 1) (p + q)
    (NormalizedSelfCut.cocycle (m + 1) (by omega) hρ)
    (NormalizedSelfCut.cocycle_supported (m + 1) (by omega) hρ)
    (GeometricTimeCupCochain.splitCup m p hr T q B) (m + (p + q)) (by omega)
    (NormalizedSelfCut.cocycle_closed (m + 1) (by omega) hρ) (split_closed m hr p q T B hT hB)
  unfold localValue originalValue
  change _ = CochainDegreeTransport.pre X _ (_ - _)
  simp only [CochainDegreeTransport.pre, Preadditive.comp_sub]
  change _ = CochainDegreeTransport.pre X (show m + (p + q) + 1 = (m + 1) + (p + q) by omega) _ -
    CochainDegreeTransport.pre X (show m + (p + q) + 1 = (m + 1) + (p + q) by omega) _
  rw [pre_pullback]
  dsimp only [NativeOrderedDoubleCutSupported.operation, NormalizedSelfCut.operation, SupportedCapHomology.operation]
  rw [pre_cut, pre_cut]
  exact h

end
end Finsler.NormalizedCutScalarPullback
