module

public import Finsler.Loop.GlobalTimeCupConstantsVanish
public import Finsler.Loop.RelativePrismCochainBoundary
public import Finsler.Loop.NativeSequentialDoubleCapOutputComparison

/-! The ORIGINAL Thom/time map supplies the needed relative support
AFTER an arbitrary near-space correction. No support of the correction
itself is required. All claims use the actual small-chain cap. -/
@[expose] public section
namespace Finsler.NativeBVThomBoundary
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.BorelLoop
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

variable (m : ℕ) {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ < r)

def parameter (q : ℕ) (K : singularCochainGroup (ZMod 2) (TopCat.of (neighborhood (m + 1) r)) q) :
    singularCochainGroup (ZMod 2) (parameters (m + 1)) ((m + 1) + q) :=
  (NormalizedSelfCut.operation (m + 1) (by omega) hρ hρr).component q ≫ K

theorem parameter_endpoint (q : ℕ)
    (K : singularCochainGroup (ZMod 2) (TopCat.of (neighborhood (m + 1) r)) q)
    (t : ClosedInterval) (ht : t = 0 ∨ t = 1) :
    cochainPullback (atTime (m + 1) t) ((m + 1) + q) (parameter m hρ hρr q K) = 0 := by
  change (push (atTime (m + 1) t)).f _ ≫ (_ ≫ K) = 0
  rw [← Category.assoc, SelfCutEndpoints.thom_atTime_zero, zero_comp]
  rcases ht with rfl | rfl
  · exact NormalizedSelfCut.time_zero _ _ _
  · exact NormalizedSelfCut.time_one _ _ _

theorem parameter_diagonal (q : ℕ)
    (K : singularCochainGroup (ZMod 2) (TopCat.of (neighborhood (m + 1) r)) q)
    {X : TopCat.{0}} (f : X ⟶ parameters (m + 1))
    (hf : ∀ x, f x ∈ FilteredGlobalThomTime.endpointCarrier (m + 1)) :
    cochainPullback f ((m + 1) + q) (parameter m hρ hρr q K) = 0 := by
  have hz := SelfCutEndpoints.cut_map_zero (exterior (m + 1) ρ) (neighborhood (m + 1) r)
    (FilteredGlobalThomTime.endpointCarrier (m + 1))
    (exterior_open _ _) (neighborhood_open _ _) (cover _ hρr) (m + 1) q
    (NormalizedSelfCut.cocycle (m + 1) (by omega) hρ)
    (NormalizedSelfCut.cocycle_supported _ _ hρ) (FilteredGlobalThomTime.cocycle_endpoint m hρ) f hf
  change (push f).f _ ≫ (_ ≫ K) = 0
  rw [← Category.assoc]
  exact (congrArg (fun g => g ≫ K) hz).trans zero_comp

theorem parameter_far (q : ℕ)
    (K : singularCochainGroup (ZMod 2) (TopCat.of (neighborhood (m + 1) r)) q)
    {X : TopCat.{0}} (f : X ⟶ parameters (m + 1)) (hf : ∀ x, f x ∈ exterior (m + 1) ρ) :
    cochainPullback f ((m + 1) + q) (parameter m hρ hρr q K) = 0 := by
  have hz := SelfCutEndpoints.cut_map_zero (exterior (m + 1) ρ) (neighborhood (m + 1) r)
    (exterior (m + 1) ρ) (exterior_open _ _) (neighborhood_open _ _) (cover _ hρr) (m + 1) q
    (NormalizedSelfCut.cocycle (m + 1) (by omega) hρ)
    (NormalizedSelfCut.cocycle_supported _ _ hρ) (NormalizedSelfCut.cocycle_supported _ _ hρ) f hf
  change (push f).f _ ≫ (_ ≫ K) = 0
  rw [← Category.assoc]
  exact (congrArg (fun g => g ≫ K) hz).trans zero_comp

def source (q : ℕ) (K : singularCochainGroup (ZMod 2) (TopCat.of (neighborhood (m + 1) r)) q) :
    singularCochainGroup (ZMod 2) (Loops (m + 1)) (m + q) :=
  (GlobalThomTime.operation m hρ hρr).component q ≫ K

theorem source_boundary (q : ℕ)
    (K : singularCochainGroup (ZMod 2) (TopCat.of (neighborhood (m + 1) r)) q) :
    cochainCoboundary (ZMod 2) (Loops (m + 1)) (m + q) (source m hρ hρr q K) =
      source m hρ hρr (q + 1) (cochainCoboundary (ZMod 2) _ q K) :=
  NativeSequentialDoubleCapOutputComparison.lowering_boundary (GlobalThomTime.operation m hρ hρr) q K

theorem source_constants_zero (q : ℕ)
    (K : singularCochainGroup (ZMod 2) (TopCat.of (neighborhood (m + 1) r)) q) :
    cochainPullback (GlobalTimeCupConstantsVanish.inclusion (m + 1)) (m + q)
      (source m hρ hρr q K) = 0 := by
  change (push (GlobalTimeCupConstantsVanish.inclusion (m + 1))).f (m + q) ≫
    ((GlobalThomTime.operation m hρ hρr).component q ≫ K) = 0
  rw [← Category.assoc]
  exact (congrArg (fun g => g ≫ K) (GlobalTimeCupConstantsVanish.time_zero m hρ hρr q)).trans zero_comp

theorem lowering_boundary_at {X Y : TopCat.{0}} {d : ℕ}
    (f : DegreeLoweringHomology.Map (chains X) (chains Y) d)
    (i j : ℕ) (h : i + 1 = j) (K : singularCochainGroup (ZMod 2) Y i) :
    (chains X).d (d + j) (d + i) ≫ (f.component i ≫ K) =
      f.component j ≫ ((chains Y).d j i ≫ K) := by
  subst j
  rw [← Category.assoc, ← f.comm, Category.assoc]

theorem relative_boundary_zero (Q : TopPair.{0}) (i j : ℕ) {M : ModuleCat.{0} (ZMod 2)}
    (u : M ⟶ (chains Q.fst).X j)
    (hu : (u ≫ (Q.singularChainComplexπ coeff).f j) ≫ (Q.singularChainComplex coeff).d j i = 0)
    (K : singularCochainGroup (ZMod 2) Q.fst i) (hK : cochainPullback Q.map i K = 0) :
    u ≫ (chains Q.fst).d j i ≫ K = 0 := by
  obtain ⟨ψ, hψ⟩ := RelativeCupCochain.exists_lift Q i K hK
  have he : (Q.singularChainComplexπ coeff).f i ≫ ψ = K := hψ
  have hc : (Q.singularChainComplexπ coeff).f j ≫ (Q.singularChainComplex coeff).d j i =
      (chains Q.fst).d j i ≫ (Q.singularChainComplexπ coeff).f i :=
    (Q.singularChainComplexπ coeff).comm j i
  calc
    _ = u ≫ ((chains Q.fst).d j i ≫ (Q.singularChainComplexπ coeff).f i) ≫ ψ := by
      simpa only [Category.assoc] using congrArg (fun k => u ≫ (chains Q.fst).d j i ≫ k) he.symm
    _ = ((u ≫ (Q.singularChainComplexπ coeff).f j) ≫ (Q.singularChainComplex coeff).d j i) ≫ ψ := by
      simpa only [Category.assoc] using congrArg (fun k => u ≫ k ≫ ψ) hc.symm
    _ = 0 := by rw [hu, zero_comp]

theorem source_relative_cycle_boundary_zero (q : ℕ)
    (K : singularCochainGroup (ZMod 2) (TopCat.of (neighborhood (m + 1) r)) q)
    {M : ModuleCat.{0} (ZMod 2)} (u : M ⟶ (chains (Loops (m + 1))).X (m + q + 1))
    (hu : (u ≫ ((RelativePrismSweep.targetPair (consts (m + 1))).singularChainComplexπ coeff).f (m + q + 1)) ≫
      ((RelativePrismSweep.targetPair (consts (m + 1))).singularChainComplex coeff).d (m + q + 1) (m + q) = 0) :
    u ≫ source m hρ hρr (q + 1) (cochainCoboundary (ZMod 2) _ q K) = 0 := by
  rw [← source_boundary]
  exact RelativePrismCochainBoundary.relative_cycle_boundary_zero
    (RelativePrismSweep.targetPair (consts (m + 1))) (m + q) u hu _ (source_constants_zero m hρ hρr q K)

end
end Finsler.NativeBVThomBoundary
