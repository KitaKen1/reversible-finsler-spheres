module

public import Finsler.Loop.TubeExtensionSquare
public import Finsler.Topology.SelfCutParameterFamily
public import Finsler.Topology.NormalizedSelfCut

/-! On a genuine map into a partial family's parameter tube, the
literal tested zero extension pulls back to the canonical tested
extension of the actual global pulled-back family. -/

@[expose] public section
namespace Finsler.PartialTestedPullback

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut Finsler.SupportedCapNaturality
open Finsler.SelfCutParameterFamily

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1300000

def canonical {Y : TopCat.{0}} {n : ℕ} (G : Y ⟶ parameters n) {r : ℝ} (hr : r ≤ 1) (p : ℕ)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p) :
    singularCochainGroup (ZMod 2) Y p :=
  TubeCochainExtension.extend Y (G ⁻¹' neighborhood n r) p
    (cochainPullback (restriction G (G ⁻¹' neighborhood n r) (neighborhood n r) (fun _ h => h)) p
      (NormalizedSelfCut.testedCocycle n p hr T))

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {ι : Type*} {n : ℕ}
  (K : Set (P × Q)) (e : ι → (TopCat.of K ⟶ parameters n)) (i : ι)
  (Y : TopCat.{0}) (f : Y ⟶ TopCat.of K) (r : ℝ)

def domainMap : TopCat.of ((f ≫ e i) ⁻¹' neighborhood n r) ⟶
    TopCat.of (domain K e (fun _ => r) i) := by
  refine TopCat.ofHom ⟨fun z => ⟨(f z.val).val, (f z.val).property, ?_⟩, ?_⟩
  · change distanceValue K e i (f z.val).val < r
    rw [distanceValue, TubeTestWitness.partialValue, dite_eq_left (f z.val).property]
    exact z.property
  · exact (continuous_subtype_val.comp (f.hom.continuous.comp continuous_subtype_val)).subtype_mk _

theorem domain_iff (y : Y) : y ∈ (f ≫ e i) ⁻¹' neighborhood n r ↔
    (f ≫ SupportedCap.subspaceMap (TopCat.of (P × Q)) K) y ∈ domain K e (fun _ => r) i := by
  constructor
  · intro hy
    refine ⟨(f y).property, ?_⟩
    change distanceValue K e i (f y).val < r
    rw [distanceValue, TubeTestWitness.partialValue, dite_eq_left (f y).property]
    exact hy
  · intro hy
    have hd := hy.2
    change distanceValue K e i (f y).val < r at hd
    rw [distanceValue, TubeTestWitness.partialValue, dite_eq_left (f y).property] at hd
    exact hd

theorem source_square : domainMap K e i Y f r ≫
    SupportedCap.subspaceMap (TopCat.of (P × Q)) (domain K e (fun _ => r) i) =
      SupportedCap.subspaceMap Y ((f ≫ e i) ⁻¹' neighborhood n r) ≫
        (f ≫ SupportedCap.subspaceMap (TopCat.of (P × Q)) K) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  rfl

theorem tested_square (hr : r ≤ 1) : domainMap K e i Y f r ≫
    testedMap K e (fun _ => r) (fun _ => hr) i =
      restriction (f ≫ e i) ((f ≫ e i) ⁻¹' neighborhood n r) (neighborhood n r) (fun _ h => h) ≫
        TopCat.ofHom (tested n hr) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  rfl

theorem pullback_tested (hr : r ≤ 1) (p : ℕ)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p) :
    cochainPullback (f ≫ SupportedCap.subspaceMap (TopCat.of (P × Q)) K) p
      (testedExtension K e (fun _ => r) (fun _ => hr) i p T) =
        canonical (f ≫ e i) hr p T := by
  unfold testedExtension
  rw [TubeExtensionSquare.pullback_extend
    (f ≫ SupportedCap.subspaceMap (TopCat.of (P × Q)) K) (domain K e (fun _ => r) i)
    ((f ≫ e i) ⁻¹' neighborhood n r) (domainMap K e i Y f r)
    (domain_iff K e i Y f r) (source_square K e i Y f r)]
  rw [← pullback_comp, tested_square]
  rw [canonical, NormalizedSelfCut.testedCocycle, ← pullback_comp]

end
end Finsler.PartialTestedPullback
