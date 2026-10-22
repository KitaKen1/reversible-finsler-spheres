module

public import Finsler.Topology.CylinderTimeTrim
public import Finsler.Topology.JoinedHalfOperations
public import Finsler.Topology.SupportedSelfCutAdequacy
public import Finsler.Topology.JoinLengthComparison

/-! Instantiate simultaneous whole-parent adequacy with the genuine full
joined-loop cylinder and both actual trimming homotopies. This supplies
one factorwise scale before all cochain degrees, representatives and
thresholds. Factoring the comparison chains through it remains separate. -/

@[expose] public section
namespace Finsler.JoinedComparisonAdequacy

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut
open Finsler.SupportedCapNaturality Finsler.SobolevLength Finsler.SelfCutParameterFamily
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

abbrev Outer (X : Type) := (ClosedInterval × ClosedInterval) × X

def tube (X : Type) : Set (Outer X) := Set.univ

section
variable {X : Type} [TopologicalSpace X] {n : ℕ}

def fullMap (u : C(X, H1JoinContinuity.composable n)) : TopCat.of (Outer X) ⟶ parameters n :=
  TopCat.ofHom ⟨fun z => (z.1.2, JoinedTimeSplit.loopFamily u z.2),
    (continuous_snd.comp continuous_fst).prodMk
      ((JoinedTimeSplit.loopFamily u).continuous.comp continuous_snd)⟩

def firstMap (u : C(X, H1JoinContinuity.composable n))
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2) : TopCat.of (Outer X) ⟶ parameters n :=
  TopCat.ofHom ⟨fun z => JoinedHalfCollars.firstFamily u
    (InteriorTimeSlide.slide a ha ha1 z.1, z.2),
    (JoinedHalfCollars.firstFamily u).hom.continuous.comp
      (((InteriorTimeSlide.slide a ha ha1).continuous.comp continuous_fst).prodMk continuous_snd)⟩

def secondMap (u : C(X, H1JoinContinuity.composable n))
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2) : TopCat.of (Outer X) ⟶ parameters n :=
  TopCat.ofHom ⟨fun z => JoinedHalfCollars.secondFamily u
    (InteriorTimeSlide.slide a ha ha1 z.1, z.2),
    (JoinedHalfCollars.secondFamily u).hom.continuous.comp
      (((InteriorTimeSlide.slide a ha ha1).continuous.comp continuous_fst).prodMk continuous_snd)⟩

def family (u : C(X, H1JoinContinuity.composable n))
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2) : Fin 3 → (TopCat.of (tube X) ⟶ parameters n) :=
  fun i => SupportedCap.subspaceMap (TopCat.of (Outer X)) (tube X) ≫
    ![fullMap u, firstMap u a ha ha1, secondMap u a ha ha1] i

theorem family_actual (u : C(X, H1JoinContinuity.composable n))
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2) (z : tube X) :
    (family u a ha ha1 0 z = JoinedTimeSplit.fullCylinder u (z.val.2, ULift.up z.val.1.2)) ∧
    (family u a ha ha1 1 z = CylinderTimeTrim.homotopy (JoinedHalfCollars.firstFamily u)
      a ha ha1 (z.val.1.1, (z.val.1.2, z.val.2))) ∧
    (family u a ha ha1 2 z = CylinderTimeTrim.homotopy (JoinedHalfCollars.secondFamily u)
      a ha ha1 (z.val.1.1, (z.val.1.2, z.val.2))) := ⟨rfl, rfl, rfl⟩

theorem triangle_actual (u : C(X, H1JoinContinuity.composable n))
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2)
    (v : Convexity.StdSimplex ℝ (Fin 3)) (s : ClosedInterval) (x : X) :
    family u a ha ha1 0 ⟨((s, (IntervalTriangle.triangleMap v).down), x), Set.mem_univ _⟩ =
      JoinedTimeSplit.fullCylinder u (x, IntervalTriangle.triangleMap v) := rfl

theorem family_loop (u : C(X, H1JoinContinuity.composable n))
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2) (i : Fin 3) (z : tube X) :
    (family u a ha ha1 i z).2 = JoinedTimeSplit.loopFamily u z.val.2 := by
  fin_cases i <;> rfl

theorem family_length (F : ReversibleMetric n) (u : C(X, H1JoinContinuity.composable n))
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2) (i : Fin 3) (z : tube X) :
    length F (family u a ha ha1 i z).2 =
      length F (u z.val.2).val.1 + length F (u z.val.2).val.2 := by
  rw [family_loop]
  exact JoinLengthComparison.length_join F (1 / 2) (by norm_num) (by norm_num)
    _ _ (u z.val.2).property

end

section
variable {X : Type} [PseudoMetricSpace X] [CompactSpace X] {n : ℕ}

theorem exists_filtered_scale (F : ReversibleMetric n)
    (u : C(X, H1JoinContinuity.composable n)) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2)
    {ρ r ε b : ℝ} (hρ : 0 < ρ) (hρr : 4 * ρ < r) (hr : r ≤ 1)
    (hε : 0 < ε) (hb : 0 < b) (hradius : r ≤ SelfCutLengthControl.radius F hε) :
    ∃ η > 0, η ≤ b ∧
      ∀ (cx : ClosedInterval × ClosedInterval) (cy : X) (S : Set (Outer X)),
      S ⊆ PairDistanceCover.cover id η cx ×ˢ PairDistanceCover.cover id η cy →
      ∀ (i : Fin 3) (k p : ℕ) (L A : ℝ)
      (φ : singularCochainGroup (ZMod 2) (parameters n) k)
      (hφ : cochainPullback (SupportedCap.subspaceMap (parameters n) (exterior n ρ)) k φ = 0)
      (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p),
      cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop n)) (SelfCutOscillation.short F L)) p T = 0 →
      (∀ z ∈ S, length F (u z.2).val.1 + length F (u z.2).val.2 < A) →
      ∀ (σ : TopCat.toSSet.obj (TopCat.of (Outer X)) _⦋k⦌)
        (τ : TopCat.toSSet.obj (TopCat.of (Outer X)) _⦋p⦌),
      Set.range ((TopCat.of (Outer X)).toSSetObjEquiv _ σ) ⊆ S →
      Set.range ((TopCat.of (Outer X)).toSSetObjEquiv _ τ) ⊆ S →
      (TopCat.toSSet.obj (TopCat.of (Outer X))).ιChainComplex σ ≫
        SupportedSelfCutAdequacy.extension (tube X) (family u a ha ha1) i k φ ≠ 0 →
      (TopCat.toSSet.obj (TopCat.of (Outer X))).ιChainComplex τ ≫
        testedExtension (tube X) (family u a ha ha1) (fun _ => r) (fun _ => hr) i p T ≠ 0 →
      ∀ z ∈ S, ∃ hz : z ∈ domain (tube X) (family u a ha ha1) (fun _ => r) i,
        length F (retainedMap (tube X) (family u a ha ha1) (fun _ => r) (fun _ => hr) i ⟨z, hz⟩) <
          A - L + 3 * ε := by
  obtain ⟨η, hη, hηb, had⟩ := SupportedSelfCutAdequacy.exists_filtered_scale F (tube X)
    (show IsCompact (tube X) from isCompact_univ) (family u a ha ha1)
    (fun _ => r) (fun _ => ρ) (fun _ => hr) (fun _ => hρ) (fun _ => hρr) hε hb (fun _ => hradius)
  refine ⟨η, hη, hηb, ?_⟩
  intro cx cy S hrect i k p L A φ hφ T hT hA σ τ hσS hτS hσ hτ z hzS
  apply had cx cy S hrect (Set.subset_univ S) i k p L A φ hφ T hT ?_ σ τ hσS hτS hσ hτ z hzS
  intro w hw
  rw [family_length]
  exact hA w.val hw

end
end
end Finsler.JoinedComparisonAdequacy
