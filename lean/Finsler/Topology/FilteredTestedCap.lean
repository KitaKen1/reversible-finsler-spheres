module

public import Finsler.Topology.CapOutputSupport
public import Finsler.Analysis.SelfCutOscillation

/-! The actual T-cap and retained C2 projection factor into the length
sublevel a-L+3epsilon after an actual tested-length small approximation.
The input is the actual cut tube with original-loop length less than a.
The time prism and the first supported Thom stage are not yet included. -/

@[expose] public section
namespace Finsler.FilteredTestedCap

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SupportedSelfCut Finsler.SobolevLength
open Finsler.RelativeCapAssociativity Finsler.SelfCutOscillation
open Set
open scoped Topology Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

variable {n : ℕ}

def incoming (F : ReversibleMetric n) (r a : ℝ) : Set (neighborhood n r) :=
  {z | length F z.val.2 < a}

def space (F : ReversibleMetric n) (r a : ℝ) : TopCat.{0} := TopCat.of (incoming F r a)

def inclusion (F : ReversibleMetric n) (r a : ℝ) : space F r a ⟶ TopCat.of (neighborhood n r) :=
  SupportedCap.subspaceMap (TopCat.of (neighborhood n r)) (incoming F r a)

def cover (F : ReversibleMetric n) {r : ℝ} (hr : r ≤ 1) (a ε : ℝ)
    (center : neighborhood n r) : Set (space F r a) :=
  inclusion F r a ⁻¹' oscillationCover F hr ε center

theorem cover_open (F : ReversibleMetric n) {r : ℝ} (hr : r ≤ 1) (a ε : ℝ)
    (center : neighborhood n r) : IsOpen (cover F hr a ε center) :=
  (oscillationCover_open F hr ε center).preimage (inclusion F r a).hom.continuous

theorem cover_univ (F : ReversibleMetric n) {r : ℝ} (hr : r ≤ 1) (a : ℝ)
    {ε : ℝ} (hε : 0 < ε) : ⋃ center, cover F hr a ε center = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  exact mem_iUnion.mpr ⟨z.val, by simp [cover, inclusion, SupportedCap.subspaceMap,
    oscillationCover, hε]⟩

def retainedMap (F : ReversibleMetric n) {r : ℝ} (hr : r ≤ 1) (a : ℝ) :
    space F r a ⟶ TopCat.of (SphereLoop n) :=
  inclusion F r a ≫ TopCat.ofHom (retained n hr)

def cochain (F : ReversibleMetric n) {r : ℝ} (hr : r ≤ 1) (a : ℝ) (p : ℕ)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p) :
    singularCochainGroup (ZMod 2) (space F r a) p :=
  cochainPullback (inclusion F r a) p (NormalizedSelfCut.testedCocycle n p hr T)

theorem cochain_closed (F : ReversibleMetric n) {r : ℝ} (hr : r ≤ 1) (a : ℝ) (p : ℕ)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p)
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop n)) p T = 0) :
    cochainCoboundary (ZMod 2) (space F r a) p (cochain F hr a p T) = 0 :=
  CochainClass.closed_map (cochainCxZMod2 (TopCat.of (neighborhood n r)))
    (singularCochainComplexZMod2.map (inclusion F r a).op) p _
    (NormalizedSelfCut.testedCocycle_closed n p hr T hT)

theorem parent_output (F : ReversibleMetric n) {r ε a L : ℝ}
    (hr : r ≤ 1) (hε : 0 < ε) (hrr : r ≤ SelfCutLengthControl.radius F hε)
    (p q : ℕ) (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p)
    (hT : cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop n)) (short F L))
      p T = 0)
    (σ : ((space F r a).smallSingularSubcomplex (cover F hr a ε) : SSet) _⦋p + q⦌)
    (hσ : (TopCat.toSSet.obj (space F r a)).ιChainComplex σ.val ≫
      absoluteChain (space F r a) p q (p + q) rfl (cochain F hr a p T) ≠ 0) :
    ∀ z ∈ Set.range ((space F r a).toSSetObjEquiv _ σ.val),
      retainedMap F hr a z ∈ short F (a - L + 3 * ε) := by
  let i := inclusion F r a
  let τ := (TopCat.toSSet.map i).app (Opposite.op ⦋p + q⦌) σ.val
  have hτ : (TopCat.toSSet.obj (TopCat.of (neighborhood n r))).ιChainComplex τ ≫
      absoluteChain (TopCat.of (neighborhood n r)) p q (p + q) rfl
        (NormalizedSelfCut.testedCocycle n p hr T) ≠ 0 := by
    intro hz
    haveI : Mono ((SupportedCapNaturality.push i).f q) :=
      SupportedCap.subspacePush_mono (TopCat.of (neighborhood n r)) (incoming F r a) q
    apply hσ
    apply (cancel_mono ((SupportedCapNaturality.push i).f q)).mp
    rw [zero_comp]
    exact (CapOutputSupport.cap_push_simplex i p q
      (NormalizedSelfCut.testedCocycle n p hr T) σ.val).trans hz
  obtain ⟨center, hcenter⟩ := (TopCat.mem_smallSingularSubcomplex_iff (space F r a)
    (cover F hr a ε) σ.val).mp σ.property
  have hfine : Set.range ((TopCat.of (neighborhood n r)).toSSetObjEquiv _ τ) ⊆
      oscillationCover F hr ε center := by
    rw [TauCeti.TopCat.toSSetObjEquiv_toSSet_map_app]
    rintro _ ⟨t, rfl⟩
    exact hcenter ⟨t, rfl⟩
  have ha : ∀ z ∈ Set.range ((TopCat.of (neighborhood n r)).toSSetObjEquiv _ τ),
      length F z.val.2 < a := by
    rw [TauCeti.TopCat.toSSetObjEquiv_toSSet_map_app]
    rintro _ ⟨t, rfl⟩
    exact (((space F r a).toSSetObjEquiv _ σ.val) t).property
  have hp := parent_retained_lt F hr hε hrr p q T hT τ hτ ⟨center, hfine⟩ ha
  rintro z ⟨t, rfl⟩
  apply hp
  rw [TauCeti.TopCat.toSSetObjEquiv_toSSet_map_app]
  exact ⟨t, rfl⟩

def smallOperation (F : ReversibleMetric n) {r ε a L : ℝ}
    (hr : r ≤ 1) (hε : 0 < ε) (hrr : r ≤ SelfCutLengthControl.radius F hε)
    (p : ℕ) (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p)
    (hclosed : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop n)) p T = 0)
    (hT : cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop n)) (short F L))
      p T = 0) :
    DegreeLoweringHomology.Map (small (space F r a) (cover F hr a ε))
      (chains (TopCat.of (short F (a - L + 3 * ε)))) p :=
  CapOutputSupport.operation (cover F hr a ε) (retainedMap F hr a)
    (short F (a - L + 3 * ε)) p (cochain F hr a p T)
    (fun q σ => parent_output F hr hε hrr p q T hT σ) (cochain_closed F hr a p T hclosed)

def operation (F : ReversibleMetric n) {r ε a L : ℝ}
    (hr : r ≤ 1) (hε : 0 < ε) (hrr : r ≤ SelfCutLengthControl.radius F hε)
    (p : ℕ) (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p)
    (hclosed : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop n)) p T = 0)
    (hT : cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop n)) (short F L))
      p T = 0) :
    DegreeLoweringHomology.Map (chains (space F r a))
      (chains (TopCat.of (short F (a - L + 3 * ε)))) p :=
  (smallOperation F hr hε hrr p T hclosed hT).pre
    (TauCeti.smallSingularRetraction coeff (cover F hr a ε)
      (cover_open F hr a ε) (cover_univ F hr a hε))

theorem operation_inclusion (F : ReversibleMetric n) {r ε a L : ℝ}
    (hr : r ≤ 1) (hε : 0 < ε) (hrr : r ≤ SelfCutLengthControl.radius F hε)
    (p : ℕ) (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p)
    (hclosed : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop n)) p T = 0)
    (hT : cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop n)) (short F L))
      p T = 0) (q : ℕ) :
    (operation F hr hε hrr p T hclosed hT (a := a)).component q ≫
        (SupportedCapNaturality.push (SupportedCap.subspaceMap (TopCat.of (SphereLoop n))
          (short F (a - L + 3 * ε)))).f q =
      (TauCeti.singularSmallApprox coeff (cover F hr a ε)).f (p + q) ≫
        absoluteChain (space F r a) p q (p + q) rfl (cochain F hr a p T) ≫
          (SupportedCapNaturality.push (retainedMap F hr a)).f q := by
  change ((TauCeti.smallSingularRetraction coeff (cover F hr a ε)
    (cover_open F hr a ε) (cover_univ F hr a hε)).f (p + q) ≫
      CapOutputSupport.component (cover F hr a ε) (retainedMap F hr a)
        (short F (a - L + 3 * ε)) p (cochain F hr a p T)
        (fun q σ => parent_output F hr hε hrr p q T hT σ) q) ≫ _ = _
  rw [Category.assoc, CapOutputSupport.component_inclusion]
  simp only [← Category.assoc]
  rw [← HomologicalComplex.comp_f, TauCeti.smallSingularRetraction_comp_ι]

theorem homology_inclusion (F : ReversibleMetric n) {r ε a L : ℝ}
    (hr : r ≤ 1) (hε : 0 < ε) (hrr : r ≤ SelfCutLengthControl.radius F hε)
    (p : ℕ) (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p)
    (hclosed : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop n)) p T = 0)
    (hT : cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop n)) (short F L))
      p T = 0) (q : ℕ) :
    (operation F hr hε hrr p T hclosed hT (a := a)).homology q ≫
        HomologicalComplex.homologyMap
          (SupportedCapNaturality.push (SupportedCap.subspaceMap (TopCat.of (SphereLoop n))
            (short F (a - L + 3 * ε)))) q =
      (SupportedCapHomology.absoluteOperation (space F r a) p (cochain F hr a p T)
        (cochain_closed F hr a p T hclosed)).homology q ≫
          HomologicalComplex.homologyMap (SupportedCapNaturality.push (retainedMap F hr a)) q := by
  let o := operation F hr hε hrr p T hclosed hT (a := a)
  let j := SupportedCapNaturality.push (SupportedCap.subspaceMap (TopCat.of (SphereLoop n))
    (short F (a - L + 3 * ε)))
  let u := (SupportedCapHomology.absoluteOperation (space F r a) p (cochain F hr a p T)
    (cochain_closed F hr a p T hclosed)).post (SupportedCapNaturality.push (retainedMap F hr a))
  let approx := TauCeti.singularSmallApprox coeff (cover F hr a ε)
  have he : (o.post j).homology q = (u.pre approx).homology q := by
    apply DegreeLoweringHomology.Map.homology_eq_of_components
    intro k
    exact operation_inclusion F hr hε hrr p T hclosed hT k
  calc
    _ = (o.post j).homology q := (o.post_homology j q).symm
    _ = (u.pre approx).homology q := he
    _ = HomologicalComplex.homologyMap approx (p + q) ≫ u.homology q := u.pre_homology approx q
    _ = u.homology q := by
      have h := (TauCeti.singularSmallApproxHomotopy coeff (cover F hr a ε)).homologyMap_eq (p + q)
      rw [HomologicalComplex.homologyMap_id] at h
      rw [← h, Category.id_comp]
    _ = _ := (SupportedCapHomology.absoluteOperation (space F r a) p (cochain F hr a p T)
      (cochain_closed F hr a p T hclosed)).post_homology
        (SupportedCapNaturality.push (retainedMap F hr a)) q

end
end Finsler.FilteredTestedCap
