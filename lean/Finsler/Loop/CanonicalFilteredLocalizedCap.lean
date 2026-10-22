module

public import Finsler.Loop.SingleCutCanonicalTwoStage
public import Finsler.Topology.DegreeLoweringSuccAlignment
public import Finsler.Loop.LocalizedCapCupComponentSource

/-! The actual canonical localized Thom-then-tested filtered cap,
before its first canonical retraction. Native time-degree alignment
recovers the original canonical indexed cut and family time components. -/

@[expose] public section
namespace Finsler.CanonicalFilteredLocalizedCap

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1600000

variable {m : ℕ} (F : ReversibleMetric (m + 1)) (a ρ R : ℝ)
  (hρ : 0 < ρ) (hρR : ρ < R) (hR : R ≤ 1) (ε : ℝ) (hε : 0 < ε)
  (hRR : R ≤ SelfCutLengthControl.radius F hε) (L : ℝ) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
  (hshort : cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
    (SelfCutOscillation.short F L)) p T = 0)

def cover := SupportedCap.cover (FilteredPrismSelfCut.domain F a)
  (FilteredPrismSelfCut.far F a ρ) (FilteredPrismSelfCut.near F a R)

theorem cover_open (i : Bool) : IsOpen (cover F a ρ R i) :=
  SupportedCap.cover_open _ _ _ (FilteredPrismSelfCut.far_open F a ρ)
    (FilteredPrismSelfCut.near_open F a R) i

include hρR in
theorem cover_univ : ⋃ i, cover F a ρ R i = Set.univ :=
  SupportedCap.cover_univ _ _ _ (FilteredPrismSelfCut.cover F a hρR)

def operation := DegreeLoweringComposition.compose
  ((SupportedCapNaturality.localizedOperation (FilteredPrismSelfCut.domain F a)
    (FilteredPrismSelfCut.far F a ρ) (FilteredPrismSelfCut.near F a R) (m + 1)
    (FilteredPrismSelfCut.cocycle (by omega) F a hρ)
    (FilteredPrismSelfCut.cocycle_far (by omega) F a hρ)
    (FilteredPrismSelfCut.cocycle_closed (by omega) F a hρ)).post
    (push (FilteredPrismSelfCut.toIncoming F R a)))
  (FilteredTestedCap.operation F hR hε hRR p T hT hshort)

def nested (q : ℕ) := SupportedCap.localizedCap (FilteredPrismSelfCut.domain F a)
  (FilteredPrismSelfCut.far F a ρ) (FilteredPrismSelfCut.near F a R) (m + 1) (p + q)
  ((m + 1) + (p + q)) rfl (FilteredPrismSelfCut.cocycle (by omega) F a hρ)
  (FilteredPrismSelfCut.cocycle_far (by omega) F a hρ) ≫
  (push (FilteredPrismSelfCut.toIncoming F R a)).f (p + q) ≫
  (FilteredTestedCap.operation F hR hε hRR p T hT hshort).component q

theorem component_nested (q : ℕ) :
    (operation F a ρ R hρ hR ε hε hRR L p T hT hshort).component q =
      eqToHom (congrArg (small (FilteredPrismSelfCut.domain F a) (cover F a ρ R)).X
        (Nat.add_assoc (m + 1) p q)) ≫ nested F a ρ R hρ hR ε hε hRR L p T hT hshort q := rfl

theorem chainCut_eq (q : ℕ) :
    FilteredPrismSelfCut.chainCut (by omega) F hρ hρR hR hε hRR p T hT hshort (a := a) q =
    (TauCeti.smallSingularRetraction (X := FilteredPrismSelfCut.domain F a) coeff (cover F a ρ R)
      (cover_open F a ρ R) (cover_univ F a ρ R hρR)).f ((m + 1) + (p + q)) ≫
      nested F a ρ R hρ hR ε hε hRR L p T hT hshort q := rfl

def indexed := DegreeLoweringSuccAlignment.align (m + p)
  (operation F a ρ R hρ hR ε hε hRR L p T hT hshort) (by omega)

theorem indexed_comm (q : ℕ) :
    indexed F a ρ R hρ hR ε hε hRR L p T hT hshort (q + 1) ≫
      (chains (TopCat.of (SelfCutOscillation.short F (a - L + 3 * ε)))).d (q + 1) q =
    (small (FilteredPrismSelfCut.domain F a) (cover F a ρ R)).d
      ((m + p) + q + 2) ((m + p) + q + 1) ≫
      indexed F a ρ R hρ hR ε hε hRR L p T hT hshort q :=
  DegreeLoweringSuccAlignment.comm (m + p)
    (operation F a ρ R hρ hR ε hε hRR L p T hT hshort) (by omega) q

theorem indexedCut_eq (q : ℕ) :
    FilteredPrismSelfCut.indexedCut m p F hρ hρR hR hε hRR T hT hshort (a := a) q =
    (TauCeti.smallSingularRetraction (X := FilteredPrismSelfCut.domain F a) coeff (cover F a ρ R)
      (cover_open F a ρ R) (cover_univ F a ρ R hρR)).f (((m + p) + q) + 1) ≫
      indexed F a ρ R hρ hR ε hε hRR L p T hT hshort q := by
  rw [FilteredPrismSelfCut.indexedCut, chainCut_eq]
  dsimp only [indexed, DegreeLoweringSuccAlignment.align]
  rw [component_nested, ← Category.assoc (eqToHom _) (eqToHom _), eqToHom_trans]
  have ht := LocalizedCapCupComponentSource.transport_f
    (TauCeti.smallSingularRetraction (X := FilteredPrismSelfCut.domain F a) coeff (cover F a ρ R)
      (cover_open F a ρ R) (cover_univ F a ρ R hρR))
    (((m + p) + q) + 1) ((m + 1) + (p + q)) (by omega)
  simpa only [Category.assoc] using congrArg
    (fun k => k ≫ nested F a ρ R hρ hR ε hε hRR L p T hT hshort q) ht

theorem family_component {P : Type} [TopologicalSpace P]
    (α : C(P, SphereLoop (m + 1))) (hA : ∀ x, SobolevLength.length F (α x) < a) (q : ℕ) :
    ((FilteredPrismSelfCut.operation m p F hρ hρR hR hε hRR T hT hshort).pre
      (push (CompactInputShortMaps.family α F a hA))).component q =
    AnnularTimeTrim.prism (TopCat.of P) ((m + p) + q) ≫
      (push (CompactInputShortMaps.cylinder α F a hA) ≫
        TauCeti.smallSingularRetraction (X := FilteredPrismSelfCut.domain F a) coeff (cover F a ρ R)
          (cover_open F a ρ R) (cover_univ F a ρ R hρR)).f (((m + p) + q) + 1) ≫
      indexed F a ρ R hρ hR ε hε hRR L p T hT hshort q := by
  change (push (CompactInputShortMaps.family α F a hA)).f ((m + p) + q) ≫
    (((FilteredPrismSelfCut.cylinder F a).toSSet.chainComplexMap coeff).hom _ _ ≫ _) = _
  rw [← Category.assoc, CompactInputShortMaps.prism_square, Category.assoc,
    indexedCut_eq, HomologicalComplex.comp_f]
  simp only [Category.assoc]

end
end Finsler.CanonicalFilteredLocalizedCap
