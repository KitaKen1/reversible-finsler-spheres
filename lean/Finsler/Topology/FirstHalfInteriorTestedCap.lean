module

public import Finsler.Topology.FirstHalfInteriorPrism
public import Finsler.Topology.FirstHalfInteriorTested
public import Finsler.Topology.SupportedCapHomology

/-! The actual closed tested cap on the filtered first-half cut domain
has a concrete prism comparison entirely in the retained-length target.
Its source cap is the existing singular (Lean Pool) cap, with no extra
cohomology or comparison hypothesis. -/

@[expose] public section
namespace Finsler.FirstHalfInteriorTestedCap

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SupportedCapNaturality Finsler.FirstHalfInteriorFamily

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {X : Type} [TopologicalSpace X] {n : ℕ}
  (u : C(X, H1JoinContinuity.composable n)) (a : ℝ) (ha : 0 < a) (ha1 : a < 1 / 2)
  {r : ℝ} (hr : r ≤ 1) (F : ReversibleMetric n) (A : ℝ)

def testedMap : TopCat.of (filteredDomain u a ha ha1 hr F A) ⟶ TopCat.of (SphereLoop n) :=
  SupportedCap.subspaceMap (TopCat.of (domain u a ha ha1 r)) (filteredDomain u a ha ha1 hr F A) ≫
    FirstHalfInteriorTested.sourceMap u a ha ha1 hr

def cochain (p : ℕ) (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p) :
    singularCochainGroup (ZMod 2) (TopCat.of (filteredDomain u a ha ha1 hr F A)) p :=
  cochainPullback (testedMap u a ha ha1 hr F A) p T

theorem cochain_closed (p : ℕ) (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p)
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop n)) p T = 0) :
    cochainCoboundary (ZMod 2) (TopCat.of (filteredDomain u a ha ha1 hr F A)) p
      (cochain u a ha ha1 hr F A p T) = 0 :=
  pullback_closed (testedMap u a ha ha1 hr F A) p T hT

variable (p : ℕ) (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p)
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop n)) p T = 0)

def cap : DegreeLoweringHomology.Map
    (chains (TopCat.of (filteredDomain u a ha ha1 hr F A)))
    (chains (TopCat.of (filteredDomain u a ha ha1 hr F A))) p :=
  SupportedCapHomology.absoluteOperation (TopCat.of (filteredDomain u a ha ha1 hr F A)) p
    (cochain u a ha ha1 hr F A p T) (cochain_closed u a ha ha1 hr F A p T hT)

def operation (s : _root_.unitInterval) : DegreeLoweringHomology.Map
    (chains (TopCat.of (filteredDomain u a ha ha1 hr F A)))
    (chains (TopCat.of {w : SphereLoop n | SobolevLength.length F w < A})) p :=
  (cap u a ha ha1 hr F A p T hT).post
    (push (TopCat.ofHom (FirstHalfInteriorPrism.endpoint u a ha ha1 hr F A s)))

theorem cap_pool (q : ℕ) :
    (cap u a ha ha1 hr F A p T hT).homology q =
      ModuleCat.ofHom (PoolCap.cap (TopCat.of (filteredDomain u a ha ha1 hr F A)) p q (p + q) rfl
        (cocycleClass (TopCat.of (filteredDomain u a ha ha1 hr F A)) p (cochain u a ha ha1 hr F A p T)
          (cochain_closed u a ha ha1 hr F A p T hT))) :=
  SupportedCapHomology.absolute_homology _ p q _ _

theorem homology_eq (q : ℕ) :
    (operation u a ha ha1 hr F A p T hT 0).homology q =
      (operation u a ha ha1 hr F A p T hT 1).homology q := by
  have he : HomologicalComplex.homologyMap
      (push (TopCat.ofHom (FirstHalfInteriorPrism.endpoint u a ha ha1 hr F A 0))) q =
      HomologicalComplex.homologyMap
      (push (TopCat.ofHom (FirstHalfInteriorPrism.endpoint u a ha ha1 hr F A 1))) q :=
    ((FirstHalfInteriorPrism.homotopy u a ha ha1 hr F A).toSSet.chainComplexMap coeff).homologyMap_eq q
  dsimp [operation]
  rw [DegreeLoweringHomology.Map.post_homology, DegreeLoweringHomology.Map.post_homology, he]

theorem capped_prism_boundary (q : ℕ) :
    (chains (TopCat.of (filteredDomain u a ha ha1 hr F A))).iCycles (p + q) ≫
      ((operation u a ha ha1 hr F A p T hT 0).component q -
       (operation u a ha ha1 hr F A p T hT 1).component q) =
    ((chains (TopCat.of (filteredDomain u a ha ha1 hr F A))).iCycles (p + q) ≫
      (cap u a ha ha1 hr F A p T hT).component q ≫ FirstHalfInteriorPrism.prism u a ha ha1 hr F A q) ≫
      (chains (TopCat.of {w : SphereLoop n | SobolevLength.length F w < A})).d (q + 1) q := by
  let c := cap u a ha ha1 hr F A p T hT
  have hh := congrArg (fun f => c.cycles q ≫ f)
    (FirstHalfInteriorPrism.prism_boundary u a ha ha1 hr F A q)
  simp only [← Category.assoc] at hh
  rw [c.cycles_i] at hh
  simpa only [operation, DegreeLoweringHomology.Map.post, Preadditive.comp_sub,
    Category.assoc, c] using hh.symm

end
end Finsler.FirstHalfInteriorTestedCap
