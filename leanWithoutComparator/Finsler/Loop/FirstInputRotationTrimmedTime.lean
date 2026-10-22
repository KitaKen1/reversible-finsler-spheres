module

public import Finsler.Loop.FirstInputRotationTimeTrim
public import Finsler.Topology.TimeCylinderComparison
public import Finsler.Topology.ClosedCapFunctoriality

/-! Compare full and trimmed cut time inside the original bounded
proper cut domain. Actual side prisms factor through the annular collar;
the explicit double-prism comparison does not discard endpoint terms. -/

@[expose] public section
namespace Finsler.FirstInputRotationTrimmedTime

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier
open Finsler.FirstInputRotationCutCylinder Finsler.FirstInputRotationTimeTrim

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1200000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R r : ℝ)
  (hR : R ≤ 1 / 2) (hr : r < 1) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (F : ReversibleMetric (m + 1))
  (B η : ℝ) (hη : 0 < η) (hρr : ρ < r)
  (hgood : FirstInputRotationTestedCap.Adequate α β R r hR hr F B η p T)
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
  (a : ℝ) (ha : 0 < a) (ha1 : a < 1 / 2)

def aligned (q : ℕ) := ClosedCapDegreeTransport.align m p
  (FirstInputRotationFullTime.retracted α β R r hR hr p T h F B η hη hρr hgood hT) q

theorem aligned_comm (q : ℕ) :
    aligned α β R r hR hr p T h F B η hη hρr hgood hT (q + 1) ≫
        (chains (FirstInputRotationTimeCap.target α β R r hR hr F B)).d (q + 1) q =
      (chains (cylinder α β R)).d ((m + p) + q + 2) ((m + p) + q + 1) ≫
        aligned α β R r hR hr p T h F B η hη hρr hgood hT q :=
  ClosedCapDegreeTransport.align_comm m p _
    (FirstInputRotationFullTime.retracted_comm α β R r hR hr p T h F B η hη hρr hgood hT) q

def trimmedCap (q : ℕ) :=
  ClosedCapDegreeTransport.align m p
    (NestedCapRefinement.pre (m + 1) p (push (trimMap α β R a ha ha1))
      (FirstInputRotationFullTime.retracted α β R r hR hr p T h F B η hη hρr hgood hT)) q

theorem trimmedCap_normal (q : ℕ) :
    trimmedCap α β R r hR hr p T h F B η hη hρr hgood hT a ha ha1 q =
      (push (trimMap α β R a ha ha1)).f ((m + p) + q + 1) ≫
        aligned α β R r hR hr p T h F B η hη hρr hgood hT q :=
  ClosedCapFunctoriality.align_pre (push (trimMap α β R a ha ha1)) m p
    (FirstInputRotationFullTime.retracted α β R r hR hr p T h F B η hη hρr hgood hT) q

theorem trimmedCap_comm (q : ℕ) :
    trimmedCap α β R r hR hr p T h F B η hη hρr hgood hT a ha ha1 (q + 1) ≫
        (chains (FirstInputRotationTimeCap.target α β R r hR hr F B)).d (q + 1) q =
      (chains (cylinder α β R)).d ((m + p) + q + 2) ((m + p) + q + 1) ≫
        trimmedCap α β R r hR hr p T h F B η hη hρr hgood hT a ha ha1 q :=
  ClosedCapDegreeTransport.align_comm m p _
    (NestedCapRefinement.pre_comm (m + 1) p (push (trimMap α β R a ha ha1)) _
      (FirstInputRotationFullTime.retracted_comm α β R r hR hr p T h F B η hη hρr hgood hT)) q

theorem trimmed_endpoint_zero (t : ClosedInterval)
    (hs : ∀ s x, sideHomotopy α β R a ha ha1 t (s, x) ∈ collar α β R δ) (q : ℕ) :
    (push (AnnularTimeTrim.slice (input α β R) t)).f ((m + p) + q + 1) ≫
      trimmedCap α β R r hR hr p T h F B η hη hρr hgood hT a ha ha1 q = 0 := by
  have hz := ClosedCapCollarPrism.map_zero (collar α β R δ) (cover α β R r η ρ)
    (cover_open α β R r η ρ) (cover_univ α β R r η hη hρr)
    (chains (FirstInputRotationTimeCap.target α β R r hR hr F B)) m p
    (FirstInputRotationTimeCap.component α β R r hR hr p T (by omega) h F B η hgood hT)
    (thom α β R hR (by omega) h) (tested α β R r hR hr p T)
    (thom_inner_zero α β R hR (by omega) h)
    (push (FirstInputRotationTimeCap.source α β R r hR hr F B))
    (FirstInputRotationTimeCap.source_mono α β R r hR hr F B)
    (FirstInputRotationTimeCap.component_source α β R r hR hr p T (by omega) h F B η hgood hT)
    (AnnularTimeTrim.slice (input α β R) t ≫ trimMap α β R a ha ha1)
    (trim_endpoint_collar α β R a ha ha1 t hs) q
  rw [trimmedCap_normal]
  change (push (AnnularTimeTrim.slice (input α β R) t)).f ((m + p) + q + 1) ≫
    (push (trimMap α β R a ha ha1)).f ((m + p) + q + 1) ≫
      ClosedCapDegreeTransport.align m p
        (fun t => (TauCeti.smallSingularRetraction (X := cylinder α β R) coeff (cover α β R r η ρ)
          (cover_open α β R r η ρ) (cover_univ α β R r η hη hρr)).f ((m + 1) + (p + t)) ≫
            FirstInputRotationTimeCap.component α β R r hR hr p T (by omega) h F B η hgood hT t) q = 0
  simpa only [push_comp, HomologicalComplex.comp_f, Category.assoc] using hz

theorem side_zero (t : ClosedInterval)
    (hs : ∀ s x, sideHomotopy α β R a ha ha1 t (s, x) ∈ collar α β R δ) (q : ℕ) :
    (push (AnnularTimeTrim.slice (input α β R) t)).f ((m + p) + q) ≫
      (((slideHomotopy α β R a ha ha1).toSSet.chainComplexMap coeff).hom
        ((m + p) + q) ((m + p) + q + 1) ≫
          aligned α β R r hR hr p T h F B η hη hρr hgood hT q) = 0 := by
  rw [← Category.assoc, TimePrismNaturality.prism_pre]
  have hz := ClosedCapCollarPrism.prism_zero (sideHomotopy α β R a ha ha1 t) (collar α β R δ) hs
    (cover α β R r η ρ) (cover_open α β R r η ρ) (cover_univ α β R r η hη hρr)
    (chains (FirstInputRotationTimeCap.target α β R r hR hr F B)) m p
    (FirstInputRotationTimeCap.component α β R r hR hr p T (by omega) h F B η hgood hT)
    (thom α β R hR (by omega) h) (tested α β R r hR hr p T)
    (thom_inner_zero α β R hR (by omega) h)
    (push (FirstInputRotationTimeCap.source α β R r hR hr F B))
    (FirstInputRotationTimeCap.source_mono α β R r hR hr F B)
    (FirstInputRotationTimeCap.component_source α β R r hR hr p T (by omega) h F B η hgood hT) q
  exact hz

variable
  (hzero : ∀ s x, sideHomotopy α β R a ha ha1 0 (s, x) ∈ collar α β R δ)
  (hone : ∀ s x, sideHomotopy α β R a ha ha1 1 (s, x) ∈ collar α β R δ)

def operation : DegreeLoweringHomology.Map (chains (input α β R))
    (chains (FirstInputRotationTimeCap.target α β R r hR hr F B)) (m + p) :=
  TimePrismDescent.operation ((AnnularTimeTrim.cylinder (input α β R)).toSSet.chainComplexMap coeff) (m + p)
    (trimmedCap α β R r hR hr p T h F B η hη hρr hgood hT a ha ha1)
    (trimmedCap_comm α β R r hR hr p T h F B η hη hρr hgood hT a ha ha1)
    (trimmed_endpoint_zero α β R r hR hr p T h F B η hη hρr hgood hT a ha ha1 0 hzero)
    (trimmed_endpoint_zero α β R r hR hr p T h F B η hη hρr hgood hT a ha ha1 1 hone)

theorem component_normal (q : ℕ) :
    (operation α β R r hR hr p T h F B η hη hρr hgood hT a ha ha1 hzero hone).component q =
      AnnularTimeTrim.prism (input α β R) ((m + p) + q) ≫
        (push (trimMap α β R a ha ha1)).f ((m + p) + q + 1) ≫
          aligned α β R r hR hr p T h F B η hη hρr hgood hT q := by
  change AnnularTimeTrim.prism (input α β R) ((m + p) + q) ≫
    trimmedCap α β R r hR hr p T h F B η hη hρr hgood hT a ha ha1 q = _
  rw [trimmedCap_normal]

theorem full_trim_homology_eq (q : ℕ) :
    (FirstInputRotationFullTime.operation α β R r hR hr p T h F B η hη hρr hgood hT).homology q =
      (operation α β R r hR hr p T h F B η hη hρr hgood hT a ha ha1 hzero hone).homology q := by
  have hid : push (𝟙 (cylinder α β R)) = 𝟙 (chains (cylinder α β R)) := by
    change ((SSet.chainComplexFunctor.{0} (ModuleCat.{0} (ZMod 2))).obj coeff).map
      (TopCat.toSSet.map (𝟙 (cylinder α β R))) = _
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  apply TimeCylinderComparison.homology_eq
    ((AnnularTimeTrim.cylinder (input α β R)).toSSet.chainComplexMap coeff)
    ((slideHomotopy α β R a ha ha1).toSSet.chainComplexMap coeff) (m + p)
    (aligned α β R r hR hr p T h F B η hη hρr hgood hT)
    (aligned_comm α β R r hR hr p T h F B η hη hρr hgood hT)
    (side_zero α β R r hR hr p T h F B η hη hρr hgood hT a ha ha1 0 hzero)
    (side_zero α β R r hR hr p T h F B η hη hρr hgood hT a ha ha1 1 hone)
  · intro t
    change (FirstInputRotationFullTime.operation α β R r hR hr p T h F B η hη hρr hgood hT).component t =
      AnnularTimeTrim.prism (input α β R) ((m + p) + t) ≫
        (push (𝟙 (cylinder α β R))).f ((m + p) + t + 1) ≫
          aligned α β R r hR hr p T h F B η hη hρr hgood hT t
    rw [hid, HomologicalComplex.id_f, Category.id_comp]
    exact FirstInputRotationFullTime.component_normal α β R r hR hr p T h F B η hη hρr hgood hT t
  · intro t
    exact component_normal α β R r hR hr p T h F B η hη hρr hgood hT a ha ha1 hzero hone t

def retainedOperation :=
  (operation α β R r hR hr p T h F B η hη hρr hgood hT a ha ha1 hzero hone).post
    (push (FirstInputRotationFilteredCap.retained α β R r hR hr F B))

theorem retained_homology_eq (q : ℕ) :
    (FirstInputRotationFullTime.retainedOperation α β R r hR hr p T h F B η hη hρr hgood hT).homology q =
      (retainedOperation α β R r hR hr p T h F B η hη hρr hgood hT a ha ha1 hzero hone).homology q := by
  rw [FirstInputRotationFullTime.retainedOperation, DegreeLoweringHomology.Map.post_homology,
    retainedOperation, DegreeLoweringHomology.Map.post_homology,
    full_trim_homology_eq α β R r hR hr p T h F B η hη hρr hgood hT a ha ha1 hzero hone]

end
end Finsler.FirstInputRotationTrimmedTime
