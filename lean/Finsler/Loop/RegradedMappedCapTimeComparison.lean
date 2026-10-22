module

public import Finsler.Loop.CylinderCommonCover
public import Finsler.Loop.RegradedSingleCapTime
public import Finsler.Loop.RegradedTimeCoverComparison
public import Finsler.Topology.PrismRefinementHomology

/-! Compare two actual time-cap models over different cylinder
presentations, retaining the original target complex and its endpoint
corrections. Source monicity is used only for genuine chain groups. -/

@[expose] public section
namespace Finsler.RegradedMappedCapTimeComparison

open CategoryTheory AlgebraicTopology SphereOddDegree TauCeti
open Finsler.IntervalSobolev Finsler.CochainComparison Finsler.SmallChainCarrier
open Finsler.SupportedCapNaturality Finsler.RelativeCapAssociativity

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 2400000

theorem homology_eq (X Z : TopCat.{0}) {ι κ : Type*}
    (U : ι → Set (ClosedInterval × X)) (V : κ → Set Z)
    (hU : ∀ i, IsOpen (U i)) (hcU : ⋃ i, U i = Set.univ)
    (hV : ∀ i, IsOpen (V i)) (hcV : ⋃ i, V i = Set.univ)
    (f : TopCat.of (ClosedInterval × X) ⟶ Z)
    (E F : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ) (j : E ⟶ F)
    (d N : ℕ) (hN : d + 1 = N)
    (c : DegreeLoweringHomology.Map (small (TopCat.of (ClosedInterval × X)) U) E N)
    (v : DegreeLoweringHomology.Map (small Z V) F N)
    (A : Set (ClosedInterval × X))
    (φ : singularCochainGroup (ZMod 2) (TopCat.of (ClosedInterval × X)) N)
    (hφ : cochainPullback (SupportedCap.subspaceMap (TopCat.of (ClosedInterval × X)) A) N φ = 0)
    (b : E ⟶ chains (TopCat.of (ClosedInterval × X))) (hb : ∀ q, Mono (b.f q))
    (hs : ∀ q, c.component q ≫ b.f q =
      (inclusion (TopCat.of (ClosedInterval × X)) U).f (N + q) ≫
        absoluteChain (TopCat.of (ClosedInterval × X)) N q (N + q) rfl φ)
    (h₀ : ∀ x, ((0 : ClosedInterval), x) ∈ A) (h₁ : ∀ x, ((1 : ClosedInterval), x) ∈ A)
    (hcap : ∀ q,
      (CylinderCommonCover.toSource (X := TopCat.of (ClosedInterval × X)) (Y := Z) U V f).f (N + q) ≫
        c.component q ≫ j.f q =
      (CylinderCommonCover.toTarget (X := TopCat.of (ClosedInterval × X)) (Y := Z) U V f).f (N + q) ≫ v.component q)
    (a : DegreeLoweringHomology.Map (chains X) E d)
    (ha : ∀ q, a.component q = AnnularTimeTrim.prism X (d + q) ≫
      (smallSingularRetraction (X := TopCat.of (ClosedInterval × X)) coeff U hU hcU).f (d + q + 1) ≫
        DegreeLoweringSuccAlignment.align d c hN.symm q)
    (z : DegreeLoweringHomology.Map (chains X) F d)
    (hz : ∀ q, z.component q = AnnularTimeTrim.prism X (d + q) ≫
      (push f ≫ smallSingularRetraction (X := Z) coeff V hV hcV).f (d + q + 1) ≫
        DegreeLoweringSuccAlignment.align d v hN.symm q) (q : ℕ) :
    (a.post j).homology q = z.homology q := by
  let C : TopCat.{0} := TopCat.of (ClosedInterval × X)
  let W := CylinderCommonCover.cover (X := C) (Y := Z) U V f
  let hW := CylinderCommonCover.cover_open (X := C) (Y := Z) U V f hU hV
  let hcW := CylinderCommonCover.cover_univ (X := C) (Y := Z) U V f hcU hcV
  let Ms := CylinderCommonCover.toSource (X := C) (Y := Z) U V f
  let Mt := CylinderCommonCover.toTarget (X := C) (Y := Z) U V f
  let R := smallSingularRetraction (X := C) coeff W hW hcW
  let cW := c.pre Ms
  have hsW (t : ℕ) : cW.component t ≫ b.f t = (inclusion C W).f (N + t) ≫
      absoluteChain C N t (N + t) rfl φ := by
    dsimp only [cW, DegreeLoweringHomology.Map.pre]
    rw [Category.assoc, hs, ← Category.assoc, ← HomologicalComplex.comp_f,
      CylinderCommonCover.toSource_inclusion]
  let aW := RegradedSingleCapTime.operation X W hW hcW E d N hN cW A φ hφ b hb hsW h₀ h₁
  have haW (t : ℕ) : aW.component t = AnnularTimeTrim.prism X (d + t) ≫
      (R ≫ Ms).f (d + t + 1) ≫ DegreeLoweringSuccAlignment.align d c hN.symm t := by
    change AnnularTimeTrim.prism X (d + t) ≫
      eqToHom (congrArg (chains C).X (show d + t + 1 = N + t by omega)) ≫ R.f (N + t) ≫ cW.component t = _
    simpa only [cW, DegreeLoweringHomology.Map.pre, HomologicalComplex.comp_f, Category.assoc] using
      congrArg (fun k => AnnularTimeTrim.prism X (d + t) ≫ k)
        (RegradedTimeCoverComparison.normal (R ≫ Ms) d N hN c t)
  have hid : push (𝟙 C) = 𝟙 (chains C) := by
    change ((SSet.chainComplexFunctor.{0} (ModuleCat.{0} (ZMod 2))).obj coeff).map (TopCat.toSSet.map (𝟙 C)) = _
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  have he₁ : a.homology q = aW.homology q := by
    apply PrismRefinementHomology.homology_eq X C W U hW hcW hU hcU (𝟙 C) Prod.fst
      (fun _ _ hz => hz.1) E d (DegreeLoweringSuccAlignment.align d c hN.symm)
      (DegreeLoweringSuccAlignment.comm d c hN.symm) a aW
    · intro t
      rw [ha t, hid, Category.id_comp]
    · exact haW
  have hcapW (t : ℕ) : cW.component t ≫ j.f t = Mt.f (N + t) ≫ v.component t := hcap t
  have haWj (t : ℕ) : (aW.post j).component t = AnnularTimeTrim.prism X (d + t) ≫
      (R ≫ Mt).f (d + t + 1) ≫ DegreeLoweringSuccAlignment.align d v hN.symm t := by
    change (AnnularTimeTrim.prism X (d + t) ≫
      eqToHom (congrArg (chains C).X (show d + t + 1 = N + t by omega)) ≫ R.f (N + t) ≫ cW.component t) ≫ j.f t = _
    simp only [Category.assoc]
    rw [hcapW]
    have he := RegradedTimeCoverComparison.normal (R ≫ Mt) d N hN v t
    simpa only [HomologicalComplex.comp_f, Category.assoc] using
      congrArg (fun k => AnnularTimeTrim.prism X (d + t) ≫ k) he
  have he₂ : z.homology q = (aW.post j).homology q :=
    PrismRefinementHomology.homology_eq X Z W V hW hcW hV hcV f Prod.snd
      (fun _ _ hz => hz.2) F d (DegreeLoweringSuccAlignment.align d v hN.symm)
      (DegreeLoweringSuccAlignment.comm d v hN.symm) z (aW.post j) hz haWj q
  rw [DegreeLoweringHomology.Map.post_homology, he₁, ← DegreeLoweringHomology.Map.post_homology]
  exact he₂.symm

end
end Finsler.RegradedMappedCapTimeComparison
