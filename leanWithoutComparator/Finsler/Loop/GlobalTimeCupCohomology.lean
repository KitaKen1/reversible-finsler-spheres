module

public import Finsler.Loop.GlobalThomTime
public import Finsler.Loop.DegreeLoweringCohomologyPullback
public import Finsler.Loop.CochainDegreeTransport
public import Finsler.Loop.GeometricTimeCupCochain

/-! A global cohomology operation from the ACTUAL split maps, ordinary
cup and genuine first-Thom time map. Its representative is the independently
defined geometric time-cut cochain, and its prism-cut pairing is proved.
No sphere-loop basis or identification with manuscript generators is assumed. -/

@[expose] public section
namespace Finsler.GlobalTimeCupCohomology
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SupportedSelfCut
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

private theorem rectangle_transport {X Y : TopCat.{0}} {f g : X ⟶ Y}
    (H : TopCat.Homotopy f g) (i j : ℕ) (h : i = j) :
    eqToHom (congrArg (chains X).X h) ≫ TimeShuffleComparison.rectangle H j =
      TimeShuffleComparison.rectangle H i ≫ eqToHom (congrArg (chains Y).X (congrArg (fun n => n + 1) h)) := by
  subst j
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

variable (m : ℕ) {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (p q : ℕ)

def product (a : cohomologyZMod2 (TopCat.of (SphereLoop (m + 1))) p)
    (b : cohomologyZMod2 (TopCat.of (SphereLoop (m + 1))) q) :
    cohomologyZMod2 (TopCat.of (SphereLoop (m + 1))) ((m + p) + q) :=
  CupUnit.absoluteCast _ (Nat.add_assoc m p q).symm
    (DegreeLoweringCohomologyPullback.map (GlobalThomTime.operation m hρ hρr) (p + q)
      (cupZMod2 ((cohPullback (TopCat.ofHom (tested (m + 1) hr)) p).hom a)
        ((cohPullback (TopCat.ofHom (retained (m + 1) hr)) q).hom b)))

theorem cochain_compare
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
    (B : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) q) :
    CochainDegreeTransport.pre (TopCat.of (SphereLoop (m + 1))) (Nat.add_assoc m p q)
      (DegreeLoweringCochainPullback.cochain (GlobalThomTime.operation m hρ hρr) (p + q)
        (GeometricTimeCupCochain.splitCup m p hr T q B)) =
    GeometricTimeCupCochain.cochain m p hρ hρr hr T q B := by
  rw [CochainDegreeTransport.pre, DegreeLoweringCochainPullback.cochain,
    GlobalThomTime.component, GeometricTimeCupCochain.cochain]
  simp only [Category.assoc]
  rw [← Category.assoc (eqToHom _) (TimeShuffleComparison.rectangle _ _),
    rectangle_transport (SelfCutTimePrism.cylinder (m + 1)) ((m + p) + q) (m + (p + q)) (Nat.add_assoc m p q)]
  simp only [Category.assoc]
  rw [← Category.assoc (eqToHom _) (eqToHom _), eqToHom_trans]

theorem product_cocycle
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
    (B : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) q)
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
    (hB : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) q B = 0) :
    product m hρ hρr hr p q (cocycleClass _ p T hT) (cocycleClass _ q B hB) =
      cocycleClass _ _ (GeometricTimeCupCochain.cochain m p hρ hρr hr T q B)
        (GeometricTimeCupCochain.closed m p hρ hρr hr T q B hT hB) := by
  let C := GeometricTimeCupCochain.splitCup m p hr T q B
  have hC : cochainCoboundary (ZMod 2) (TopCat.of (neighborhood (m + 1) r)) (p + q) C = 0 :=
    cochainCupZMod2_respects_cocycles p q _ _
      (NormalizedSelfCut.testedCocycle_closed (m + 1) p hr T hT)
      (cochainPullback_cocycle (TopCat.ofHom (retained (m + 1) hr)) q B hB)
  let f := GlobalThomTime.operation m hρ hρr
  let φ := DegreeLoweringCochainPullback.cochain f (p + q) C
  have hφ := DegreeLoweringCochainPullback.closed f (p + q) C hC
  have hc := cochain_compare m hρ hρr hr p q T B
  have hcast := CochainDegreeTransport.class_cast (TopCat.of (SphereLoop (m + 1)))
    (Nat.add_assoc m p q) φ hφ
  have he := cocycleClass_congr (TopCat.of (SphereLoop (m + 1))) ((m + p) + q) hc
    (CochainDegreeTransport.closed _ (Nat.add_assoc m p q) φ hφ)
    (GeometricTimeCupCochain.closed m p hρ hρr hr T q B hT hB)
  rw [product, cohPullback_cocycleClass, cohPullback_cocycleClass, cupZMod2_mk,
    DegreeLoweringCohomologyPullback.map_cocycle]
  exact hcast.symm.trans he

theorem representatives_eq
    (T T' : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
    (B B' : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) q)
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
    (hT' : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T' = 0)
    (hB : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) q B = 0)
    (hB' : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) q B' = 0)
    (h₁ : cocycleClass _ p T hT = cocycleClass _ p T' hT')
    (h₂ : cocycleClass _ q B hB = cocycleClass _ q B' hB') :
    cocycleClass _ _ (GeometricTimeCupCochain.cochain m p hρ hρr hr T q B)
      (GeometricTimeCupCochain.closed m p hρ hρr hr T q B hT hB) =
    cocycleClass _ _ (GeometricTimeCupCochain.cochain m p hρ hρr hr T' q B')
      (GeometricTimeCupCochain.closed m p hρ hρr hr T' q B' hT' hB') := by
  rw [← product_cocycle m hρ hρr hr p q T B hT hB,
    ← product_cocycle m hρ hρr hr p q T' B' hT' hB', h₁, h₂]

theorem pairing
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
    (B : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) q)
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
    (hB : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) q B = 0)
    (z : PoolCap.homology (TopCat.of (SphereLoop (m + 1))) ((m + p) + q)) :
    (kroneckerMap _ ((m + p) + q)).hom
      (product m hρ hρr hr p q (cocycleClass _ p T hT) (cocycleClass _ q B hB)) z =
    (kroneckerMap _ q).hom (cocycleClass _ q B hB)
      (((PrismSelfCut.operation m p hρ hρr hr T hT).homology q).hom z) := by
  rw [product_cocycle m hρ hρr hr p q T B hT hB]
  exact GeometricTimeCupCochain.pairing m p hρ hρr hr T q B hT hB z

end
end Finsler.GlobalTimeCupCohomology
