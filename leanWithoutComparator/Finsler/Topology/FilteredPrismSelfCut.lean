module

public import Finsler.Topology.FilteredTestedCap
public import Finsler.Topology.TimePrismDescent

/-! An actual filtered prism self-cut on the original strong-H1 length
sublevel. The first supported Thom cut retains the input length bound;
the tested-length small approximation and T cap land in length a-L+3epsilon.
Time endpoints vanish before T capping. The resulting actual chain operation
has degree 1-n-p. Comparison with the specified shuffled time rectangle,
arc timing, join interchange, the absolute unit and UF remain separate. -/

@[expose] public section
namespace Finsler.FilteredPrismSelfCut

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SobolevLength Finsler.SelfCutThomCocycle
open Finsler.SelfCutOscillation
open Set
open scoped Topology

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

variable {n : ℕ}

def domain (F : ReversibleMetric n) (a : ℝ) : TopCat.{0} :=
  TopCat.of (ClosedInterval × short F a)

def forget (F : ReversibleMetric n) (a : ℝ) : domain F a ⟶ parameters n :=
  TopCat.ofHom ⟨fun z => (z.1, z.2.val),
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)⟩

def far (F : ReversibleMetric n) (a ρ : ℝ) : Set (domain F a) :=
  forget F a ⁻¹' SupportedSelfCut.exterior n ρ

def near (F : ReversibleMetric n) (a r : ℝ) : Set (domain F a) :=
  forget F a ⁻¹' SupportedSelfCut.neighborhood n r

theorem far_open (F : ReversibleMetric n) (a ρ : ℝ) : IsOpen (far F a ρ) :=
  (SupportedSelfCut.exterior_open n ρ).preimage (forget F a).hom.continuous

theorem near_open (F : ReversibleMetric n) (a r : ℝ) : IsOpen (near F a r) :=
  (SupportedSelfCut.neighborhood_open n r).preimage (forget F a).hom.continuous

theorem cover (F : ReversibleMetric n) (a : ℝ) {ρ r : ℝ} (hρr : ρ < r) :
    far F a ρ ∪ near F a r = Set.univ := by
  rw [far, near, ← Set.preimage_union, SupportedSelfCut.cover n hρr, Set.preimage_univ]

private theorem pullback_preimage_zero {X Y : TopCat.{0}} (f : X ⟶ Y) (A : Set Y)
    (p : ℕ) (φ : singularCochainGroup (ZMod 2) Y p)
    (hφ : cochainPullback (SupportedCap.subspaceMap Y A) p φ = 0) :
    cochainPullback (SupportedCap.subspaceMap X (f ⁻¹' A)) p (cochainPullback f p φ) = 0 := by
  let g : TopCat.of (f ⁻¹' A) ⟶ TopCat.of A :=
    TopCat.ofHom ⟨fun z => ⟨f z.val, z.property⟩,
      (f.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩
  have he : SupportedCap.subspaceMap X (f ⁻¹' A) ≫ f = g ≫ SupportedCap.subspaceMap Y A := by
    ext z : 1
    rfl
  rw [← SupportedCapNaturality.pullback_comp, he, SupportedCapNaturality.pullback_comp, hφ]
  simp [cochainPullback]

def cocycle (hn : 1 ≤ n) (F : ReversibleMetric n) (a : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    singularCochainGroup (ZMod 2) (domain F a) n :=
  cochainPullback (forget F a) n (NormalizedSelfCut.cocycle n hn hρ)

theorem cocycle_closed (hn : 1 ≤ n) (F : ReversibleMetric n) (a : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    cochainCoboundary (ZMod 2) (domain F a) n (cocycle hn F a hρ) = 0 :=
  CochainClass.closed_map (cochainCxZMod2 (parameters n))
    (singularCochainComplexZMod2.map (forget F a).op) n _ (NormalizedSelfCut.cocycle_closed n hn hρ)

theorem cocycle_far (hn : 1 ≤ n) (F : ReversibleMetric n) (a : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    cochainPullback (SupportedCap.subspaceMap (domain F a) (far F a ρ)) n
      (cocycle hn F a hρ) = 0 :=
  pullback_preimage_zero (forget F a) (SupportedSelfCut.exterior n ρ) n _
    (NormalizedSelfCut.cocycle_supported n hn hρ)

def firstThom (hn : 1 ≤ n) (F : ReversibleMetric n) (a : ℝ) {ρ r : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) :=
  SupportedCapHomology.operation (domain F a) (far F a ρ) (near F a r)
    (far_open F a ρ) (near_open F a r) (cover F a hρr) n
    (cocycle hn F a hρ) (cocycle_far hn F a hρ) (cocycle_closed hn F a hρ)

def toIncoming (F : ReversibleMetric n) (r a : ℝ) :
    TopCat.of (near F a r) ⟶ FilteredTestedCap.space F r a :=
  TopCat.ofHom ⟨fun z => ⟨⟨forget F a z.val, z.property⟩, z.val.2.property⟩,
    (((forget F a).hom.continuous.comp continuous_subtype_val).subtype_mk _).subtype_mk _⟩

def thom (hn : 1 ≤ n) (F : ReversibleMetric n) (a : ℝ) {ρ r : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) :=
  (firstThom hn F a hρ hρr).post (SupportedCapNaturality.push (toIncoming F r a))

def atTimeBelow (F : ReversibleMetric n) (a : ℝ) (t : ClosedInterval) :
    TopCat.of (short F a) ⟶ domain F a :=
  TopCat.ofHom ⟨fun u => (t, u), continuous_const.prodMk continuous_id⟩

theorem at_cocycle_zero (hn : 1 ≤ n) (F : ReversibleMetric n) (a : ℝ) {ρ : ℝ}
    (hρ : 0 < ρ) (t : ClosedInterval)
    (ht : cochainPullback (atTime n t) n (NormalizedSelfCut.cocycle n hn hρ) = 0) :
    cochainPullback (atTimeBelow F a t) n (cocycle hn F a hρ) = 0 := by
  have he : atTimeBelow F a t ≫ forget F a =
      SupportedCap.subspaceMap (TopCat.of (SphereLoop n)) (short F a) ≫ atTime n t := by
    ext z : 1
    rfl
  rw [cocycle, ← SupportedCapNaturality.pullback_comp, he,
    SupportedCapNaturality.pullback_comp, ht]
  simp [cochainPullback]

theorem thom_endpoint (hn : 1 ≤ n) (F : ReversibleMetric n) (a : ℝ) {ρ r : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (q : ℕ) (t : ClosedInterval)
    (ht : cochainPullback (atTime n t) n (NormalizedSelfCut.cocycle n hn hρ) = 0) :
    (SupportedCapNaturality.push (atTimeBelow F a t)).f (n + q) ≫
      (thom hn F a hρ hρr).component q = 0 := by
  let C : Set (domain F a) := {z | z.1 = t}
  let pr : TopCat.of C ⟶ TopCat.of (short F a) :=
    TopCat.ofHom ⟨fun z => z.val.2, continuous_snd.comp continuous_subtype_val⟩
  have he : SupportedCap.subspaceMap (domain F a) C = pr ≫ atTimeBelow F a t := by
    ext z : 1
    exact Prod.ext z.property rfl
  have hC : cochainPullback (SupportedCap.subspaceMap (domain F a) C) n (cocycle hn F a hρ) = 0 := by
    rw [he, SupportedCapNaturality.pullback_comp, at_cocycle_zero hn F a hρ t ht]
    simp [cochainPullback]
  have hz : (SupportedCapNaturality.push (atTimeBelow F a t)).f (n + q) ≫
      (firstThom hn F a hρ hρr).component q = 0 :=
    SelfCutEndpoints.cut_map_zero (far F a ρ) (near F a r) C
      (far_open F a ρ) (near_open F a r) (cover F a hρr) n q
      (cocycle hn F a hρ) (cocycle_far hn F a hρ) hC (atTimeBelow F a t) (fun _ => rfl)
  change (SupportedCapNaturality.push (atTimeBelow F a t)).f (n + q) ≫
    ((firstThom hn F a hρ hρr).component q ≫ (SupportedCapNaturality.push (toIncoming F r a)).f q) = 0
  rw [← Category.assoc, hz, zero_comp]

def chainCut (hn : 1 ≤ n) (F : ReversibleMetric n) {ρ r ε a L : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1)
    (hε : 0 < ε) (hrr : r ≤ SelfCutLengthControl.radius F hε) (p : ℕ)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p)
    (hclosed : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop n)) p T = 0)
    (hT : cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop n)) (short F L)) p T = 0)
    (q : ℕ) : (chains (domain F a)).X (n + (p + q)) ⟶
      (chains (TopCat.of (short F (a - L + 3 * ε)))).X q :=
  (thom hn F a hρ hρr).component (p + q) ≫
    (FilteredTestedCap.operation F hr hε hrr p T hclosed hT).component q

theorem chainCut_boundary (hn : 1 ≤ n) (F : ReversibleMetric n) {ρ r ε a L : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1)
    (hε : 0 < ε) (hrr : r ≤ SelfCutLengthControl.radius F hε) (p : ℕ)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p)
    (hclosed : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop n)) p T = 0)
    (hT : cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop n)) (short F L)) p T = 0)
    (q : ℕ) : chainCut hn F hρ hρr hr hε hrr p T hclosed hT (a := a) (q + 1) ≫
        (chains (TopCat.of (short F (a - L + 3 * ε)))).d (q + 1) q =
      (chains (domain F a)).d (n + (p + (q + 1))) (n + (p + q)) ≫
        chainCut hn F hρ hρr hr hε hrr p T hclosed hT q := by
  have hu : (thom hn F a hρ hρr).component (p + (q + 1)) ≫
      (chains (FilteredTestedCap.space F r a)).d (p + (q + 1)) (p + q) =
    (chains (domain F a)).d (n + (p + (q + 1))) (n + (p + q)) ≫
      (thom hn F a hρ hρr).component (p + q) := (thom hn F a hρ hρr).comm (p + q)
  unfold chainCut
  rw [Category.assoc, (FilteredTestedCap.operation F hr hε hrr p T hclosed hT).comm,
    ← Category.assoc, hu, Category.assoc]

def cylinder (F : ReversibleMetric n) (a : ℝ) : TopCat.Homotopy (atTimeBelow F a 0) (atTimeBelow F a 1) where
  toFun z := (⟨z.1.val, z.1.property⟩, z.2)
  continuous_toFun := continuous_fst.prodMk continuous_snd
  map_zero_left _ := rfl
  map_one_left _ := rfl

private theorem cast_d (D : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ)
    {i i' j j' : ℕ} (hi : i = i') (hj : j = j') :
    eqToHom (congrArg D.X hi) ≫ D.d i' j' =
      D.d i j ≫ eqToHom (congrArg D.X hj) := by
  subst i'
  subst j'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

private theorem map_cast {C D : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
    (f : C ⟶ D) {i j : ℕ} (h : i = j) :
    f.f i ≫ eqToHom (congrArg D.X h) = eqToHom (congrArg C.X h) ≫ f.f j := by
  subst j
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

section Operation

variable (m p : ℕ) (F : ReversibleMetric (m + 1)) {ρ r ε a L : ℝ}
  (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1)
  (hε : 0 < ε) (hrr : r ≤ SelfCutLengthControl.radius F hε)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  (hclosed : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
  (hT : cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
    (short F L)) p T = 0)

def indexedCut (q : ℕ) : (chains (domain F a)).X ((m + p) + q + 1) ⟶
    (chains (TopCat.of (short F (a - L + 3 * ε)))).X q :=
  eqToHom (congrArg (chains (domain F a)).X
    (by omega : (m + p) + q + 1 = (m + 1) + (p + q))) ≫
      chainCut (by omega) F hρ hρr hr hε hrr p T hclosed hT q

theorem indexedCut_boundary (q : ℕ) :
    indexedCut m p F hρ hρr hr hε hrr T hclosed hT (a := a) (q + 1) ≫
        (chains (TopCat.of (short F (a - L + 3 * ε)))).d (q + 1) q =
      (chains (domain F a)).d ((m + p) + q + 2) ((m + p) + q + 1) ≫
        indexedCut m p F hρ hρr hr hε hrr T hclosed hT q := by
  unfold indexedCut
  rw [Category.assoc, chainCut_boundary, ← Category.assoc,
    cast_d _ (j := (m + p) + q + 1) (by omega) (by omega), Category.assoc]
  rfl

theorem indexedCut_endpoint (q : ℕ) (t : ClosedInterval)
    (ht : cochainPullback (atTime (m + 1) t) (m + 1)
      (NormalizedSelfCut.cocycle (m + 1) (by omega) hρ) = 0) :
    (SupportedCapNaturality.push (atTimeBelow F a t)).f ((m + p) + q + 1) ≫
      indexedCut m p F hρ hρr hr hε hrr T hclosed hT q = 0 := by
  have hz : (SupportedCapNaturality.push (atTimeBelow F a t)).f ((m + 1) + (p + q)) ≫
      chainCut (by omega) F hρ hρr hr hε hrr p T hclosed hT q = 0 := by
    rw [chainCut, ← Category.assoc, thom_endpoint (by omega) F a hρ hρr (p + q) t ht,
      zero_comp]
  unfold indexedCut
  rw [← Category.assoc, map_cast _ (by omega), Category.assoc, hz, comp_zero]

def operation : DegreeLoweringHomology.Map (chains (TopCat.of (short F a)))
    (chains (TopCat.of (short F (a - L + 3 * ε)))) (m + p) :=
  TimePrismDescent.operation ((cylinder F a).toSSet.chainComplexMap coeff) (m + p)
    (indexedCut m p F hρ hρr hr hε hrr T hclosed hT)
    (indexedCut_boundary m p F hρ hρr hr hε hrr T hclosed hT)
    (fun q => indexedCut_endpoint m p F hρ hρr hr hε hrr T hclosed hT q 0
      (NormalizedSelfCut.time_zero (m + 1) (by omega) hρ))
    (fun q => indexedCut_endpoint m p F hρ hρr hr hε hrr T hclosed hT q 1
      (NormalizedSelfCut.time_one (m + 1) (by omega) hρ))

theorem operation_boundary (q : ℕ) :
    (operation m p F hρ hρr hr hε hrr T hclosed hT (a := a)).component (q + 1) ≫
        (chains (TopCat.of (short F (a - L + 3 * ε)))).d (q + 1) q =
      (chains (TopCat.of (short F a))).d ((m + p) + (q + 1)) ((m + p) + q) ≫
        (operation m p F hρ hρr hr hε hrr T hclosed hT).component q :=
  (operation m p F hρ hρr hr hε hrr T hclosed hT).comm q

theorem cycles_closed (q : ℕ) :
    ((chains (TopCat.of (short F a))).iCycles ((m + p) + q) ≫
      (operation m p F hρ hρr hr hε hrr T hclosed hT).component q) ≫
        (chains (TopCat.of (short F (a - L + 3 * ε)))).d q (q - 1) = 0 :=
  (operation m p F hρ hρr hr hε hrr T hclosed hT).cycles_closed q

end Operation

def canonicalOperation (m p : ℕ) (F : ReversibleMetric (m + 1)) {ε a L : ℝ}
    (hε : 0 < ε)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
    (hclosed : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
    (hT : cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
      (short F L)) p T = 0) :
    DegreeLoweringHomology.Map (chains (TopCat.of (short F a)))
      (chains (TopCat.of (short F (a - L + 3 * ε)))) (m + p) :=
  let r := SelfCutLengthControl.radius F hε
  have hr : 0 < r ∧ r ≤ 1 := ⟨(SelfCutLengthControl.radius_spec F hε).1,
    (SelfCutLengthControl.radius_spec F hε).2.1⟩
  operation m p F (half_pos hr.1) (half_lt_self hr.1) hr.2 hε le_rfl T hclosed hT

def homology (m p : ℕ) (F : ReversibleMetric (m + 1)) {ε a L : ℝ}
    (hε : 0 < ε)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
    (hclosed : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
    (hT : cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
      (short F L)) p T = 0) (q : ℕ) :
    (chains (TopCat.of (short F a))).homology ((m + p) + q) ⟶
      (chains (TopCat.of (short F (a - L + 3 * ε)))).homology q :=
  (canonicalOperation m p F hε T hclosed hT).homology q

theorem homology_class (m p : ℕ) (F : ReversibleMetric (m + 1)) {ε a L : ℝ}
    (hε : 0 < ε)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
    (hclosed : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
    (hT : cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
      (short F L)) p T = 0) (q : ℕ) :
    (chains (TopCat.of (short F a))).homologyπ ((m + p) + q) ≫ homology m p F hε T hclosed hT q =
      (canonicalOperation m p F hε T hclosed hT).cycles q ≫
        (chains (TopCat.of (short F (a - L + 3 * ε)))).homologyπ q :=
  (canonicalOperation m p F hε T hclosed hT).homologyπ_homology q

end
end Finsler.FilteredPrismSelfCut
