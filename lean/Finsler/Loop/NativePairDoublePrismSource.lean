module

public import Finsler.Loop.DoubleRelativeTimeCylinder
public import Finsler.Loop.NativePairGoodCarrier
public import Finsler.Loop.NativeThetaCoefficientSixQuarters
public import Finsler.Topology.RelativeKronecker

/-! The ACTUAL native degree3d+2 relative input from TWO ORIGINAL
interval prisms of the OLD triple equator fundamental source.
All four time faces map into the already-proved native relative
boundary. The ORIGINAL cut class, with an explicit degree transport,
is paired with this actual input and evaluated on the original
uncapped double prism. Numeric local/global values remain separate. -/
@[expose] public section
namespace Finsler.NativePairDoublePrismSource
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.MeridianLoopFamily
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.BorelLoop
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

abbrev source {n : ℕ} (P : Sphere n) : TopCat.{0} := TopCat.of (NativeH1TripleMeridian.parameters P)

def reorderHomeomorph {n : ℕ} (P : Sphere n) :
    DoubleRelativeTimeCylinder.cylinder (DoubleRelativeTimeCylinder.cylinder (source P)) ≃ₜ
      NativeMeridianPairCoordinates.parameters P where
  toFun z := ((z.1, z.2.2.1.1), ((z.2.1, z.2.2.1.2), z.2.2.2))
  invFun z := (z.1.1, (z.2.1.1, ((z.1.2, z.2.1.2), z.2.2)))
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def reorder {n : ℕ} (P : Sphere n) :
    DoubleRelativeTimeCylinder.cylinder (DoubleRelativeTimeCylinder.cylinder (source P)) ⟶
      NativeMeridianPairCoordinates.parameters P := TopCat.ofHom ⟨reorderHomeomorph P, (reorderHomeomorph P).continuous⟩

theorem faces_map {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    Set.MapsTo (reorder P) (DoubleRelativeTimeCylinder.squareBoundary (source P))
      (NativePairBoundaryRelativeCut.bad P v₀) := by
  intro z hz
  change z.1 = 0 ∨ z.1 = 1 ∨ z.2.1 = 0 ∨ z.2.1 = 1 ∨ _ ∨ _
  rcases hz with (h | h) | (h | h)
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))

def pairMap {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    DoubleRelativeTimeCylinder.squarePair (source P) ⟶ NativePairBoundaryRelativeCut.pair P v₀ :=
  TopPair.ofSubsetMap (B := DoubleRelativeTimeCylinder.squareBoundary (source P))
    (B' := NativePairBoundaryRelativeCut.bad P v₀) (reorder P) (faces_map P v₀)

theorem pairMap_fst {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    TopPair.Hom.fst (pairMap P v₀) = reorder P := by
  ext z : 1
  exact TopPair.ofSubsetMap_fst_apply (B := DoubleRelativeTimeCylinder.squareBoundary (source P))
    (B' := NativePairBoundaryRelativeCut.bad P v₀) (reorder P) (faces_map P v₀) z

def relativeMap {n : ℕ} (P : Sphere n) (v₀ : equator P) := TopPair.singularChainComplexMap (pairMap P v₀) coeff

def rawComponent {n : ℕ} (P : Sphere n) (q : ℕ) :
    (chains (source P)).X q ⟶ (chains (NativeMeridianPairCoordinates.parameters P)).X (q + 2) :=
  ((DoubleRelativeTimeCylinder.homotopy (source P)).toSSet.chainComplexMap coeff).hom q (q + 1) ≫
    ((DoubleRelativeTimeCylinder.homotopy (DoubleRelativeTimeCylinder.cylinder (source P))).toSSet.chainComplexMap coeff).hom
      (q + 1) (q + 2) ≫ (push (reorder P)).f (q + 2)

def component {n : ℕ} (P : Sphere n) (v₀ : equator P) (q : ℕ) :=
  rawComponent P q ≫ ((NativePairBoundaryRelativeCut.pair P v₀).singularChainComplexπ coeff).f (q + 2)

def cycles {n : ℕ} (P : Sphere n) (v₀ : equator P) (q : ℕ) :=
  DoubleRelativeTimeCylinder.cycles (source P) q ≫ HomologicalComplex.cyclesMap (relativeMap P v₀) (q + 2)

theorem cycles_i {n : ℕ} (P : Sphere n) (v₀ : equator P) (q : ℕ) :
    cycles P v₀ q ≫ ((NativePairBoundaryRelativeCut.pair P v₀).singularChainComplex coeff).iCycles (q + 2) =
      (chains (source P)).iCycles q ≫ component P v₀ q := by
  unfold cycles
  rw [Category.assoc, HomologicalComplex.cyclesMap_i, ← Category.assoc,
    DoubleRelativeTimeCylinder.cycles_i, Category.assoc]
  unfold DoubleRelativeTimeCylinder.component component rawComponent
  simp only [Category.assoc]
  have he := congrArg (fun f => f.f (q + 2))
    (TopPair.singularChainComplexπ_pair_naturality (pairMap P v₀) coeff)
  change (push (TopPair.Hom.fst (pairMap P v₀))).f (q + 2) ≫
      ((NativePairBoundaryRelativeCut.pair P v₀).singularChainComplexπ coeff).f (q + 2) =
    ((DoubleRelativeTimeCylinder.squarePair (source P)).singularChainComplexπ coeff).f (q + 2) ≫
      (relativeMap P v₀).f (q + 2) at he
  rw [pairMap_fst] at he
  exact congrArg
    (fun k => (chains (source P)).iCycles q ≫
      ((DoubleRelativeTimeCylinder.homotopy (source P)).toSSet.chainComplexMap coeff).hom q (q + 1) ≫
      ((DoubleRelativeTimeCylinder.homotopy (DoubleRelativeTimeCylinder.cylinder (source P))).toSSet.chainComplexMap coeff).hom
        (q + 1) (q + 2) ≫ k) he.symm

def homology {n : ℕ} (P : Sphere n) (v₀ : equator P) (q : ℕ) :=
  DoubleRelativeTimeCylinder.homology (source P) q ≫
    TopPair.singularHomologyMap (pairMap P v₀) coeff (q + 2)

theorem homologyπ_homology {n : ℕ} (P : Sphere n) (v₀ : equator P) (q : ℕ) :
    (chains (source P)).homologyπ q ≫ homology P v₀ q =
      cycles P v₀ q ≫ ((NativePairBoundaryRelativeCut.pair P v₀).singularChainComplex coeff).homologyπ (q + 2) := by
  change (chains (source P)).homologyπ q ≫
    (DoubleRelativeTimeCylinder.homology (source P) q ≫ HomologicalComplex.homologyMap (relativeMap P v₀) (q + 2)) = _
  rw [← Category.assoc, DoubleRelativeTimeCylinder.homologyπ_homology, Category.assoc,
    HomologicalComplex.homologyπ_naturality, ← Category.assoc]
  rfl

def inputClass (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :=
  (homology P v₀ (3 * m)).hom (BasedMeridianProducts.tripleSource m hm P)

def inputCycle (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :=
  (cycles P v₀ (3 * m)).hom (NativeThetaCoefficientSixQuarters.sourceCycle m hm P)

theorem inputCycle_class (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    (((NativePairBoundaryRelativeCut.pair P v₀).singularChainComplex coeff).homologyπ (3 * m + 2)).hom
      (inputCycle m hm P v₀) = inputClass m hm P v₀ := by
  have he := ConcreteCategory.congr_hom (homologyπ_homology P v₀ (3 * m))
    (NativeThetaCoefficientSixQuarters.sourceCycle m hm P)
  change (homology P v₀ (3 * m)).hom
    (((chains (source P)).homologyπ (3 * m)).hom (NativeThetaCoefficientSixQuarters.sourceCycle m hm P)) =
      (((NativePairBoundaryRelativeCut.pair P v₀).singularChainComplex coeff).homologyπ (3 * m + 2)).hom
        (inputCycle m hm P v₀) at he
  have hc := NativeThetaCoefficientSixQuarters.sourceCycle_class m hm P
  change ((chains (source P)).homologyπ (3 * m)).hom
    (NativeThetaCoefficientSixQuarters.sourceCycle m hm P) = BasedMeridianProducts.tripleSource m hm P at hc
  rw [hc] at he
  exact he.symm

private theorem toAmbient_eq (Q : TopPair.{0}) (k : ℕ) (ψ : RelativeCupCochain.relative Q k) :
    (Q.singularChainComplexπ coeff).f k ≫ ψ = RelativeCupCochain.toAmbient Q k ψ := rfl

theorem pairing {n : ℕ} (P : Sphere n) (v₀ : equator P) (q : ℕ)
    (ψ : RelativeCupCochain.relative (NativePairBoundaryRelativeCut.pair P v₀) (q + 2))
    (hψ : RelativeCupCochain.differential (NativePairBoundaryRelativeCut.pair P v₀) (q + 2) ψ = 0)
    (c : (chains (source P)).cycles q) :
    RelativeKronecker.comparison (NativePairBoundaryRelativeCut.pair P v₀) (q + 2)
      (CochainClass.classOf (RelativeCup.cx (NativePairBoundaryRelativeCut.pair P v₀)) (q + 2) ψ hψ)
      ((homology P v₀ q).hom (((chains (source P)).homologyπ q).hom c)) =
        ((chains (source P)).iCycles q ≫ rawComponent P q ≫
          RelativeCupCochain.toAmbient (NativePairBoundaryRelativeCut.pair P v₀) (q + 2) ψ).hom c := by
  have he := ConcreteCategory.congr_hom (homologyπ_homology P v₀ q) c
  change (homology P v₀ q).hom (((chains (source P)).homologyπ q).hom c) =
    (((NativePairBoundaryRelativeCut.pair P v₀).singularChainComplex coeff).homologyπ (q + 2)).hom
      ((cycles P v₀ q).hom c) at he
  have h₀ := congrArg
    (RelativeKronecker.comparison (NativePairBoundaryRelativeCut.pair P v₀) (q + 2)
      (CochainClass.classOf (RelativeCup.cx (NativePairBoundaryRelativeCut.pair P v₀)) (q + 2) ψ hψ)) he
  have h₁ := RelativeKronecker.comparison_classOf (NativePairBoundaryRelativeCut.pair P v₀) (q + 2) ψ hψ
    ((cycles P v₀ q).hom c)
  have hi := ConcreteCategory.congr_hom (cycles_i P v₀ q) c
  change (((NativePairBoundaryRelativeCut.pair P v₀).singularChainComplex coeff).iCycles (q + 2)).hom
    ((cycles P v₀ q).hom c) = ((chains (source P)).iCycles q ≫ component P v₀ q).hom c at hi
  have hv := congrArg ψ.hom hi
  change _ = (((chains (source P)).iCycles q ≫ component P v₀ q) ≫ ψ).hom c at hv
  rw [component, Category.assoc, Category.assoc, toAmbient_eq] at hv
  exact h₀.trans (h₁.trans hv)

private theorem cast_closed (Q : TopPair.{0}) {i j : ℕ} (h : i = j)
    (ψ : RelativeCupCochain.relative Q i) (hψ : RelativeCupCochain.differential Q i ψ = 0) :
    RelativeCupCochain.differential Q j (RelativeCupCochain.cast Q h ψ) = 0 := by
  subst j
  exact hψ

private theorem cast_class (Q : TopPair.{0}) {i j : ℕ} (h : i = j)
    (ψ : RelativeCupCochain.relative Q i) (hψ : RelativeCupCochain.differential Q i ψ = 0) :
    (eqToHom (congrArg (fun k => Q.singularCohomology coeff (ZMod 2) coeff k) h)).hom
      (CochainClass.classOf (RelativeCup.cx Q) i ψ hψ) =
        CochainClass.classOf (RelativeCup.cx Q) j (RelativeCupCochain.cast Q h ψ) (cast_closed Q h ψ hψ) := by
  subst j
  rfl

theorem degree (m : ℕ) : (m + 1) + (m + (m + 1)) = 3 * m + 2 := by omega

def primitiveCocycle (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr4 : r ≤ 1 / 4) (hη4 : η ≤ 1 / 4) :=
  RelativeCupCochain.cast (NativePairBoundaryRelativeCut.pair P v₀) (degree m)
    (NativePairBoundaryRelativeCut.relativeCocycle m m P v₀ b hρ hρr hr hη hr4 hη4
      (classRepr _ m (MeridianLoopClass.H1TransgressionClass m)))

theorem primitive_closed (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr4 : r ≤ 1 / 4) (hη4 : η ≤ 1 / 4) :
    RelativeCupCochain.differential (NativePairBoundaryRelativeCut.pair P v₀) (3 * m + 2)
      (primitiveCocycle m P v₀ b hρ hρr hr hη hr4 hη4) = 0 :=
  cast_closed _ (degree m) _
    (NativePairBoundaryRelativeCut.relative_closed m m P v₀ b hρ hρr hr hη hr4 hη4 _ (classRepr_isCocycle _ m _))

def primitiveClass (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr4 : r ≤ 1 / 4) (hη4 : η ≤ 1 / 4) :=
  (eqToHom (congrArg (fun k => (NativePairBoundaryRelativeCut.pair P v₀).singularCohomology coeff (ZMod 2) coeff k)
    (degree m))).hom (NativePairBoundaryRelativeCut.originalPrimitiveClass m P v₀ b hρ hρr hr hη hr4 hη4)

theorem primitiveClass_represents (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr4 : r ≤ 1 / 4) (hη4 : η ≤ 1 / 4) :
    primitiveClass m P v₀ b hρ hρr hr hη hr4 hη4 =
      CochainClass.classOf (RelativeCup.cx (NativePairBoundaryRelativeCut.pair P v₀)) (3 * m + 2)
        (primitiveCocycle m P v₀ b hρ hρr hr hη hr4 hη4) (primitive_closed m P v₀ b hρ hρr hr hη hr4 hη4) :=
  cast_class _ (degree m) _
    (NativePairBoundaryRelativeCut.relative_closed m m P v₀ b hρ hρr hr hη hr4 hη4 _ (classRepr_isCocycle _ m _))

def branchPairing (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr4 : r ≤ 1 / 4) (hη4 : η ≤ 1 / 4) : ZMod 2 :=
  RelativeKronecker.comparison (NativePairBoundaryRelativeCut.pair P v₀) (3 * m + 2)
    (primitiveClass m P v₀ b hρ hρr hr hη hr4 hη4) (inputClass m hm P v₀)

theorem branchPairing_double_prism (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr4 : r ≤ 1 / 4) (hη4 : η ≤ 1 / 4) :
    branchPairing m hm P v₀ b hρ hρr hr hη hr4 hη4 =
      ((chains (source P)).iCycles (3 * m) ≫ rawComponent P (3 * m) ≫
        cochainCast (degree m) (NativePairBoundaryRelativeCut.cochain m m P v₀ b hρ hρr hr hη
          (classRepr _ m (MeridianLoopClass.H1TransgressionClass m)))).hom
            (NativeThetaCoefficientSixQuarters.sourceCycle m hm P) := by
  have he := pairing P v₀ (3 * m) (primitiveCocycle m P v₀ b hρ hρr hr hη hr4 hη4)
    (primitive_closed m P v₀ b hρ hρr hr hη hr4 hη4) (NativeThetaCoefficientSixQuarters.sourceCycle m hm P)
  have hc := NativeThetaCoefficientSixQuarters.sourceCycle_class m hm P
  change ((chains (source P)).homologyπ (3 * m)).hom
    (NativeThetaCoefficientSixQuarters.sourceCycle m hm P) = BasedMeridianProducts.tripleSource m hm P at hc
  rw [hc] at he
  have ha : RelativeCupCochain.toAmbient (NativePairBoundaryRelativeCut.pair P v₀) (3 * m + 2)
      (primitiveCocycle m P v₀ b hρ hρr hr hη hr4 hη4) =
        cochainCast (degree m) (NativePairBoundaryRelativeCut.cochain m m P v₀ b hρ hρr hr hη
          (classRepr _ m (MeridianLoopClass.H1TransgressionClass m))) := by
    rw [primitiveCocycle, RelativeCupCochain.toAmbient_cast, NativePairBoundaryRelativeCut.relative_toAmbient]
  rw [ha] at he
  unfold branchPairing
  rw [primitiveClass_represents]
  exact he

end
end Finsler.NativePairDoublePrismSource
