module

public import Finsler.Loop.NativeH1TripleMeridian
public import Finsler.Loop.LengthFilteredLoopRotation
public import Finsler.Loop.CompactInputShortMaps
public import Finsler.Loop.MeridianThetaCutCoefficient
public import Finsler.Loop.EmptySingularChains
public import Finsler.Analysis.CompactH1Alignment

/-! A genuine strict length-cut representative of the SAME Theta
candidate, for every actual metric. The original filtered cut is
instantiated with the actual primitive tested representative and
L=0, whose support condition is genuinely discharged. No positive
HR saving or uniform bound over powers is claimed. -/
@[expose] public section
namespace Finsler.NativeThetaLengthCut
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.BorelLoop
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.MeridianLoopFamily Finsler.StrictLengthEnergyBridge
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

theorem exists_bound {n : ℕ} (F : ReversibleMetric n) (P : Sphere n) (v₀ : equator P) :
    ∃ A : ℝ, 0 < A ∧ ∀ z : NativeH1TripleMeridian.parameters P,
      SobolevLength.length F (NativeH1TripleMeridian.native P v₀ z) < A := by
  have hK : IsCompact (Set.univ : Set (NativeH1TripleMeridian.parameters P)) := by
    simpa only [Set.univ_prod_univ] using
      ((equator_compact P).prod (equator_compact P)).prod (equator_compact P)
  obtain ⟨M, hM, hb⟩ := CompactH1Alignment.exists_length_bound F hK
    (NativeH1TripleMeridian.native P v₀) (NativeH1TripleMeridian.continuous_native P v₀).continuousOn
  exact ⟨M + 1, by linarith, fun z => (hb z (Set.mem_univ z)).trans_lt (by linarith)⟩

def bound {n : ℕ} (F : ReversibleMetric n) (P : Sphere n) (v₀ : equator P) : ℝ :=
  (exists_bound F P v₀).choose

theorem bound_positive {n : ℕ} (F : ReversibleMetric n) (P : Sphere n) (v₀ : equator P) :
    0 < bound F P v₀ := (exists_bound F P v₀).choose_spec.1

theorem bound_spec {n : ℕ} (F : ReversibleMetric n) (P : Sphere n) (v₀ : equator P)
    (z : NativeH1TripleMeridian.parameters P) :
    SobolevLength.length F (NativeH1TripleMeridian.native P v₀ z) < bound F P v₀ :=
  (exists_bound F P v₀).choose_spec.2 z

def family {n : ℕ} (F : ReversibleMetric n) (P : Sphere n) (v₀ : equator P) :=
  CompactInputShortMaps.family (NativeH1TripleMeridian.family P v₀).hom F (bound F P v₀) (bound_spec F P v₀)

theorem family_full {n : ℕ} (F : ReversibleMetric n) (P : Sphere n) (v₀ : equator P) :
    family F P v₀ ≫ LengthFilteredLoopRotation.full F (bound F P v₀) =
      NativeH1TripleMeridian.family P v₀ :=
  CompactInputShortMaps.family_source _ _ _ _

def cube (m : ℕ) (hm : 1 ≤ m) (F : ReversibleMetric (m + 1)) (P : Sphere (m + 1)) (v₀ : equator P) :=
  (homologyPushZMod2 (family F P v₀) (3 * m)).hom (BasedMeridianProducts.tripleSource m hm P)

def theta (m : ℕ) (hm : 1 ≤ m) (F : ReversibleMetric (m + 1)) (P : Sphere (m + 1)) (v₀ : equator P) :=
  (LengthFilteredLoopRotation.BV F (bound F P v₀) (3 * m)).hom (cube m hm F P v₀)

theorem theta_full (m : ℕ) (hm : 1 ≤ m) (F : ReversibleMetric (m + 1)) (P : Sphere (m + 1)) (v₀ : equator P) :
    (homologyPushZMod2 (LengthFilteredLoopRotation.full F (bound F P v₀)) (3 * m + 1)).hom
      (theta m hm F P v₀) = MeridianRotationClasses.H1Theta m hm P v₀ := by
  have hc := ConcreteCategory.congr_hom
    (((singularHomologyFunctor (ModuleCat.{0} (ZMod 2)) (3 * m)).obj coeff).map_comp
      (family F P v₀) (LengthFilteredLoopRotation.full F (bound F P v₀))) (BasedMeridianProducts.tripleSource m hm P)
  rw [family_full] at hc
  have he := ConcreteCategory.congr_hom
    (LengthFilteredLoopRotation.BV_full F (bound F P v₀) (3 * m)) (cube m hm F P v₀)
  have hcube : (homologyPushZMod2 (LengthFilteredLoopRotation.full F (bound F P v₀)) (3 * m)).hom
      (cube m hm F P v₀) = MeridianRotationClasses.H1Cube m hm P v₀ :=
    hc.symm.trans (NativeH1TripleMeridian.cube_original m hm P v₀)
  change (H1LoopRotation.BV (m + 1) (3 * m)).hom
    ((homologyPushZMod2 (LengthFilteredLoopRotation.full F (bound F P v₀)) (3 * m)).hom (cube m hm F P v₀)) =
    (homologyPushZMod2 (LengthFilteredLoopRotation.full F (bound F P v₀)) (3 * m + 1)).hom (theta m hm F P v₀) at he
  rw [hcube] at he
  exact he.symm

private theorem push_cast {X Y : TopCat.{0}} (f : X ⟶ Y) {i j : ℕ} (h : i = j)
    (z : homologyZMod2 X i) :
    (homologyPushZMod2 f j).hom ((eqToHom (congrArg (fun k => homologyZMod2 X k) h)).hom z) =
      (eqToHom (congrArg (fun k => homologyZMod2 Y k) h)).hom ((homologyPushZMod2 f i).hom z) := by
  subst j
  rfl

def input (m : ℕ) (hm : 1 ≤ m) (F : ReversibleMetric (m + 1)) (P : Sphere (m + 1)) (v₀ : equator P) :
    homologyZMod2 (lengthSpace F (bound F P v₀)) ((m + m) + (m + 1)) :=
  (eqToHom (congrArg (fun q => homologyZMod2 (lengthSpace F (bound F P v₀)) q)
    (by omega : 3 * m + 1 = (m + m) + (m + 1)))).hom (theta m hm F P v₀)

theorem input_full (m : ℕ) (hm : 1 ≤ m) (F : ReversibleMetric (m + 1)) (P : Sphere (m + 1)) (v₀ : equator P) :
    (homologyPushZMod2 (LengthFilteredLoopRotation.full F (bound F P v₀)) ((m + m) + (m + 1))).hom
      (input m hm F P v₀) = MeridianThetaCutCoefficient.thetaInput m hm P v₀ := by
  have h := push_cast (LengthFilteredLoopRotation.full F (bound F P v₀))
    (show 3 * m + 1 = (m + m) + (m + 1) by omega) (theta m hm F P v₀)
  rw [theta_full] at h
  exact h

theorem empty_support {n : ℕ} (F : ReversibleMetric n) (p : ℕ)
    (T : singularCochainGroup (ZMod 2) (Loops n) p) :
    cochainPullback (SupportedCap.subspaceMap (Loops n) (SelfCutOscillation.short F 0)) p T = 0 := by
  have : IsEmpty (SelfCutOscillation.short F 0) := short_empty F 0 le_rfl
  exact (EmptySingularChains.chains_zero (TopCat.of (SelfCutOscillation.short F 0)) p).eq_of_src _ _

def cut (m : ℕ) (hm : 1 ≤ m) (F : ReversibleMetric (m + 1)) (P : Sphere (m + 1)) (v₀ : equator P)
    {ε : ℝ} (hε : 0 < ε) :=
  ((FilteredPrismSelfCut.canonicalOperation m m F hε
    (classRepr _ m (MeridianLoopClass.H1TransgressionClass m)) (classRepr_isCocycle _ m _)
    (empty_support F m _) (a := bound F P v₀)).homology (m + 1)).hom (input m hm F P v₀)

theorem cut_full (m : ℕ) (hm : 1 ≤ m) (F : ReversibleMetric (m + 1)) (P : Sphere (m + 1)) (v₀ : equator P)
    {ε : ℝ} (hε : 0 < ε) :
    (homologyPushZMod2 (SupportedCap.subspaceMap (Loops (m + 1))
      (SelfCutOscillation.short F (bound F P v₀ - 0 + 3 * ε))) (m + 1)).hom (cut m hm F P v₀ hε) =
        MeridianThetaCutCoefficient.cutTheta m hm P v₀ := by
  have h := CanonicalGlobalSelfCutFiltered.original_filtered m hm m F hε
    (classRepr _ m (MeridianLoopClass.H1TransgressionClass m)) (classRepr_isCocycle _ m _)
    (empty_support F m _) (m + 1) (input m hm F P v₀)
  rw [cocycleClass_classRepr] at h
  exact h.trans (congrArg
    ((CanonicalGlobalSelfCut.map m m (m + 1) (MeridianLoopClass.H1TransgressionClass m)).hom)
    (input_full m hm F P v₀))

end
end Finsler.NativeThetaLengthCut
