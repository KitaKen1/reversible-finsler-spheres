module

public import Finsler.Loop.FirstInputRotationFullTime
public import Finsler.Topology.TimePrismNaturality

/-! Compare the actual full-cut-time operations at the two rotation
slices in the identical length target. The whole cut-time prism and
the genuine source retraction remain in each endpoint chain formula. -/

@[expose] public section
namespace Finsler.FirstInputRotationTimeEndpoints

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier
open Finsler.FirstInputRotationCutCylinder

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R : ℝ)

def slice (s : _root_.unitInterval) : TopCat.of (CompactNearJoinParameters.tube α β R) ⟶ input α β R :=
  TopCat.ofHom ⟨fun z => (s, z), continuous_const.prodMk continuous_id⟩

def rotationHomotopy : TopCat.Homotopy (slice α β R 0) (slice α β R 1) where
  toFun z := (z.1, z.2)
  continuous_toFun := continuous_fst.prodMk continuous_snd
  map_zero_left _ := rfl
  map_one_left _ := rfl

def cylinderSlice (s : _root_.unitInterval) :
    TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R) ⟶ cylinder α β R :=
  TopCat.ofHom ⟨fun z => (z.1, (s, z.2)), by fun_prop⟩

theorem slice_prism (s : _root_.unitInterval) (d : ℕ) :
    (push (slice α β R s)).f d ≫ AnnularTimeTrim.prism (input α β R) d =
      AnnularTimeTrim.prism (TopCat.of (CompactNearJoinParameters.tube α β R)) d ≫
        (push (cylinderSlice α β R s)).f (d + 1) := by
  have hpre := TimePrismNaturality.prism_pre (AnnularTimeTrim.cylinder (input α β R)) (slice α β R s) d
  have hpost := TimePrismNaturality.prism_post
    (AnnularTimeTrim.cylinder (TopCat.of (CompactNearJoinParameters.tube α β R))) (cylinderSlice α β R s) d
  have hcongr := TimePrismNaturality.prism_congr
    ((AnnularTimeTrim.cylinder (input α β R)).comp (TopCat.Homotopy.refl (slice α β R s)))
    ((TopCat.Homotopy.refl (cylinderSlice α β R s)).comp
      (AnnularTimeTrim.cylinder (TopCat.of (CompactNearJoinParameters.tube α β R))))
    (by
      apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro z
      rfl) d
  exact hpre.trans (hcongr.trans hpost.symm)

variable (r : ℝ) (hR : R ≤ 1 / 2) (hr : r < 1) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (F : ReversibleMetric (m + 1))
  (B η : ℝ) (hη : 0 < η) (hρr : ρ < r)
  (hgood : FirstInputRotationTestedCap.Adequate α β R r hR hr F B η p T)
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)

def endpoint (s : _root_.unitInterval) :
    DegreeLoweringHomology.Map (chains (TopCat.of (CompactNearJoinParameters.tube α β R)))
      (chains (TopCat.of (JoinedFilteredCap.sublevel F B))) (m + p) :=
  (FirstInputRotationFullTime.retainedOperation α β R r hR hr p T h F B η hη hρr hgood hT).pre
    (push (slice α β R s))

theorem homology_eq (q : ℕ) :
    (endpoint α β R r hR hr p T h F B η hη hρr hgood hT 0).homology q =
      (endpoint α β R r hR hr p T h F B η hη hρr hgood hT 1).homology q := by
  dsimp only [endpoint]
  rw [DegreeLoweringHomology.Map.pre_homology, DegreeLoweringHomology.Map.pre_homology]
  exact congrArg (fun f => f ≫
    (FirstInputRotationFullTime.retainedOperation α β R r hR hr p T h F B η hη hρr hgood hT).homology q)
      (((rotationHomotopy α β R).toSSet.chainComplexMap coeff).homologyMap_eq ((m + p) + q))

theorem component_normal (s : _root_.unitInterval) (q : ℕ) :
    (endpoint α β R r hR hr p T h F B η hη hρr hgood hT s).component q =
      AnnularTimeTrim.prism (TopCat.of (CompactNearJoinParameters.tube α β R)) ((m + p) + q) ≫
        (push (cylinderSlice α β R s)).f ((m + p) + q + 1) ≫
          ClosedCapDegreeTransport.align m p
            (FirstInputRotationFullTime.retracted α β R r hR hr p T h F B η hη hρr hgood hT) q ≫
              (push (FirstInputRotationFilteredCap.retained α β R r hR hr F B)).f q := by
  change (push (slice α β R s)).f ((m + p) + q) ≫
    (FirstInputRotationFullTime.retainedOperation α β R r hR hr p T h F B η hη hρr hgood hT).component q = _
  rw [FirstInputRotationFullTime.retained_component_normal, ← Category.assoc,
    ← Category.assoc, slice_prism]
  simp only [Category.assoc]

private theorem transport_d_left (K : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ)
    (i i' j : ℕ) (hi : i = i') :
    eqToHom (congrArg K.X hi) ≫ K.d i' j = K.d i j := by
  subst i'
  simp only [eqToHom_refl, Category.id_comp]

theorem cycle_boundary (q : ℕ) :
    (chains (TopCat.of (CompactNearJoinParameters.tube α β R))).iCycles ((m + p) + q) ≫
      ((endpoint α β R r hR hr p T h F B η hη hρr hgood hT 0).component q -
        (endpoint α β R r hR hr p T h F B η hη hρr hgood hT 1).component q) =
      ((chains (TopCat.of (CompactNearJoinParameters.tube α β R))).iCycles ((m + p) + q) ≫
        ((rotationHomotopy α β R).toSSet.chainComplexMap coeff).hom ((m + p) + q) ((m + p) + q + 1) ≫
          eqToHom (congrArg (chains (input α β R)).X (Nat.add_assoc (m + p) q 1)) ≫
          (FirstInputRotationFullTime.retainedOperation α β R r hR hr p T h F B η hη hρr hgood hT).component (q + 1)) ≫
            (chains (TopCat.of (JoinedFilteredCap.sublevel F B))).d (q + 1) q := by
  let w := FirstInputRotationFullTime.retainedOperation α β R r hR hr p T h F B η hη hρr hgood hT
  let e := eqToHom (congrArg (chains (input α β R)).X (Nat.add_assoc (m + p) q 1))
  have hd : e ≫ (chains (input α β R)).d ((m + p) + (q + 1)) ((m + p) + q) =
      (chains (input α β R)).d ((m + p) + q + 1) ((m + p) + q) :=
    transport_d_left _ _ _ _ (Nat.add_assoc (m + p) q 1)
  have hw : (chains (input α β R)).d ((m + p) + q + 1) ((m + p) + q) ≫ w.component q =
      e ≫ w.component (q + 1) ≫ (chains (TopCat.of (JoinedFilteredCap.sublevel F B))).d (q + 1) q := by
    rw [← hd, Category.assoc, ← w.comm]
  have hb := congrArg (fun f => f ≫ w.component q)
    (TimePrismComparison.cycles_prism_boundary
      ((rotationHomotopy α β R).toSSet.chainComplexMap coeff) ((m + p) + q))
  rw [Category.assoc, hw] at hb
  simpa only [endpoint, DegreeLoweringHomology.Map.pre, w, e, push, Preadditive.sub_comp,
    Category.assoc] using hb.symm

end
end Finsler.FirstInputRotationTimeEndpoints
