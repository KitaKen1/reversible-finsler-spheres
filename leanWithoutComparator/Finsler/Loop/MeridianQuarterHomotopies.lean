module

public import Finsler.Loop.MeridianLoopFamily
public import Finsler.Loop.RationalSphereArcCarrier
public import Finsler.Loop.UncappedTimeSplit

/-! The four ACTUAL meridian-loop pieces as genuine homotopies.
Their whole images lie in the two actual antipodal open sets, with
the varying/fixed equator evaluations as the intermediate endpoints. -/

@[expose] public section
namespace Finsler.MeridianQuarterHomotopies
open CategoryTheory Topology Finsler.SphereGeometry Finsler.MeridianLoopFamily
open Finsler.RationalSphereArc
open scoped RealInnerProductSpace
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward false
set_option maxHeartbeats 1200000

abbrev parameters {n : ℕ} (P : Sphere n) : TopCat.{0} := TopCat.of (equator P)

def constant {n : ℕ} (P Q : Sphere n) : parameters P ⟶ BorelEvaluation.sphere n :=
  TopCat.ofHom (ContinuousMap.const (equator P) Q)

def equatorMap {n : ℕ} (P : Sphere n) : parameters P ⟶ BorelEvaluation.sphere n :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

def outgoingH {n : ℕ} (P : Sphere n) : TopCat.Homotopy (constant P P) (equatorMap P) where
  toFun z := arc (outgoing P z.2) z.1
  continuous_toFun := by
    change Continuous (fun z : _root_.unitInterval × equator P => point (outgoing P z.2) z.1)
    have hc : Continuous (fun z : _root_.unitInterval × equator P => (outgoing P z.2, z.1)) := by
      unfold outgoing
      fun_prop
    exact (RationalSphereArc.point_continuous n).comp hc
  map_zero_left v := (arc (outgoing P v)).source
  map_one_left v := (arc (outgoing P v)).target

def incomingH {n : ℕ} (P : Sphere n) :
    TopCat.Homotopy (equatorMap P) (constant P (antipode P)) where
  toFun z := arc (incoming P z.2) z.1
  continuous_toFun := by
    change Continuous (fun z : _root_.unitInterval × equator P => point (incoming P z.2) z.1)
    have hc : Continuous (fun z : _root_.unitInterval × equator P => (incoming P z.2, z.1)) := by
      unfold incoming
      fun_prop
    exact (RationalSphereArc.point_continuous n).comp hc
  map_zero_left v := (arc (incoming P v)).source
  map_one_left v := (arc (incoming P v)).target

def returnIncomingH {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    TopCat.Homotopy (constant P (antipode P)) (constant P v₀.val) where
  toFun z := (arc (incoming P v₀)).symm z.1
  continuous_toFun := (arc (incoming P v₀)).symm.continuous.comp continuous_fst
  map_zero_left _ := (arc (incoming P v₀)).symm.source
  map_one_left _ := (arc (incoming P v₀)).symm.target

def returnOutgoingH {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    TopCat.Homotopy (constant P v₀.val) (constant P P) where
  toFun z := (arc (outgoing P v₀)).symm z.1
  continuous_toFun := (arc (outgoing P v₀)).symm.continuous.comp continuous_fst
  map_zero_left _ := (arc (outgoing P v₀)).symm.source
  map_one_left _ := (arc (outgoing P v₀)).symm.target

def upper {n : ℕ} (P : Sphere n) : Set (BorelEvaluation.sphere n) := {antipode P}ᶜ
def lower {n : ℕ} (P : Sphere n) : Set (BorelEvaluation.sphere n) := {P}ᶜ

theorem outgoing_upper {n : ℕ} (P : Sphere n) (z : _root_.unitInterval × parameters P) :
    outgoingH P z ∈ upper P := by
  change arc (outgoing P z.2) z.1 ≠ antipode P
  intro h
  exact RationalSphereArcCarrier.point_ne_neg_left (outgoing P z.2) z.1 (congrArg Subtype.val h)

theorem incoming_lower {n : ℕ} (P : Sphere n) (z : _root_.unitInterval × parameters P) :
    incomingH P z ∈ lower P := by
  change arc (incoming P z.2) z.1 ≠ P
  intro h
  have he := congrArg Subtype.val h
  change (point (incoming P z.2) z.1 : Ambient n) = (P : Ambient n) at he
  have hv : (point (incoming P z.2) z.1 : Ambient n) =
      -((incoming P z.2).val.2 : Ambient n) := by
    simpa only [incoming, antipode, neg_neg] using he
  exact RationalSphereArcCarrier.point_ne_neg_right (incoming P z.2) z.1 hv

theorem returnIncoming_lower {n : ℕ} (P : Sphere n) (v₀ : equator P)
    (z : _root_.unitInterval × parameters P) : returnIncomingH P v₀ z ∈ lower P := by
  exact incoming_lower P (unitInterval.symm z.1, v₀)

theorem returnOutgoing_upper {n : ℕ} (P : Sphere n) (v₀ : equator P)
    (z : _root_.unitInterval × parameters P) : returnOutgoingH P v₀ z ∈ upper P := by
  exact outgoing_upper P (unitInterval.symm z.1, v₀)

theorem pole_ne_antipode {n : ℕ} (P : Sphere n) : P ≠ antipode P := by
  intro h
  have he := congrArg (fun Q : Sphere n => inner ℝ (P : Ambient n) (Q : Ambient n)) h
  change inner ℝ (P : Ambient n) (P : Ambient n) = inner ℝ (P : Ambient n) (-(P : Ambient n)) at he
  rw [inner_neg_right, real_inner_self_eq_norm_sq, mem_sphere_zero_iff_norm.mp P.property] at he
  norm_num at he

theorem open_upper {n : ℕ} (P : Sphere n) : IsOpen (upper P) := isOpen_compl_singleton
theorem open_lower {n : ℕ} (P : Sphere n) : IsOpen (lower P) := isOpen_compl_singleton

theorem cover {n : ℕ} (P : Sphere n) : upper P ∪ lower P = Set.univ := by
  ext Q
  simp only [upper, lower, Set.mem_union, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  by_cases h : Q = P
  · left
    simpa only [h] using pole_ne_antipode P
  · exact Or.inr h

end
end Finsler.MeridianQuarterHomotopies
