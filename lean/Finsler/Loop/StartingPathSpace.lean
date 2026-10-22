module

public import Finsler.Loop.BasedLoopPathSpace
public import Finsler.Loop.SphereProductHomologyDetection

/-! The ACTUAL compact-open space of paths with one fixed start and
free endpoint. Scaling the time parameter gives a genuine continuous
contraction and hence actual positive-degree homology zero. -/
@[expose] public section
namespace Finsler.StartingPathSpace
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000
local notation "I" => _root_.unitInterval

abbrev space (X : TopCat.{0}) (x : X) : TopCat.{0} := TopCat.of {p : C(I, X) // p 0 = x}

def endpoint (X : TopCat.{0}) (x : X) : space X x ⟶ X :=
  TopCat.ofHom ⟨fun p => p.val 1, (continuous_eval_const 1).comp continuous_subtype_val⟩

def constant (X : TopCat.{0}) (x : X) : space X x := ⟨ContinuousMap.const I x, rfl⟩

def scale (t s : I) : I := ⟨(t : ℝ) * (s : ℝ), mul_nonneg t.property.1 s.property.1, by
  calc (t : ℝ) * s ≤ 1 * s := mul_le_mul_of_nonneg_right t.property.2 s.property.1
    _ = s := one_mul _
    _ ≤ 1 := s.property.2⟩

theorem scale_zero (s : I) : scale 0 s = 0 := Subtype.ext (by simp [scale])
theorem scale_one (s : I) : scale 1 s = s := Subtype.ext (by simp [scale])
theorem scale_right_zero (t : I) : scale t 0 = 0 := Subtype.ext (by simp [scale])
theorem scale_continuous : Continuous (fun q : I × I => scale q.1 q.2) :=
  ((continuous_subtype_val.comp continuous_fst).mul
    (continuous_subtype_val.comp continuous_snd)).subtype_mk _

def initialSegment (X : TopCat.{0}) (x : X) (t : I) (p : space X x) : space X x :=
  ⟨⟨fun s => p.val (scale t s), p.val.continuous.comp
    (scale_continuous.comp (continuous_const.prodMk continuous_id))⟩,
    by change p.val (scale t 0) = x; rw [scale_right_zero]; exact p.property⟩

theorem initialSegment_continuous (X : TopCat.{0}) (x : X) :
    Continuous (fun q : I × space X x => initialSegment X x q.1 q.2) := by
  apply Continuous.subtype_mk
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact continuous_eval.comp
    ((continuous_subtype_val.comp (continuous_snd.comp continuous_fst)).prodMk
      (scale_continuous.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)))

theorem initialSegment_zero (X : TopCat.{0}) (x : X) (p : space X x) : initialSegment X x 0 p = constant X x := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro s
  change p.val (scale 0 s) = x
  rw [scale_zero]
  exact p.property

theorem initialSegment_one (X : TopCat.{0}) (x : X) (p : space X x) : initialSegment X x 1 p = p := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro s
  change p.val (scale 1 s) = p.val s
  rw [scale_one]

def expansion (X : TopCat.{0}) (x : X) :
    ContinuousMap.Homotopy (ContinuousMap.const (space X x) (constant X x)) (ContinuousMap.id (space X x)) where
  toFun q := initialSegment X x q.1 q.2
  continuous_toFun := initialSegment_continuous X x
  map_zero_left := initialSegment_zero X x
  map_one_left := initialSegment_one X x

theorem contractible (X : TopCat.{0}) (x : X) : ContractibleSpace (space X x) :=
  (contractible_iff_id_nullhomotopic (space X x)).mpr ⟨constant X x, ⟨(expansion X x).symm⟩⟩

theorem positive_homology_zero (X : TopCat.{0}) (x : X) (k : ℕ) :
    IsZero (homologyZMod2 (space X x) (k + 1)) := by
  have := contractible X x
  exact (TauCeti.isZero_reducedSingularHomologyFunctor_of_contractibleSpace coeff (space X x) (k + 1)).of_iso
    ((TauCeti.reducedSingularHomologySuccIso coeff k).app (space X x)).symm

end
end Finsler.StartingPathSpace
