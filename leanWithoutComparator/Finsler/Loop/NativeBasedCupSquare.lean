module

public import Finsler.Loop.CupSquareZeroTransport
public import Finsler.Loop.NativePrimitiveBVComparison
public import Finsler.Loop.MatchingZeroEndpointCohomology

/-! No divided-power presentation is assumed. The ORIGINAL nonzero
triple meridian forces the based double meridian to be nonzero.
Actual rank one and the two-sphere pullback then kill every ordinary
cup square in based-loop degree m, including m=2. -/
@[expose] public section
namespace Finsler.NativeBasedCupSquare
open CategoryTheory MonoidalCategory CartesianMonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.CochainComparison Finsler.MeridianLoopFamily
open Finsler.MatchingZeroEndpointCohomology
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1800000

private theorem cast_zero (X : TopCat.{0}) {i j : ℕ} (h : i = j) :
    CupUnit.absoluteCast X h 0 = 0 := by
  subst j
  rfl

variable (m : ℕ) (hm : 2 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P)

theorem cube_ne_zero : BasedMeridianProducts.cube m (by omega) P v₀ ≠ 0 := by
  intro hz
  have ho : MeridianRotationClasses.ordinaryCube m (by omega) P v₀ = 0 := by
    unfold MeridianRotationClasses.ordinaryCube
    rw [hz, map_zero]
  have hh : MeridianRotationClasses.H1Cube m (by omega) P v₀ = 0 := by
    unfold MeridianRotationClasses.H1Cube
    rw [ho, map_zero]
  have hc : NativePrimitiveBVComparison.cube m hm P v₀ = 0 := by
    unfold NativePrimitiveBVComparison.cube
    rw [hh, map_zero]
  have he := NativePrimitiveBVComparison.cube_pairing_one m hm P v₀
  rw [hc, map_zero] at he
  exact zero_ne_one he

theorem square_ne_zero : BasedMeridianProducts.square m (by omega) P v₀ ≠ 0 := by
  intro hz
  apply cube_ne_zero m hm P v₀
  unfold BasedMeridianProducts.cube
  rw [hz, map_zero]
  rfl

include hm v₀ in
private theorem rank_one (k : ℕ) (z : homologyZMod2 (BasedMeridianProducts.space P) (k * m))
    (hz : z ≠ 0) : Module.finrank (ZMod 2) (homologyZMod2 (BasedMeridianProducts.space P) (k * m)) = 1 := by
  obtain ⟨f, hf⟩ := PathSphereRankTower.path_embedding m (by omega) P P v₀ k
  have := Module.Finite.of_injective f hf
  have hl := (LinearMap.finrank_le_finrank_of_injective hf).trans_eq (Module.finrank_self (ZMod 2))
  change Module.finrank (ZMod 2) (homologyZMod2 (BasedMeridianProducts.space P) (k * m)) ≤ 1 at hl
  have hp := (Module.finrank_pos_iff_exists_ne_zero (R := ZMod 2)).mpr ⟨z, hz⟩
  omega

include hm v₀ in
theorem primitive_rank_one : Module.finrank (ZMod 2) (homologyZMod2 (BasedMeridianProducts.space P) m) = 1 := by
  have h := PathSphereRankTower.path_embedding m (by omega) P P v₀ 1
  rw [Nat.one_mul] at h
  obtain ⟨f, hf⟩ := h
  have := Module.Finite.of_injective f hf
  have hl := (LinearMap.finrank_le_finrank_of_injective hf).trans_eq (Module.finrank_self (ZMod 2))
  change Module.finrank (ZMod 2) (homologyZMod2 (BasedMeridianProducts.space P) m) ≤ 1 at hl
  have hp := (Module.finrank_pos_iff_exists_ne_zero (R := ZMod 2)).mpr
    ⟨BasedMeridianProducts.primitive m (by omega) P v₀, BasedMeridianProducts.primitive_ne_zero m (by omega) P v₀⟩
  omega

include hm v₀ in
theorem square_rank_one : Module.finrank (ZMod 2) (homologyZMod2 (BasedMeridianProducts.space P) (2 * m)) = 1 :=
  rank_one m hm P v₀ 2 _ (square_ne_zero m hm P v₀)

def transgression : cohomologyZMod2 (BasedMeridianProducts.space P) m :=
  (cohPullback (BasedMeridianProducts.forget P) m).hom (MeridianLoopClass.ordinaryTransgression m)

theorem transgression_pairing : (kroneckerMap (BasedMeridianProducts.space P) m).hom (transgression m P)
    (BasedMeridianProducts.primitive m (by omega) P v₀) = 1 := by
  have h := congrArg (fun l => l (BasedMeridianProducts.primitive m (by omega) P v₀))
    (kroneckerMap_naturality_apply (BasedMeridianProducts.forget P) m (MeridianLoopClass.ordinaryTransgression m))
  exact h.trans ((congrArg ((kroneckerMap _ m).hom (MeridianLoopClass.ordinaryTransgression m))
    (BasedMeridianProducts.forget_primitive m (by omega) P v₀)).trans
      (MeridianPrimitiveNonzero.ordinary_pairing_one m (by omega) P v₀))

include hm v₀ in
theorem class_zero_or_transgression (a : cohomologyZMod2 (BasedMeridianProducts.space P) m) :
    a = 0 ∨ a = transgression m P := by
  let c := (kroneckerMap _ m).hom a (BasedMeridianProducts.primitive m (by omega) P v₀)
  have hc : c = 0 ∨ c = 1 := by generalize c = d; fin_cases d <;> simp
  rcases hc with h | h
  · left
    apply CupSquareZeroTransport.equal_of_one_value _ m (primitive_rank_one m hm P v₀)
      (BasedMeridianProducts.primitive m (by omega) P v₀) (BasedMeridianProducts.primitive_ne_zero m (by omega) P v₀)
    exact h.trans (by simp)
  · right
    apply CupSquareZeroTransport.equal_of_one_value _ m (primitive_rank_one m hm P v₀)
      (BasedMeridianProducts.primitive m (by omega) P v₀) (BasedMeridianProducts.primitive_ne_zero m (by omega) P v₀)
    exact h.trans (transgression_pairing m hm P v₀).symm

theorem double_pullback : (cohPullback (BasedMeridianProducts.doubleFamily P v₀) m).hom (transgression m P) =
    leftClass m P v₀ + rightClass m P v₀ :=
  (Cup.pullback_comp (BasedMeridianProducts.doubleFamily P v₀) (BasedMeridianProducts.forget P) m _).symm.trans
    (double_transgression m P v₀)

include hm in
theorem right_square_zero : cupZMod2 (rightClass m P v₀) (rightClass m P v₀) = 0 := by
  exact (Cup.naturality (snd (E P) (E P)) m m (meridianClass m P v₀) (meridianClass m P v₀)).symm.trans
    ((congrArg (cohPullback (snd (E P) (E P)) (m + m)).hom
      (NativeBallDiagonalCohomology.equator_cohomology_zero m (m + m) P (by omega) (by omega) _)).trans (map_zero _))

include hm in
theorem double_square_zero : cupZMod2 (leftClass m P v₀ + rightClass m P v₀)
    (leftClass m P v₀ + rightClass m P v₀) = 0 := by
  change CupAtDegree.cup _ m m (m + m) rfl _ _ = 0
  rw [CupAtDegree.add_left]
  rw [CupAtDegree.comm _ m m (m + m) rfl (leftClass m P v₀) (leftClass m P v₀ + rightClass m P v₀),
    CupAtDegree.comm _ m m (m + m) rfl (rightClass m P v₀) (leftClass m P v₀ + rightClass m P v₀)]
  rw [CupAtDegree.add_left, CupAtDegree.add_left]
  have hl : CupAtDegree.cup (E P ⊗ E P) m m (m + m) rfl (leftClass m P v₀) (leftClass m P v₀) = 0 := left_square_zero m (by omega) P v₀
  have hr : CupAtDegree.cup (E P ⊗ E P) m m (m + m) rfl (rightClass m P v₀) (rightClass m P v₀) = 0 := right_square_zero m hm P v₀
  rw [hl, hr, zero_add, add_zero, CupAtDegree.comm _ m m (m + m) rfl (rightClass m P v₀) (leftClass m P v₀)]
  have h : ∀ x : cohomologyZMod2 (E P ⊗ E P) (m + m), x + x = 0 := by
    intro x
    have hzero : ((1 : ZMod 2) + 1) • x = 0 := by rw [show (1 : ZMod 2) + 1 = 0 from rfl, zero_smul]
    simpa only [add_smul, one_smul] using hzero
  exact h _

include hm v₀ in
theorem transgression_square_zero : cupZMod2 (transgression m P) (transgression m P) = 0 := by
  have h : CupAtDegree.cup (BasedMeridianProducts.space P) m m (2 * m) (by omega)
      (transgression m P) (transgression m P) = 0 := by
    apply CupSquareZeroTransport.equal_of_one_value _ _ (square_rank_one m hm P v₀)
      (BasedMeridianProducts.square m (by omega) P v₀) (square_ne_zero m hm P v₀)
    rw [← BasedMeridianProducts.doubleFamily_image m (by omega) P v₀]
    have hn := congrArg (fun l => l (BasedMeridianProducts.doubleSource m (by omega) P))
      (kroneckerMap_naturality_apply (BasedMeridianProducts.doubleFamily P v₀) (2 * m)
        (CupAtDegree.cup _ m m (2 * m) (by omega) (transgression m P) (transgression m P)))
    have hp : (cohPullback (BasedMeridianProducts.doubleFamily P v₀) (2 * m)).hom
        (CupAtDegree.cup _ m m (2 * m) (by omega) (transgression m P) (transgression m P)) = 0 := by
      rw [CupAtDegree.naturality, double_pullback]
      unfold CupAtDegree.cup
      rw [double_square_zero m hm P v₀]
      exact cast_zero _ _
    rw [hp, map_zero] at hn
    exact hn.symm.trans (by simp)
  apply CupIteration.absoluteCast_injective (BasedMeridianProducts.space P) (show m + m = 2 * m by omega)
  exact h.trans (cast_zero _ _).symm

include hm v₀ in
theorem square_zero (a : cohomologyZMod2 (BasedMeridianProducts.space P) m) : cupZMod2 a a = 0 := by
  rcases class_zero_or_transgression m hm P v₀ a with rfl | rfl
  · exact Cup.zero_cup _ _ _
  · exact transgression_square_zero m hm P v₀

end
end Finsler.NativeBasedCupSquare
