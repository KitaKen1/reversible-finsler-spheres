module

public import Finsler.Geometry.DiagonalGeometry
public import Finsler.Topology.SphereTopClass
public import Finsler.Topology.SpherePuncturedEvaluation
public import Finsler.Topology.CochainComparison
public import TauCeti.AlgebraicTopology.Cohomology.HomotopyInvariance

/-! The actual F₂ relative diagonal class, from the two sphere top classes.
The deleted diagonal retracts to the antidiagonal. Its projections pull the
unique nonzero top class back equally, so their sum has a genuine relative lift. -/

@[expose] public section

namespace Finsler.DiagonalCohomology

open CategoryTheory SphereOddDegree
open Finsler.SphereGeometry Finsler.DiagonalGeometry Finsler.SphereTopClass
open Finsler.BorelEvaluation Finsler.CochainComparison
open Set

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

theorem homotopy_pullback {X Y : TopCat.{0}} {f g : X ⟶ Y} (H : TopCat.Homotopy f g)
    (k : ℕ) (a : cohomologyZMod2 Y k) :
    (cohPullback f k).hom a = (cohPullback g k).hom a := by
  apply (Finsler.CochainComparison.cohomologyEquiv X k).injective
  change (cohomologyIso X k).hom.hom ((cohPullback f k).hom a) =
    (cohomologyIso X k).hom.hom ((cohPullback g k).hom a)
  rw [cohomology_natural_apply, cohomology_natural_apply]
  exact ConcreteCategory.congr_hom (H.congr_singularCohomologyMap coeff (ZMod 2) coeff k) _

theorem pullback_id (X : TopCat.{0}) (k : ℕ) (a : cohomologyZMod2 X k) :
    (cohPullback (𝟙 X) k).hom a = a := by
  exact congrArg (fun f => f.hom a) ((singularCohomologyZMod2 k).map_id (Opposite.op X))

theorem homeomorphism_top (n : ℕ) (hn : 1 ≤ n) (e : Sphere n ≃ₜ Sphere n) :
    (cohPullback (TopCat.ofHom ⟨e, e.continuous⟩) n).hom (topClass n hn) = topClass n hn := by
  apply eq_topClass_of_ne_zero
  intro hzero
  let f : sphere n ⟶ sphere n := TopCat.ofHom ⟨e, e.continuous⟩
  let g : sphere n ⟶ sphere n := TopCat.ofHom ⟨e.symm, e.symm.continuous⟩
  have hid : g ≫ f = 𝟙 (sphere n) := by
    ext x : 1
    exact e.apply_symm_apply x
  have hz : (cohPullback (g ≫ f) n).hom (topClass n hn) = 0 := by
    rw [Cup.pullback_comp, hzero, map_zero]
  rw [hid, pullback_id] at hz
  exact topClass_ne_zero n hn hz

def antiMap (n : ℕ) : sphere n ⟶ sphere n := TopCat.ofHom (antipodal n)

theorem antipodal_top (n : ℕ) (hn : 1 ≤ n) :
    (cohPullback (antiMap n) n).hom (topClass n hn) = topClass n hn :=
  homeomorphism_top n hn (antipodalHomeomorph n)

def product (n : ℕ) : TopCat.{0} := TopCat.of (Sphere n × Sphere n)
def diagonalPair (n : ℕ) : TopPair.{0} := TopPair.ofSubset (X := product n) (deleted n)
def prFirst (n : ℕ) : product n ⟶ sphere n := TopCat.ofHom ⟨Prod.fst, continuous_fst⟩
def prSecond (n : ℕ) : product n ⟶ sphere n := TopCat.ofHom ⟨Prod.snd, continuous_snd⟩

theorem deleted_projection_top (n : ℕ) (hn : 1 ≤ n) :
    (cohPullback ((diagonalPair n).map ≫ prSecond n) n).hom (topClass n hn) =
      (cohPullback ((diagonalPair n).map ≫ prFirst n) n).hom (topClass n hn) := by
  let H : TopCat.Homotopy ((diagonalPair n).map ≫ prSecond n)
      (((diagonalPair n).map ≫ prFirst n) ≫ antiMap n) := projectionHomotopy n
  rw [homotopy_pullback H, Cup.pullback_comp, antipodal_top]

def ambientClass (n : ℕ) (hn : 1 ≤ n) : cohomologyZMod2 (product n) n :=
  (cohPullback (prFirst n) n).hom (topClass n hn) +
    (cohPullback (prSecond n) n).hom (topClass n hn)

theorem restriction_zero (n : ℕ) (hn : 1 ≤ n) :
    (cohPullback (diagonalPair n).map n).hom (ambientClass n hn) = 0 := by
  let a := (cohPullback (diagonalPair n).map n).hom
    ((cohPullback (prFirst n) n).hom (topClass n hn))
  have h1 := Cup.pullback_comp (diagonalPair n).map (prFirst n) n (topClass n hn)
  have h2 := Cup.pullback_comp (diagonalPair n).map (prSecond n) n (topClass n hn)
  have he : (cohPullback (diagonalPair n).map n).hom
      ((cohPullback (prSecond n) n).hom (topClass n hn)) = a :=
    h2.symm.trans ((deleted_projection_top n hn).trans h1)
  calc
    _ = a + (cohPullback (diagonalPair n).map n).hom
        ((cohPullback (prSecond n) n).hom (topClass n hn)) := map_add _ _ _
    _ = a + a := congrArg (fun b => a + b) he
    _ = ((1 : ZMod 2) + 1) • a := by rw [add_smul, one_smul]
    _ = 0 := by
      rw [show (1 : ZMod 2) + 1 = 0 from by decide, zero_smul]

theorem exists_relative_diagonal (n : ℕ) (hn : 1 ≤ n) :
    ∃ T : (diagonalPair n).singularCohomology coeff (ZMod 2) coeff n,
      ((diagonalPair n).singularCohomologyπ coeff (ZMod 2) coeff n).hom T =
        Finsler.CochainComparison.cohomologyEquiv (product n) n (ambientClass n hn) :=
  Finsler.CochainComparison.relative_lift (diagonalPair n) n (ambientClass n hn)
    (restriction_zero n hn)

def relativeClass (n : ℕ) (hn : 1 ≤ n) :
    (diagonalPair n).singularCohomology coeff (ZMod 2) coeff n :=
  (exists_relative_diagonal n hn).choose

theorem relativeClass_image (n : ℕ) (hn : 1 ≤ n) :
    ((diagonalPair n).singularCohomologyπ coeff (ZMod 2) coeff n).hom (relativeClass n hn) =
      Finsler.CochainComparison.cohomologyEquiv (product n) n (ambientClass n hn) :=
  (exists_relative_diagonal n hn).choose_spec

theorem relativeClass_pool_image (n : ℕ) (hn : 1 ≤ n) :
    (relativeToPool (diagonalPair n) n).hom (relativeClass n hn) = ambientClass n hn := by
  change (Finsler.CochainComparison.cohomologyEquiv (product n) n).symm
    (((diagonalPair n).singularCohomologyπ coeff (ZMod 2) coeff n).hom (relativeClass n hn)) = _
  rw [relativeClass_image, LinearEquiv.symm_apply_apply]

def fiber (n : ℕ) (y : Sphere n) : sphere n ⟶ product n :=
  TopCat.ofHom ⟨fun x => (y, x), continuous_const.prodMk continuous_id⟩

theorem fiber_pullback (n : ℕ) (hn : 1 ≤ n) (y : Sphere n) :
    (cohPullback (fiber n y) n).hom (ambientClass n hn) = topClass n hn := by
  have hz : (cohPullback (fiber n y ≫ prFirst n) n).hom (topClass n hn) = 0 :=
    Finsler.SpherePuncturedEvaluation.evaluation_topClass_zero n hn
      (antipodalHomeomorph n y) (fiber n y ≫ prFirst n)
      (fun _ => sphere_ne_antipodal y)
  have hid : fiber n y ≫ prSecond n = 𝟙 (sphere n) := by ext x : 1; rfl
  change (cohPullback (fiber n y) n).hom
    ((cohPullback (prFirst n) n).hom (topClass n hn) +
      (cohPullback (prSecond n) n).hom (topClass n hn)) = _
  rw [map_add, ← Cup.pullback_comp, ← Cup.pullback_comp, hz, hid, pullback_id, zero_add]

theorem ambientClass_ne_zero (n : ℕ) (hn : 1 ≤ n) : ambientClass n hn ≠ 0 := by
  intro h
  obtain ⟨y, hy⟩ := (NormedSpace.sphere_nonempty (E := Ambient n) (x := (0 : Ambient n))).mpr zero_le_one
  have he := fiber_pullback n hn ⟨y, hy⟩
  rw [h, map_zero] at he
  exact topClass_ne_zero n hn he.symm

theorem relativeClass_ne_zero (n : ℕ) (hn : 1 ≤ n) : relativeClass n hn ≠ 0 := by
  intro h
  have he := relativeClass_pool_image n hn
  rw [h, map_zero] at he
  exact ambientClass_ne_zero n hn he.symm


end
end Finsler.DiagonalCohomology
