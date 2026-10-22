import SurfaceLocalHomology
import Finsler.Geometry.PolygonModel

/-!
# From polygon local classes to genuine Sobolev loop local classes

Sampling is a left inverse to the actual broken-geodesic map. Both maps
preserve the strict lower-energy part and the distinguished point, so they
restrict to maps of critical-carrier pairs. Their literal retraction identity
proves injectivity on relative singular homology. Consequently a nonzero
polygon class cannot disappear upon inclusion into the actual H¹ loop space.

For every closed geodesic and every strictly larger energy cut, the existing
short-segment and fine-sampling theorems construct a polygon model whose
distinguished broken geodesic is exactly the given parametrized geodesic.
This result does not address inclusion into a critical orbit or an upper
energy sublevel.
-/

namespace Finsler.SurfacePolygonHomology

open CategoryTheory Set
open Finsler.Geometry Finsler.SphereGeometry Finsler.IntervalSobolev
open Finsler.PolygonModel Finsler.PolygonSampling Finsler.PolygonLoop
open Finsler.PolygonCritical
open Finsler.SurfaceLocalHomology

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 400000

variable {n N : ℕ} {F : ReversibleMetric n} {a : ℝ} [NeZero N]
    (M : PolygonModelData F a N)

abbrev Short := {q : ZMod N → Sphere n // ShortPolygon M.δ q}

/-- The actual finite-dimensional energy, not a formal surrogate. -/
def polygonEnergy (q : Short M) : ℝ :=
  polyEnergy F N (fun i => (q.val i : Ambient n))

theorem energy_broken_eq (q : Short M) :
    SobolevEnergy.energy F (broken M q) = polygonEnergy M q := energy_broken M q

theorem polygonEnergy_continuous : Continuous (polygonEnergy M) := by
  have h := (SobolevEnergy.energy_continuous F).comp (broken_continuous M)
  simpa only [Function.comp_def, energy_broken_eq] using h

/-- Polygons strictly below the reference energy, with the reference point
adjoined, relative to the strict lower part. -/
abbrev polygonPair (p : Short M) : TopPair := criticalPair (polygonEnergy M) p

/-- The corresponding pair in the genuine strong H¹ sphere loop space. -/
abbrev loopPair (p : Short M) : TopPair := criticalPair (SobolevEnergy.energy F) (broken M p)

theorem carrier_energy_lt (p : Short M) (hp : polygonEnergy M p < a ^ 2)
    (u : criticalCarrier (SobolevEnergy.energy F) (broken M p)) :
    SobolevEnergy.energy F u.val < a ^ 2 := by
  rcases u.property with h | h
  · exact h.trans ((energy_broken_eq M p) ▸ hp)
  · rw [h, energy_broken_eq]
    exact hp

/-- Breaking the vertices into minimizing segments maps critical carriers. -/
def brokenCarrier (p : Short M) :
    C(criticalCarrier (polygonEnergy M) p,
      criticalCarrier (SobolevEnergy.energy F) (broken M p)) := by
  have hmem : ∀ q : criticalCarrier (polygonEnergy M) p,
      broken M q.val ∈ criticalCarrier (SobolevEnergy.energy F) (broken M p) := by
    intro q
    rcases q.property with h | h
    · exact Or.inl (by simpa only [energy_broken_eq] using h)
    · exact Or.inr (congrArg (broken M) h)
  exact ⟨fun q => ⟨broken M q.val, hmem q⟩,
    ((broken_continuous M).comp continuous_subtype_val).subtype_mk hmem⟩

/-- Sampling is continuous and never increases energy. All points of the
carrier lie below the cut on which the polygon model is defined. -/
def sampleCarrier (p : Short M) (hp : polygonEnergy M p < a ^ 2) :
    C(criticalCarrier (SobolevEnergy.energy F) (broken M p),
      criticalCarrier (polygonEnergy M) p) := by
  let sample : C(criticalCarrier (SobolevEnergy.energy F) (broken M p), Short M) :=
    ⟨fun u => ⟨samplePoly N u.val, sample_short M (carrier_energy_lt M p hp u)⟩,
      ((samplePoly_continuous N).comp continuous_subtype_val).subtype_mk _⟩
  have hmem : ∀ u, sample u ∈ criticalCarrier (polygonEnergy M) p := by
    intro u
    rcases u.property with h | h
    · apply Or.inl
      have hs := (polyEnergy_samplePoly_le (F := F) (N := N) u.val).trans_lt h
      exact hs.trans_eq (energy_broken_eq M p)
    · apply Or.inr
      apply Subtype.ext
      change samplePoly N u.val = p.val
      rw [h, sample_broken]
  exact ⟨fun u => ⟨sample u, hmem u⟩, sample.continuous.subtype_mk hmem⟩

/-- The broken-geodesic map between the two actual critical pairs. -/
def brokenPair (p : Short M) : polygonPair M p ⟶ loopPair M p :=
  TopPair.ofSubsetMap (TopCat.ofHom (brokenCarrier M p)) (by
    intro q hq
    change SobolevEnergy.energy F (broken M q.val) < SobolevEnergy.energy F (broken M p)
    rw [energy_broken_eq, energy_broken_eq]
    exact hq)

/-- Sampling between the two actual critical pairs. -/
def samplePair (p : Short M) (hp : polygonEnergy M p < a ^ 2) :
    loopPair M p ⟶ polygonPair M p :=
  TopPair.ofSubsetMap (TopCat.ofHom (sampleCarrier M p hp)) (by
    intro u hu
    change polyEnergy F N (fun i => (samplePoly N u.val i : Ambient n)) < polygonEnergy M p
    exact ((polyEnergy_samplePoly_le (F := F) (N := N) u.val).trans_lt hu).trans_eq (energy_broken_eq M p))

/-- The retraction is exact on both the ambient carrier and its lower part. -/
theorem brokenPair_samplePair (p : Short M) (hp : polygonEnergy M p < a ^ 2) :
    brokenPair M p ≫ samplePair M p hp = 𝟙 (polygonPair M p) := by
  ext : 1
  · ext x
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact sample_broken M x.val.val
  · ext x
    apply Subtype.ext
    apply Subtype.ext
    exact sample_broken M x.val

/-- The polygon local homology injects into the genuine loop local homology.
No assumption about nonvanishing, an abstract comparison map or an inverse
on homology is used: the left inverse is the actual sampling map. -/
theorem brokenPair_homology_injective (p : Short M) (hp : polygonEnergy M p < a ^ 2)
    (K : Type) [Field K] (j : ℕ) :
    Function.Injective (TopPair.singularHomologyMap (brokenPair M p) (ModuleCat.of K K) j) := by
  have h := congrArg (fun f => TopPair.singularHomologyMap f (ModuleCat.of K K) j)
    (brokenPair_samplePair M p hp)
  rw [TopPair.singularHomologyMap_comp, TopPair.singularHomologyMap_id] at h
  intro x y hxy
  have hx := ConcreteCategory.congr_hom h x
  have hy := ConcreteCategory.congr_hom h y
  change TopPair.singularHomologyMap (samplePair M p hp) (ModuleCat.of K K) j
    (TopPair.singularHomologyMap (brokenPair M p) (ModuleCat.of K K) j x) = x at hx
  change TopPair.singularHomologyMap (samplePair M p hp) (ModuleCat.of K K) j
    (TopPair.singularHomologyMap (brokenPair M p) (ModuleCat.of K K) j y) = y at hy
  exact hx.symm.trans ((congrArg _ hxy).trans hy)

/-- A constructed polygon class remains nonzero as a class of actual loops. -/
theorem brokenPair_class_ne_zero (p : Short M) (hp : polygonEnergy M p < a ^ 2)
    (K : Type) [Field K] (j : ℕ)
    (z : ↥((polygonPair M p).singularHomology (ModuleCat.of K K) j)) (hz : z ≠ 0) :
    TopPair.singularHomologyMap (brokenPair M p) (ModuleCat.of K K) j z ≠ 0 := by
  intro h
  apply hz
  apply brokenPair_homology_injective M p hp K j
  simpa only [map_zero] using h

section LocalDisk

variable {q : ℕ} (U : Set (Short M)) (f : C(Disk q, U))
    (hmax : ∀ x, x ≠ center q → polygonEnergy M (f x).val < polygonEnergy M (f (center q)).val)

/-- The maximal disk in a polygon neighborhood, followed by the actual
neighborhood inclusion and the actual broken-geodesic map. -/
def localDiskToLoops : TauCeti.diskBoundaryPair q ⟶ loopPair M (f (center q)).val :=
  familyMap
    (fun x : criticalCarrier (fun x : U => polygonEnergy M x.val) (f (center q)) =>
      polygonEnergy M x.val.val)
    (polygonEnergy M (f (center q)).val)
    (criticalFamily (fun x : U => polygonEnergy M x.val) f hmax)
    (fun x => hmax _ (boundary_ne_center q x)) ≫
  criticalInclusion (polygonEnergy M) U (f (center q)) ≫ brokenPair M (f (center q)).val

/-- This map represents precisely the broken-geodesic family specified by
the given vertices, including its parametrization. -/
theorem localDiskToLoops_apply (x : Disk q) :
    (TopPair.Hom.fst (localDiskToLoops M U f hmax) x).val = broken M (f x).val := rfl

include hmax in
/-- A maximal disk with a central-fiber energy minimum in an open polygon
neighborhood produces a nonzero class in the genuine loop critical pair.
Only geometric coordinate and energy conditions are assumed; neither a
nonzero homology class nor a comparison-map injectivity is an input. -/
theorem localDiskToLoops_class_ne_zero (hU : IsOpen U)
    (hp : polygonEnergy M (f (center q)).val < a ^ 2) (r : C(U, Disk q))
    (hmin : ∀ x : U, r x = center q → polygonEnergy M (f (center q)).val ≤ polygonEnergy M x.val)
    (hr : ∀ x, r (f x) = x) (K : Type) [Field K] :
    TopPair.singularHomologyMap (localDiskToLoops M U f hmax) (ModuleCat.of K K) q
      (diskClass q K) ≠ 0 := by
  have hi := isIso_criticalInclusion (polygonEnergy M) (polygonEnergy_continuous M)
    U hU (f (center q)) K q
  have hinj := (ConcreteCategory.bijective_of_isIso
    (TopPair.singularHomologyMap (criticalInclusion (polygonEnergy M) U (f (center q)))
      (ModuleCat.of K K) q)).1
  rw [localDiskToLoops, TopPair.singularHomologyMap_comp, TopPair.singularHomologyMap_comp]
  change TopPair.singularHomologyMap (brokenPair M (f (center q)).val) (ModuleCat.of K K) q
    (TopPair.singularHomologyMap (criticalInclusion (polygonEnergy M) U (f (center q)))
      (ModuleCat.of K K) q
      (TopPair.singularHomologyMap _ (ModuleCat.of K K) q (diskClass q K))) ≠ 0
  apply brokenPair_class_ne_zero M _ hp K q
  intro hz
  apply criticalClass_ne_zero (fun x : U => polygonEnergy M x.val) f r hmax hmin hr K
  apply hinj
  rw [map_zero]
  convert hz using 1

end LocalDisk

/-- An actual finite polygon presentation of a parametrized closed geodesic,
inside a strictly larger energy cut. -/
structure GeodesicModel (F : ReversibleMetric n) (g : Geodesics.ClosedGeodesic F) (a : ℝ) where
  vertices : ℕ
  [nonzero : NeZero vertices]
  model : PolygonModelData F a vertices
  point : Short model
  critical : PolyCritical F vertices point.val
  below : polygonEnergy model point < a ^ 2
  broken_eq : broken model point = SmoothSobolev.ofSmooth g.loop

attribute [instance] GeodesicModel.nonzero

/-- The model exists for every closed geodesic, with its point critical and
its broken path exactly equal to the original loop. No restriction to
nondegenerate or prime geodesics is imposed. -/
theorem nonempty_geodesicModel (F : ReversibleMetric n) (g : Geodesics.ClosedGeodesic F)
    {a : ℝ} (ha : SobolevEnergy.energy F (SmoothSobolev.ofSmooth g.loop) < a ^ 2) :
    Nonempty (GeodesicModel F g a) := by
  obtain ⟨S⟩ := exists_segmentData F
  obtain ⟨N₀, hN₀⟩ := exists_sample_spacing F (δ := S.δ) (a := a) S.pos
  obtain ⟨N₁, hN₁⟩ := sample_closedGeodesic S g
  obtain ⟨N₂, hN₂⟩ := broken_sample_closedGeodesic S g
  let N := max N₀ (max N₁ N₂) + 1
  have hN : 0 < N := by dsimp [N]; omega
  let : NeZero N := ⟨by omega⟩
  let M : PolygonModelData F a N :=
    PolygonModelData.mk S (hN₀ N (by dsimp [N]; omega) hN)
  obtain ⟨hs, hc, hE⟩ := hN₁ N (by dsimp [N]; omega)
  let p : Short M := ⟨samplePoly N (SmoothSobolev.ofSmooth g.loop), hs⟩
  refine ⟨⟨N, M, p, hc, ?_, ?_⟩⟩
  · exact hE.trans_lt ha
  · exact hN₂ N (by dsimp [N]; omega) hs

end
end Finsler.SurfacePolygonHomology
