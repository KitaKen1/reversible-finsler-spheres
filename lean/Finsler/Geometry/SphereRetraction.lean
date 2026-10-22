module

public import Finsler.Geometry.SphereVariation
public import Mathlib.Geometry.Manifold.ContMDiff.Basic

/-! Actual ambient normalization and its tangent map. Normalization is smooth
away from zero; its tangent map retracts the genuine sphere tangent bundle.
The fallback value at zero is excluded from every smoothness statement. -/

@[expose] public section

namespace Finsler.SphereRetraction

open Finsler.SphereGeometry Finsler.Geometry Finsler.Loops Finsler.Geodesics
open TauCeti.Manifold Function Set Bundle
open scoped Manifold ContDiff Topology

noncomputable section

variable {n : ℕ}

def nonzeroAmbient (n : ℕ) : TopologicalSpace.Opens (Ambient n) :=
  ⟨{q | q ≠ 0}, isClosed_singleton.isOpen_compl⟩

def rawNormalize (q : Ambient n) : Ambient n := ‖q‖⁻¹ • q

theorem rawNormalize_mem_sphere {q : Ambient n} (hq : q ≠ 0) :
    rawNormalize q ∈ Metric.sphere (0 : Ambient n) 1 := by
  simp [rawNormalize, norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hq)]

theorem rawNormalize_smoothAt {q : Ambient n} (hq : q ≠ 0) :
    ContDiffAt ℝ ∞ rawNormalize q :=
  ((contDiffAt_id.norm ℝ hq).inv (norm_ne_zero_iff.mpr hq)).smul contDiffAt_id

def normalizedNonzero (q : nonzeroAmbient n) : Sphere n :=
  ⟨rawNormalize q, rawNormalize_mem_sphere q.property⟩

theorem normalizedNonzero_smooth (n : ℕ) :
    ContMDiff 𝓘(ℝ, Ambient n) (𝓡 n) ∞ (normalizedNonzero (n := n)) := by
  have hs : ContMDiff 𝓘(ℝ, Ambient n) 𝓘(ℝ, Ambient n) ∞
      (fun q : nonzeroAmbient n => rawNormalize (q : Ambient n)) := by
    intro q
    exact contMDiffAt_subtype_iff.mpr
      (rawNormalize_smoothAt q.property).contMDiffAt
  exact hs.codRestrict_sphere (fun q => rawNormalize_mem_sphere q.property)

def northPole (n : ℕ) : Sphere n :=
  ⟨EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ), by simp⟩

def normalize (q : Ambient n) : Sphere n :=
  if hq : q = 0 then northPole n else normalizedNonzero ⟨q, hq⟩

theorem normalize_coe (q : nonzeroAmbient n) :
    normalize (q : Ambient n) = normalizedNonzero q := by
  have hq : (q : Ambient n) ≠ 0 := q.property
  simp [normalize, hq]

theorem normalize_smoothAt {q : Ambient n} (hq : q ≠ 0) :
    ContMDiffAt 𝓘(ℝ, Ambient n) (𝓡 n) ∞ normalize q := by
  have he : (fun p : nonzeroAmbient n => normalize (p : Ambient n)) =
      normalizedNonzero := funext normalize_coe
  apply (contMDiffAt_subtype_iff (x := (⟨q, hq⟩ : nonzeroAmbient n))).mp
  rw [he]
  exact (normalizedNonzero_smooth n).contMDiffAt

theorem normalize_inclusion (x : Sphere n) : normalize (x : Ambient n) = x := by
  have hx : (x : Ambient n) ≠ 0 := ne_zero_of_mem_unit_sphere x
  apply Subtype.ext
  simp [normalize, hx, normalizedNonzero, rawNormalize]

theorem normalize_comp_inclusion (n : ℕ) :
    normalize ∘ inclusion n = id := funext normalize_inclusion

def pairLift (z : Ambient n × Ambient n) :
    TangentBundle 𝓘(ℝ, Ambient n) (Ambient n) := ⟨z.1, z.2⟩

theorem pairLift_smooth (n : ℕ) :
    ContMDiff 𝓘(ℝ, Ambient n × Ambient n) (𝓘(ℝ, Ambient n)).tangent ∞
      (pairLift (n := n)) := by
  intro z
  apply Bundle.contMDiffAt_totalSpace.mpr
  refine ⟨contDiff_fst.contDiffAt.contMDiffAt, ?_⟩
  convert! contDiff_snd.contDiffAt.contMDiffAt using 1
  simp [pairLift]

def lift (z : Ambient n × Ambient n) : Total n :=
  tangentMap 𝓘(ℝ, Ambient n) (𝓡 n) normalize (pairLift z)

theorem normalize_smoothOn (n : ℕ) :
    ContMDiffOn 𝓘(ℝ, Ambient n) (𝓡 n) ∞ normalize
      (nonzeroAmbient n : Set (Ambient n)) :=
  fun _ hq => (normalize_smoothAt hq).contMDiffWithinAt

theorem normalize_tangentMap_smoothOn (n : ℕ) :
    ContMDiffOn (𝓘(ℝ, Ambient n)).tangent (𝓡 n).tangent ∞
      (tangentMap 𝓘(ℝ, Ambient n) (𝓡 n) normalize)
      ((fun p : TangentBundle 𝓘(ℝ, Ambient n) (Ambient n) => p.proj) ⁻¹'
        (nonzeroAmbient n : Set (Ambient n))) := by
  have hu : UniqueMDiffOn 𝓘(ℝ, Ambient n) (nonzeroAmbient n : Set (Ambient n)) :=
    (nonzeroAmbient n).isOpen.uniqueMDiffOn
  have h := (normalize_smoothOn n).contMDiffOn_tangentMapWithin (m := ∞) (by simp) hu
  apply h.congr
  intro p hp
  exact (tangentMapWithin_eq_tangentMap (hu p.proj hp)
    ((normalize_smoothAt hp).mdifferentiableAt (by simp))).symm

theorem lift_smoothAt {z : Ambient n × Ambient n} (hz : z.1 ≠ 0) :
    ContMDiffAt 𝓘(ℝ, Ambient n × Ambient n) (𝓡 n).tangent ∞ lift z := by
  have ho : IsOpen ((fun p : TangentBundle 𝓘(ℝ, Ambient n) (Ambient n) => p.proj) ⁻¹'
      (nonzeroAmbient n : Set (Ambient n)) :
      Set (TangentBundle 𝓘(ℝ, Ambient n) (Ambient n))) :=
    (nonzeroAmbient n).isOpen.preimage
      (FiberBundle.continuous_proj (Ambient n) (TangentSpace 𝓘(ℝ, Ambient n)))
  have ht := (normalize_tangentMap_smoothOn n (pairLift z) hz).contMDiffAt
    (ho.mem_nhds hz)
  exact ht.comp z (pairLift_smooth n).contMDiffAt

def ambientPair (p : Total n) : Ambient n × Ambient n :=
  ((p.proj : Ambient n), ambientVector n p)

theorem pairLift_ambientPair (p : Total n) :
    pairLift (ambientPair p) = tangentMap (𝓡 n) 𝓘(ℝ, Ambient n) (inclusion n) p := rfl

theorem lift_ambientPair (p : Total n) : lift (ambientPair p) = p := by
  have hg := (normalize_smoothAt (ne_zero_of_mem_unit_sphere p.proj)).mdifferentiableAt
    (by simp)
  have hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, Ambient n) (inclusion n) p.proj :=
    (inclusion_smooth n).mdifferentiableAt (by simp)
  have he := tangentMap_comp_at p hg hf
  change tangentMap (𝓡 n) (𝓡 n) (normalize ∘ inclusion n) p =
    tangentMap 𝓘(ℝ, Ambient n) (𝓡 n) normalize
      (tangentMap (𝓡 n) 𝓘(ℝ, Ambient n) (inclusion n) p) at he
  rw [normalize_comp_inclusion, tangentMap_id] at he
  simpa only [lift, pairLift_ambientPair, id_eq] using he.symm

end

end Finsler.SphereRetraction
