module

public import Finsler.Loop.MeridianCoverBoundary
public import Finsler.Loop.MeridianLoopClass

/-! The ORIGINAL evaluation sweep, rather than a replacement
suspension class, has actual Mayer–Vietoris boundary fixed_* - varying_*.
The three time triangles provide the explicit comparison boundary. -/
@[expose] public section
namespace Finsler.MeridianSweepConnecting
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.CochainComparison Finsler.SmallChainCarrier
open Finsler.SupportedCapNaturality Finsler.MeridianLoopFamily Finsler.MeridianQuarterHomotopies
open Finsler.MeridianIntersectionMaps Finsler.MeridianCoverPrisms Finsler.MeridianCoverBoundary
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

def includeSmall {n : ℕ} (P : Sphere n) : (sequence P).X₃ ⟶ chains (BorelEvaluation.sphere n) :=
  SmallChainCarrier.inclusion (BorelEvaluation.sphere n) ![upper P, lower P]

theorem upper_small_include {n : ℕ} (P : Sphere n) :
    SSet.chainComplexMap (TopCat.toSmallSingularSubcomplex ![upper P, lower P]
      (Matrix.cons_val_zero (upper P) ![lower P]).superset) coeff ≫ includeSmall P =
        push (SupportedCap.subspaceMap (BorelEvaluation.sphere n) (upper P)) := by
  have he : TopCat.ofHom (ContinuousMap.subtypeVal (upper P)) =
      SupportedCap.subspaceMap (BorelEvaluation.sphere n) (upper P) := by ext x : 1; rfl
  have h := congrArg (fun f => SSet.chainComplexMap f coeff)
      (TopCat.toSmallSingularSubcomplex_ι ![upper P, lower P]
        (Matrix.cons_val_zero (upper P) ![lower P]).superset)
  rw [he] at h
  simpa only [SSet.chainComplexMap, includeSmall, SmallChainCarrier.inclusion, push,
    ← Functor.map_comp] using h

theorem lower_small_include {n : ℕ} (P : Sphere n) :
    SSet.chainComplexMap (TopCat.toSmallSingularSubcomplex ![upper P, lower P]
      ((Matrix.cons_val_one (upper P) ![lower P]).trans
        (Matrix.cons_val_zero (lower P) ![])).superset) coeff ≫ includeSmall P =
        push (SupportedCap.subspaceMap (BorelEvaluation.sphere n) (lower P)) := by
  have he : TopCat.ofHom (ContinuousMap.subtypeVal (lower P)) =
      SupportedCap.subspaceMap (BorelEvaluation.sphere n) (lower P) := by ext x : 1; rfl
  have h := congrArg (fun f => SSet.chainComplexMap f coeff)
      (TopCat.toSmallSingularSubcomplex_ι ![upper P, lower P]
        ((Matrix.cons_val_one (upper P) ![lower P]).trans
          (Matrix.cons_val_zero (lower P) ![])).superset)
  rw [he] at h
  simpa only [SSet.chainComplexMap, includeSmall, SmallChainCarrier.inclusion, push,
    ← Functor.map_comp] using h

theorem cover_include {n : ℕ} (P : Sphere n) (v₀ : equator P) (q : ℕ) :
    coverChain P v₀ q ≫ (includeSmall P).f (q + 1) =
      (chains (parameters P)).iCycles q ≫
        (upperChain P v₀ q ≫ (push (SupportedCap.subspaceMap (BorelEvaluation.sphere n) (upper P))).f (q + 1)) +
      (chains (parameters P)).iCycles q ≫
        (lowerChain P v₀ q ≫ (push (SupportedCap.subspaceMap (BorelEvaluation.sphere n) (lower P))).f (q + 1)) := by
  change (liftChain P v₀ q ≫
    (biprod.desc
      (SSet.chainComplexMap (TopCat.toSmallSingularSubcomplex ![upper P, lower P]
        (Matrix.cons_val_zero (upper P) ![lower P]).superset) coeff)
      (SSet.chainComplexMap (TopCat.toSmallSingularSubcomplex ![upper P, lower P]
        ((Matrix.cons_val_one (upper P) ![lower P]).trans
          (Matrix.cons_val_zero (lower P) ![])).superset) coeff)).f (q + 1)) ≫ _ = _
  simp only [liftChain, Preadditive.add_comp, Category.assoc,
    HomologicalComplex.biprod_inl_desc_f_assoc, HomologicalComplex.biprod_inr_desc_f_assoc]
  rw [← HomologicalComplex.comp_f, upper_small_include,
    ← HomologicalComplex.comp_f, lower_small_include]

def sweepCycles {n : ℕ} (P : Sphere n) (v₀ : equator P) (q : ℕ) :=
  HomologicalComplex.cyclesMap (push (ordinary P v₀)) q ≫
    SelfHomotopySweep.cycles (ContinuousLoopSweep.chainHomotopy n) q

theorem sweep_i {n : ℕ} (P : Sphere n) (v₀ : equator P) (q : ℕ) :
    sweepCycles P v₀ q ≫ (chains (BorelEvaluation.sphere n)).iCycles (q + 1) =
      (chains (parameters P)).iCycles q ≫
        ((push (ordinary P v₀)).f q ≫ (ContinuousLoopSweep.chainHomotopy n).hom q (q + 1)) := by
  rw [sweepCycles, Category.assoc, SelfHomotopySweep.cycles_i, ← Category.assoc,
    HomologicalComplex.cyclesMap_i, Category.assoc]
  rfl

theorem sweep_cover_boundary {n : ℕ} (P : Sphere n) (v₀ : equator P) (q : ℕ) :
    sweepCycles P v₀ q - coverCycles P v₀ q ≫ HomologicalComplex.cyclesMap (includeSmall P) (q + 1) =
      ((chains (parameters P)).iCycles q ≫ UncappedTimeSplit.fourComparison
        (MeridianSweepQuarterMaps.fullMap P v₀) q) ≫
          (chains (BorelEvaluation.sphere n)).toCycles (q + 2) (q + 1) := by
  apply (cancel_mono ((chains (BorelEvaluation.sphere n)).iCycles (q + 1))).mp
  rw [Preadditive.sub_comp, sweep_i, Category.assoc, HomologicalComplex.cyclesMap_i]
  have hc : coverCycles P v₀ q ≫ (sequence P).X₃.iCycles (q + 1) = coverChain P v₀ q :=
    (sequence P).X₃.liftCycles_i _ _ _ _
  rw [reassoc_of% hc, Category.assoc, (chains (BorelEvaluation.sphere n)).toCycles_i]
  rw [cover_include, MeridianCoverPrisms.original_cover_split]
  abel

theorem sweep_cover_homology {n : ℕ} (P : Sphere n) (v₀ : equator P) (q : ℕ) :
    sweepCycles P v₀ q ≫ (chains (BorelEvaluation.sphere n)).homologyπ (q + 1) =
      coverCycles P v₀ q ≫ (sequence P).X₃.homologyπ (q + 1) ≫
        HomologicalComplex.homologyMap (includeSmall P) (q + 1) := by
  rw [HomologicalComplex.homologyπ_naturality, ← Category.assoc]
  apply sub_eq_zero.mp
  rw [← Preadditive.sub_comp, sweep_cover_boundary, Category.assoc,
    HomologicalComplex.toCycles_comp_homologyπ, comp_zero]

def connecting {n : ℕ} (P : Sphere n) (q : ℕ) :=
  TopCat.mayerVietorisδ coeff (open_upper P) (open_lower P) (cover P) (q + 1) q

theorem include_connecting {n : ℕ} (P : Sphere n) (q : ℕ) :
    HomologicalComplex.homologyMap (includeSmall P) (q + 1) ≫ connecting P q =
      (shortExact P).δ (q + 1) q (by rfl) := by
  have : Mono (intoUpper P) := (TopCat.mono_iff_injective _).mpr
    (Set.inclusion_injective Set.inter_subset_left)
  have : Mono (TopCat.toSSet.map (intoUpper P)) := Functor.map_mono _ _
  have h := TopCat.homologyMap_ι_comp_mayerVietorisδ coeff
    (open_upper P) (open_lower P) (cover P) (q + 1) q rfl
  exact h.trans (SSet.mayerVietorisδ_def
    (t := TopCat.toSSet.map (intoUpper P)) coeff (square P) (q + 1) q rfl)

theorem sweep_connecting {n : ℕ} (P : Sphere n) (v₀ : equator P) (q : ℕ) :
    HomologicalComplex.homologyMap (push (ordinary P v₀)) q ≫
      ContinuousLoopSweep.homology n q ≫ connecting P q =
        HomologicalComplex.homologyMap (push (fixed P v₀)) q -
          HomologicalComplex.homologyMap (push (varying P)) q := by
  have hs : (chains (parameters P)).homologyπ q ≫
      (HomologicalComplex.homologyMap (push (ordinary P v₀)) q ≫ ContinuousLoopSweep.homology n q) =
        sweepCycles P v₀ q ≫ (chains (BorelEvaluation.sphere n)).homologyπ (q + 1) := by
    rw [← Category.assoc, HomologicalComplex.homologyπ_naturality, Category.assoc]
    exact congrArg (fun f => HomologicalComplex.cyclesMap (push (ordinary P v₀)) q ≫ f)
      (SelfHomotopySweep.homologyπ_homology (ContinuousLoopSweep.chainHomotopy n) q)
  apply (cancel_epi ((chains (parameters P)).homologyπ q)).mp
  calc
    _ = ((chains (parameters P)).homologyπ q ≫
        (HomologicalComplex.homologyMap (push (ordinary P v₀)) q ≫ ContinuousLoopSweep.homology n q)) ≫
          connecting P q := by simp only [Category.assoc]
    _ = (sweepCycles P v₀ q ≫ _) ≫ connecting P q := congrArg (fun f => f ≫ connecting P q) hs
    _ = coverCycles P v₀ q ≫ (sequence P).X₃.homologyπ (q + 1) ≫
        (HomologicalComplex.homologyMap (includeSmall P) (q + 1) ≫ connecting P q) := by
          rw [sweep_cover_homology]; simp only [Category.assoc]
    _ = intersectionCycles P v₀ q ≫ (sequence P).X₁.homologyπ q := by
      rw [include_connecting]
      exact connecting_cycles P v₀ q
    _ = _ := by
      change intersectionCycles P v₀ q ≫ (chains (TopCat.of ↥(upper P ∩ lower P))).homologyπ q = _
      simp only [intersectionCycles, Preadditive.sub_comp,
        Preadditive.comp_sub, HomologicalComplex.homologyπ_naturality]

end
end Finsler.MeridianSweepConnecting
