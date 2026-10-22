module

public import Finsler.Loop.MatchingOriginalRelativeOutputSplit

/-! Embed the ENTIRE original matching locus into the original
independent-time native pair parameters, with literal source/cut
alignment. Each actual whole-ball diagonal factors through this SAME
global matching family. Its retained output primitive therefore has
a common origin on all these genuine local diagonals. -/
@[expose] public section
namespace Finsler.NativeMatchingPairEmbedding
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.MeridianLoopFamily Finsler.CochainComparison Finsler.BorelLoop
open Finsler.SupportedCapNaturality Finsler.NativeBallDiagonalCohomology
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1700000

def pairEmbedding {n : ℕ} (P : Sphere n) :
    NativeMeridianMatchingLoci.parameters P ⟶ NativeMeridianPairCoordinates.parameters P :=
  TopCat.ofHom ⟨fun z => ((z.1, z.2.1), ((z.1, z.2.1), z.2.2)), by fun_prop⟩

theorem assembly_repeated {n : ℕ} (P : Sphere n) (b : Fin 3) (v w : equator P) :
    NativeMeridianPairCoordinates.assembly b v v w = NativeMeridianMatchingLoci.repeated b v w := by
  fin_cases b <;> rfl

theorem source_factor {n : ℕ} (P : Sphere n) (b : Fin 3) :
    pairEmbedding P ≫ NativeMeridianPairCoordinates.intoSource P b = NativeMeridianMatchingLoci.intoSource P b := by
  ext z : 1
  fin_cases b <;> rfl

theorem cut_factor {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) :
    pairEmbedding P ≫ NativeMeridianPairCoordinates.intoCut P v₀ b = NativeMeridianMatchingLoci.intoCut P v₀ b := by
  unfold NativeMeridianPairCoordinates.intoCut NativeMeridianMatchingLoci.intoCut
  rw [← Category.assoc, source_factor]

def fromLocalDiagonal {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    diagonal P v₀ ⟶ NativeMeridianMatchingLoci.parameters P :=
  TopCat.ofHom ⟨fun z => ((LocalNativeBallCut.toNative P v₀ z.val).1.1,
    ((LocalNativeBallCut.toNative P v₀ z.val).1.2, (LocalNativeBallCut.toNative P v₀ z.val).2.2)), by
    have hc : Continuous (fun z : diagonal P v₀ => LocalNativeBallCut.toNative P v₀ z.val) :=
      (LocalNativeBallCut.toNative P v₀).hom.continuous.comp continuous_subtype_val
    exact hc.fst.fst.prodMk (hc.fst.snd.prodMk hc.snd.snd)⟩

theorem local_first_eq_second {n : ℕ} (P : Sphere n) (v₀ : equator P) (z : diagonal P v₀) :
    (LocalNativeBallCut.toNative P v₀ z.val).1 = (LocalNativeBallCut.toNative P v₀ z.val).2.1 := by
  let y := LocalNativeBallCut.toGraphPatch P v₀ z.val
  have hx : y.val.1 = y.val.2.1 := congrArg Subtype.val z.property
  have hn : (⟨y.val.1, y.property.1⟩ : RationalNorthMeridianChart.north P) = ⟨y.val.2.1, y.property.2⟩ :=
    Subtype.ext hx
  change (MeridianNorthParameterChart.inverse P ⟨y.val.1, y.property.1⟩).val =
    (MeridianNorthParameterChart.inverse P ⟨y.val.2.1, y.property.2⟩).val
  exact congrArg (fun u => (MeridianNorthParameterChart.inverse P u).val) hn

theorem local_pair_factor {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    SupportedCap.subspaceMap (LocalNativeBallCut.space P v₀) (diagonalSet P v₀) ≫ LocalNativeBallCut.toNative P v₀ =
      fromLocalDiagonal P v₀ ≫ pairEmbedding P := by
  ext z : 1
  change LocalNativeBallCut.toNative P v₀ z.val =
    ((LocalNativeBallCut.toNative P v₀ z.val).1, ((LocalNativeBallCut.toNative P v₀ z.val).1,
      (LocalNativeBallCut.toNative P v₀ z.val).2.2))
  exact Prod.ext rfl (Prod.ext (local_first_eq_second P v₀ z).symm rfl)

theorem local_cut_factor {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) :
    SupportedCap.subspaceMap (LocalNativeBallCut.space P v₀) (diagonalSet P v₀) ≫ LocalNativeBallCut.cutParameters P v₀ b =
      fromLocalDiagonal P v₀ ≫ NativeMeridianMatchingLoci.intoCut P v₀ b := by
  unfold LocalNativeBallCut.cutParameters
  rw [← Category.assoc, local_pair_factor, Category.assoc, cut_factor]

theorem local_retained_factor {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) :
    SupportedCap.subspaceMap (LocalNativeBallCut.space P v₀) (diagonalSet P v₀) ≫ LocalNativeBallCut.retainedH1 P v₀ b =
      fromLocalDiagonal P v₀ ≫ MatchingRetainedOutputPrimitive.retainedH1 P v₀ b := by
  ext z : 1
  change H1SelfCutNeighborhood.right (LocalNativeBallCut.toTube P v₀ b z.val) =
    H1SelfCutNeighborhood.right (DiagonalSelfCutRepresentatives.intoTube
      (NativeMeridianMatchingLoci.intoDiagonal P v₀ b (fromLocalDiagonal P v₀ z)))
  apply congrArg H1SelfCutNeighborhood.right
  apply Subtype.ext
  exact ConcreteCategory.congr_hom (local_cut_factor P v₀ b) z

variable (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P)
  (B : singularCochainGroup (ZMod 2) (Loops (m + 1)) (m + 1))
  (hB : cochainCoboundary (ZMod 2) (Loops (m + 1)) (m + 1) B = 0)

def commonOutputPrimitive : singularCochainGroup (ZMod 2) (diagonal P v₀) m :=
  cochainPullback (fromLocalDiagonal P v₀) m (MatchingRetainedOutputPrimitive.primitive m P v₀ B hB)

theorem commonOutputPrimitive_d : cochainCoboundary (ZMod 2) (diagonal P v₀) m
    (commonOutputPrimitive m P v₀ B hB) =
    cochainPullback (SupportedCap.subspaceMap (LocalNativeBallCut.space P v₀) (diagonalSet P v₀)) (m + 1)
      (cochainPullback (LocalNativeBallCut.retainedH1 P v₀ 1) (m + 1) B) := by
  have he := SmallChainPrimitiveCorrection.pullback_boundary (fromLocalDiagonal P v₀) m (m + 1)
    (MatchingRetainedOutputPrimitive.primitive m P v₀ B hB)
  change cochainCoboundary (ZMod 2) (diagonal P v₀) m (commonOutputPrimitive m P v₀ B hB) =
    cochainPullback _ (m + 1) (cochainCoboundary (ZMod 2) _ m (MatchingRetainedOutputPrimitive.primitive m P v₀ B hB)) at he
  rw [MatchingRetainedOutputPrimitive.primitive_d, MatchingRetainedOutputPrimitive.cochain,
    ← pullback_comp, ← local_retained_factor, pullback_comp] at he
  exact he

end
end Finsler.NativeMatchingPairEmbedding
