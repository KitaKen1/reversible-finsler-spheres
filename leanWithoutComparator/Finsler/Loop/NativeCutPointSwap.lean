module

public import Finsler.Loop.LocalNativeWrappedBallPrimitive
public import Finsler.Loop.NativeExplicitGraphRestriction

/-! Exchange the TWO sphere points before the actual complementary
cut. The resulting original self-evaluation is EXACTLY the existing
forward self-evaluation. Thus the ORIGINAL normalized Thom COCHAIN
pullbacks agree literally, without a new Thom-symmetry primitive.
All actual cut maps, radii and supports are retained. -/
@[expose] public section
namespace Finsler.NativeCutPointSwap
open CategoryTheory SphereOddDegree Finsler.SphereGeometry Finsler.MeridianLoopFamily
open Finsler.CochainComparison Finsler.SupportedCapNaturality
open Finsler.NativePairRelativeSphereTransport Finsler.NativeMeridianPairCoordinates
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1100000

def graphSwap {n : ℕ} (P : Sphere n) : graphSpace P ⟶ graphSpace P :=
  TopCat.ofHom ⟨fun z => (z.2.1, (z.1, z.2.2)), continuous_snd.fst.prodMk (continuous_fst.prodMk continuous_snd.snd)⟩
def ballSwap {n : ℕ} (P : Sphere n) (v₀ : equator P) : LocalNativeBallCut.space P v₀ ⟶ LocalNativeBallCut.space P v₀ :=
  TopCat.ofHom ⟨fun z => (z.2.1, (z.1, z.2.2)), continuous_snd.fst.prodMk (continuous_fst.prodMk continuous_snd.snd)⟩
def nativeSwap {n : ℕ} (P : Sphere n) : parameters P ⟶ parameters P :=
  TopCat.ofHom ⟨fun z => (z.2.1, (z.1, z.2.2)), continuous_snd.fst.prodMk (continuous_fst.prodMk continuous_snd.snd)⟩

theorem graph_involution {n : ℕ} (P : Sphere n) : graphSwap P ≫ graphSwap P = 𝟙 (graphSpace P) := rfl
theorem ball_involution {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    ballSwap P v₀ ≫ ballSwap P v₀ = 𝟙 (LocalNativeBallCut.space P v₀) := rfl
theorem native_involution {n : ℕ} (P : Sphere n) : nativeSwap P ≫ nativeSwap P = 𝟙 (parameters P) := rfl

theorem graph_good {n : ℕ} (P : Sphere n) (v₀ : equator P) (z : graphSpace P) :
    graphSwap P z ∈ NativeQuarterGraphPatch.graphGood P v₀ ↔ z ∈ NativeQuarterGraphPatch.graphGood P v₀ := and_comm
theorem ball_good {n : ℕ} (P : Sphere n) (v₀ : equator P) (z : LocalNativeBallCut.space P v₀) :
    ballSwap P v₀ z ∈ NativeBallSupportPatch.localGood P v₀ ↔ z ∈ NativeBallSupportPatch.localGood P v₀ := and_comm
theorem native_good {n : ℕ} (P : Sphere n) (v₀ : equator P) (z : parameters P) :
    nativeSwap P z ∈ NativeQuarterSupport.good P v₀ ↔ z ∈ NativeQuarterSupport.good P v₀ := and_comm

def graphPairSwap {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    NativeQuarterGraphDescent.graphSupportPair P v₀ ⟶ NativeQuarterGraphDescent.graphSupportPair P v₀ :=
  TopPair.ofSubsetMap (B := (NativeQuarterGraphPatch.graphGood P v₀)ᶜ) (B' := (NativeQuarterGraphPatch.graphGood P v₀)ᶜ)
    (graphSwap P) (fun z hz hg => hz ((graph_good P v₀ z).mp hg))
def ballPairSwap {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    NativeBallSupportPatch.localPair P v₀ ⟶ NativeBallSupportPatch.localPair P v₀ :=
  TopPair.ofSubsetMap (B := (NativeBallSupportPatch.localGood P v₀)ᶜ) (B' := (NativeBallSupportPatch.localGood P v₀)ᶜ)
    (ballSwap P v₀) (fun z hz hg => hz ((ball_good P v₀ z).mp hg))

theorem ball_graph_square {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    ballSwap P v₀ ≫ LocalNativeBallCut.toGraph P v₀ = LocalNativeBallCut.toGraph P v₀ ≫ graphSwap P := rfl

theorem ball_native_square {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    ballSwap P v₀ ≫ LocalNativeBallCut.toNative P v₀ = LocalNativeBallCut.toNative P v₀ ≫ nativeSwap P := rfl

def straightenedCut {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) :
    LocalNativeBallCut.space P v₀ ⟶ SelfCutThomCocycle.parameters n := ballSwap P v₀ ≫ LocalNativeWrappedBallCut.cutParameters P v₀ b

theorem straightened_self_evaluation {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) :
    straightenedCut P v₀ b ≫ SelfCutThomCocycle.selfEvaluation n =
      LocalNativeBallCut.cutParameters P v₀ b ≫ SelfCutThomCocycle.selfEvaluation n := by
  apply TopCat.ext
  intro z
  exact (LocalNativeWrappedBallCut.self_evaluation P v₀ b (ballSwap P v₀ z)).trans
    (LocalNativeBallCut.self_evaluation P v₀ b z).symm

theorem straightened_cocycle (n : ℕ) (hn : 1 ≤ n) (P : Sphere n) (v₀ : equator P) (b : Fin 3) {ρ : ℝ} (hρ : 0 < ρ) :
    cochainPullback (straightenedCut P v₀ b) n (NormalizedSelfCut.cocycle n hn hρ) =
      LocalNativeSupportedCap.cocycle n hn P v₀ b hρ := by
  unfold LocalNativeSupportedCap.cocycle NormalizedSelfCut.cocycle
  rw [← pullback_comp, ← pullback_comp, straightened_self_evaluation]

set_option backward.isDefEq.respectTransparency true in
set_option backward.defeqAttrib.useBackward false in
theorem distance_of_selfEvaluation (n : ℕ) (z w : SelfCutThomCocycle.parameters n)
    (h : SelfCutThomCocycle.selfEvaluation n z = SelfCutThomCocycle.selfEvaluation n w) :
    SupportedSelfCut.distance n z = SupportedSelfCut.distance n w := by
  have hl := congrArg Prod.fst h
  have hr := congrArg Prod.snd h
  change H1FiberBase.point z.2 = H1FiberBase.point w.2 at hl
  change H1SelfCutNeighborhood.endpoint z = H1SelfCutNeighborhood.endpoint w at hr
  change ‖(H1SelfCutNeighborhood.endpoint z : Ambient n) - (H1FiberBase.point z.2 : Ambient n)‖ =
    ‖(H1SelfCutNeighborhood.endpoint w : Ambient n) - (H1FiberBase.point w.2 : Ambient n)‖
  rw [hl, hr]

theorem straightened_distance {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) (z : LocalNativeBallCut.space P v₀) :
    SupportedSelfCut.distance n (straightenedCut P v₀ b z) =
      SupportedSelfCut.distance n (LocalNativeBallCut.cutParameters P v₀ b z) := by
  have he := ConcreteCategory.congr_hom (straightened_self_evaluation P v₀ b) z
  exact distance_of_selfEvaluation n (straightenedCut P v₀ b z) (LocalNativeBallCut.cutParameters P v₀ b z) he

end
end Finsler.NativeCutPointSwap
