module

public import Finsler.Topology.AmbientLensFinite
public import Finsler.Topology.PacketCutTimes

/-! Finite-dimensional ordinary lens groups for the actual global packet descent.
First split a finite crossing into any disjoint open family. Then use the actual cut-flow
comparison with regular wide loop cuts and the packet trapping estimate. -/

@[expose] public section

namespace Finsler.PacketFinite

open CategoryTheory Set Finsler.SphereGeometry Finsler.Geometry Finsler.Geodesics
open Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop Finsler.FlowLens
open Finsler.BorelComparison Finsler.PairTriple Finsler.LensFamily Finsler.LensContinuation
open Finsler.AmbientPenalty Finsler.CirclePacketFamily Finsler.PacketDeformation
open Finsler.LocalLabelPacket Finsler.PacketCutTimes Finsler.AmbientLensFinite Finsler.SampleK
open Finsler.CriticalLevels

noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 5
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Every local lens in a disjoint open trapping family is a quotient of the crossing. -/
theorem local_finite_of_cover {W : TopCat.{0}} {g : W → ℝ} (D : Descent W g)
    (hg : Continuous g) {a' a b T : ℝ} (hab : a ≤ b) (ha' : a' < a) (hT : 0 ≤ T)
    {J : Type*} (U : J → Set W) (hU : ∀ i, IsOpen (U i))
    (hdis : Pairwise fun i j => Disjoint (U i) (U j))
    (htrap : ∀ w, g w < b → a' ≤ g (D.flow T w) → ∃ j, w ∈ U j) (i : J) (q : ℕ)
    [Module.Finite (ZMod 2) (H (triv (pairOf (sub_mono g hab))) q)] :
    Module.Finite (ZMod 2) (H (triv (pairOf (partY_sub_partU g D (U i) a b T))) q) := by
  classical
  let V : Set W := ⋃ j : {j : J // j ≠ i}, U j.1
  have hV : IsOpen V := isOpen_iUnion fun j => hU j.1
  have hUV : Disjoint (U i) V := by
    apply Set.disjoint_left.mpr
    intro w hw hwV
    obtain ⟨j, hj⟩ := mem_iUnion.mp hwV
    exact Set.disjoint_left.mp (hdis j.2.symm) hw hj
  apply local_lens_finite D hg hab ha' hT (hU i) hV hUV
  intro w hw hw'
  obtain ⟨j, hj⟩ := htrap w hw hw'
  by_cases hji : j = i
  · exact Or.inl (hji ▸ hj)
  · exact Or.inr (mem_iUnion.mpr ⟨⟨j, hji⟩, hj⟩)

variable {n M : ℕ} [NeZero M] {ι : Type*} [Fintype ι]
variable {F : ReversibleMetric n} {c η a₀ b₀ : ℝ} {p : ι → Packet n (2 * M)}
variable {Γ : ι → Set (ZMod (2 * M) → Ambient n)}

theorem big_disjoint (han : ∀ i, Analytic F c η (Γ i) (p i))
    (hdis : ∀ i j, i ≠ j → Disjoint (p i).U (p j).U) :
    Pairwise fun i j => Disjoint (p i).big (p j).big := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro Q hQi hQj
  have hi := (han i).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 Q hQi
  have hj := (han j).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 Q hQj
  exact Set.disjoint_left.mp (tubes_disjoint han hdis i j hij) hi hj

/-- Regular wide loop cuts, actual cut-flow times and packet trapping imply finiteness of
every local packet lens for this actual global descent, at sufficiently tight cuts. -/
theorem exists_local_finite (han : ∀ i, Analytic F c η (Γ i) (p i))
    (hdis : ∀ i j, i ≠ j → Disjoint (p i).U (p j).U)
    (G : CirclePacketFamily.Global M F p a₀ b₀) (hn : 1 ≤ n)
    (hfin : (primeImages F).Finite) (hη : 0 ≤ η)
    {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u)
    (hlreg : l ∉ crit F) (hureg : u ∉ crit F)
    (ha₀ : a₀ ≤ l ^ 2 - η) (hb₀ : u ^ 2 + η ≤ b₀)
    (hTval : ∀ i y, y ∈ (p i).T →
      l ^ 2 + η < pen F (2 * M) 1 y ∧ pen F (2 * M) 1 y < u ^ 2 - η)
    (hs : ∀ q, Function.Bijective (nativePull (samplePair (F := F) (M := M) hl hlu) q)) :
    ∃ e : ℝ, 0 < e ∧ ∀ a' a b T : ℝ,
      l ^ 2 ≤ a' → a' < a → a < c ^ 2 → c ^ 2 < b → b ≤ u ^ 2 → b - a' < e → 1 ≤ T →
      ∀ i q, Module.Finite (ZMod 2) (H (triv (pairOf (partY_sub_partU
        (fun Q : Om n (2 * M) => deformed M F p Q.1)
        (PacketDeformation.Global.descent G) (p i).big a b T))) q) := by
  obtain ⟨e, he, htrap⟩ := PacketDeformation.Global.exists_trap han hdis G hn hη ha₀ hb₀
  refine ⟨e, he, fun a' a b T hla' ha' hac hcb hbu hw hT i q => ?_⟩
  have hla := hla'.trans ha'.le
  have hab := hac.le.trans hcb.le
  have hT0 : 0 ≤ T := zero_le_one.trans hT
  obtain ⟨τl, τu, hτl, hτu, hpushl, hpushu⟩ := exists_cut_times han hdis G hn hη
    ha₀ hb₀ hla hac hcb hbu
  obtain ⟨hsa, hsb⟩ := wide_sublevels han hdis hη hTval
  haveI : Module.Finite (ZMod 2) (H (triv (pairOf (sub_mono
      (fun Q : Om n (2 * M) => deformed M F p Q.1) hab))) q) :=
    crossing_finite M F (PacketDeformation.Global.descent G) hl hlu hla hab hbu hT0
    hsa hsb hτu hpushu (by norm_num) hτl hpushl hn hfin hlreg hureg hs q
  exact local_finite_of_cover (PacketDeformation.Global.descent G) (deformed_continuous han hn)
    hab ha' hT0 (fun i => (p i).big) (fun i => (han i).2.2.2.2.2.2.2.2.2.2.2.2.1)
    (big_disjoint han hdis) (htrap a' b T hla' hbu hw hT) i q

end

end Finsler.PacketFinite
