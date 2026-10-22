module
public import Finsler.Topology.BorelTotalCup
/-! The finite twisted absolute-relative convolution is constructed inside the actual relative singular cochains by the actual relative cup and powers of relative pullback. Its componentwise ambient inclusion is the existing absolute convolution. Cochain-level ambient injection proves support preservation and the general two-input total Leibniz law, without closed or invariant component assumptions. The construction uses actual relative cochains and does not assume injectivity of relative cohomology into absolute cohomology. Relative quotient descent and the full general module laws remain separate. -/

@[expose] public section
namespace Finsler.BorelRelativeTotal
open CategoryTheory SphereOddDegree BorelCochain BorelTwistedCup BorelTwistedDifferential
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (P : TopPair.{0}) (r : P ⟶ P) (hr : r≫r=𝟙 P)

abbrev relativeComplex := BorelPair.ofPair P r hr
abbrev absoluteComplex := BorelAbsolute.ofSpace P.fst (TopPair.Hom.fst r) (BorelAbsolute.fst_sq P r hr)
abbrev ambientHom := BorelAbsoluteCup.toAbsolute P r hr

def act (i j : ℕ) : (relativeComplex P r hr).C j →ₗ[ZMod 2] (relativeComplex P r hr).C j :=
  ((relativeComplex P r hr).t j)^i

theorem ambient_act (i j : ℕ) (x : (relativeComplex P r hr).C j) :
    (ambientHom P r hr).f j (act P r hr i j x)=
      BorelTwistedCup.act (TopPair.Hom.fst r) i j ((ambientHom P r hr).f j x) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have he : act P r hr (i+1) j x=(relativeComplex P r hr).t j (act P r hr i j x) := by
      simp only [act,pow_succ',Module.End.mul_apply]
    rw [he,(ambientHom P r hr).comm_t,ih,act_succ_left]
    rfl

theorem ambient_cast {a b : ℕ} (h : a=b) (x : (relativeComplex P r hr).C a) :
    (ambientHom P r hr).f b (BorelGraded.castC (relativeComplex P r hr) h x)=
      BorelGraded.castC (absoluteComplex P r hr) h ((ambientHom P r hr).f a x) := by
  subst b
  rfl

def term (p k a : ℕ) (x : Seq (absoluteComplex P r hr)) (y : Seq (relativeComplex P r hr)) :
    (relativeComplex P r hr).C k :=
  if h : a≤k ∧ a≤p then
    BorelGraded.castC (relativeComplex P r hr) (by omega)
      (RelativeCupCochain.cup P a (k-a) (x a) (act P r hr (p-a) (k-a) (y (k-a))))
  else 0

/-- Relative twisted convolution is constructed inside actual relative cochains. -/
def convolution (p : ℕ) (x : Seq (absoluteComplex P r hr)) (y : Seq (relativeComplex P r hr)) :
    Seq (relativeComplex P r hr) := fun k => ∑ a ∈ Finset.range (k+1),term P r hr p k a x y

theorem ambient_term (p k a : ℕ) (x : Seq (absoluteComplex P r hr)) (y : Seq (relativeComplex P r hr)) :
    (ambientHom P r hr).f k (term P r hr p k a x y)=
      BorelTwistedCup.term (TopPair.Hom.fst r) p k a x (seqMap (ambientHom P r hr) y) := by
  unfold term BorelTwistedCup.term
  split_ifs with h
  · rw [ambient_cast,←cast_absolute (TopPair.Hom.fst r) (BorelAbsolute.fst_sq P r hr)]
    change cochainCast _ (RelativeCupCochain.toAmbient P (a+(k-a))
      (RelativeCupCochain.cup P a (k-a) (x a) (act P r hr (p-a) (k-a) (y (k-a)))))=_
    rw [RelativeCupCochain.toAmbient_cup]
    have he := ambient_act P r hr (p-a) (k-a) (y (k-a))
    change RelativeCupCochain.toAmbient P (k-a) (act P r hr (p-a) (k-a) (y (k-a)))=
      BorelTwistedCup.act (TopPair.Hom.fst r) (p-a) (k-a) (RelativeCupCochain.toAmbient P (k-a) (y (k-a))) at he
    rw [he]
    rfl
  · exact map_zero _

/-- The relative construction maps to the verified actual absolute convolution. -/
theorem ambient_convolution (p : ℕ) (x : Seq (absoluteComplex P r hr)) (y : Seq (relativeComplex P r hr)) :
    seqMap (ambientHom P r hr) (convolution P r hr p x y)=
      BorelTwistedDifferential.convolution (TopPair.Hom.fst r) (BorelAbsolute.fst_sq P r hr) p x
        (seqMap (ambientHom P r hr) y) := by
  funext k
  change (ambientHom P r hr).f k (∑ a ∈ Finset.range (k+1),term P r hr p k a x y)=_
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro a ha
  exact ambient_term P r hr p k a x y

theorem ambient_seq_injective : Function.Injective (seqMap (ambientHom P r hr)) := by
  intro x y he
  funext k
  apply RelativeCupCochain.toAmbient_injective P k
  exact congrFun he k

/-- Right relative support is preserved before taking cohomology. -/
theorem convolution_low (p q : ℕ) (x : Seq (absoluteComplex P r hr)) (y : Seq (relativeComplex P r hr))
    (hy : y ∈ low (relativeComplex P r hr) q) : convolution P r hr p x y ∈ low (relativeComplex P r hr) (p+q) := by
  have hb := BorelTotalCup.convolution_low (TopPair.Hom.fst r) (BorelAbsolute.fst_sq P r hr) p q x
    (seqMap (ambientHom P r hr) y) (seqMap_low (ambientHom P r hr) hy)
  rw [←ambient_convolution] at hb
  intro k hk
  apply RelativeCupCochain.toAmbient_injective P k
  change (ambientHom P r hr).f k (convolution P r hr p x y k)=(ambientHom P r hr).f k 0
  rw [map_zero]
  exact hb k hk

/-- General Leibniz is inherited using cochain injection and actual relative primitives. -/
theorem convolution_D (p : ℕ) (x : Seq (absoluteComplex P r hr)) (y : Seq (relativeComplex P r hr))
    (hx : x ∈ low (absoluteComplex P r hr) (p+1)) :
    D (relativeComplex P r hr) (convolution P r hr p x y)=
      convolution P r hr (p+1) (D (absoluteComplex P r hr) x) y+
        convolution P r hr p x (D (relativeComplex P r hr) y) := by
  apply ambient_seq_injective P r hr
  rw [map_add,seqMap_D,ambient_convolution,ambient_convolution,ambient_convolution,
    seqMap_D]
  exact BorelTwistedDifferential.convolution_D (TopPair.Hom.fst r) (BorelAbsolute.fst_sq P r hr) p x _ hx

end
end Finsler.BorelRelativeTotal
