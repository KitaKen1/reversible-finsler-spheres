module

public import Finsler.Topology.BorelComparison
public import Finsler.Topology.BorelLoop

/-! The filtered reflection Gysin system with its ordinary groups given by
Tau Ceti's actual relative singular cohomology of the Finsler loop pairs. -/

@[expose] public section

namespace Finsler.BorelLoopComparison

open CategoryTheory Finsler.BorelCochain Finsler.BorelPair
  Finsler.BorelLoop Finsler.BorelComparison

noncomputable section

variable {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n)

abbrev fullEquiv (n q : ℕ) : H (fullComplex n) q ≃ₗ[ZMod 2] native (fullPair n) q :=
  ordinaryEquiv (fullPair n) (revFullPair n) (revFullPair_sq n) q

abbrev levEquiv (a : ℝ) (q : ℕ) : H (levComplex F a) q ≃ₗ[ZMod 2] native (levPair F a) q :=
  ordinaryEquiv (levPair F a) (revPair F a) (revPair_sq F a) q

theorem res_natural (a : ℝ) (q : ℕ) (z : H (fullComplex n) q) :
    levEquiv F a q (Hmap (resHom F a) q z) =
      nativePull (resPair F a) q (fullEquiv n q z) :=
  ordinaryEquiv_natural (revPair_sq F a) (revFullPair_sq n)
    (resPair F a) (resPair_equivariant F a) q z

theorem cut_natural {a b : ℝ} (hab : a ≤ b) (q : ℕ) (z : H (levComplex F b) q) :
    levEquiv F a q (Hmap (cutHom F hab) q z) =
      nativePull (cutPair F hab) q (levEquiv F b q z) :=
  ordinaryEquiv_natural (revPair_sq F a) (revPair_sq F b)
    (cutPair F hab) (cutPair_equivariant F hab) q z

/-- All ordinary restriction and cut maps in this data are the actual singular
cohomology pullbacks; its equivariant groups retain the explicit Borel model. -/
def nativeGysinData :
    Finsler.FilteredGysin.Data (fun q => native (fullPair n) q)
      (fun q => HR (fullComplex n) q) (fun a q => native (levPair F a) q)
      (fun a q => HR (levComplex F a) q) where
  w q := (w (fullComplex n) q).toAddMonoidHom
  forget q := (forgetNative (fullPair n) (revFullPair n) (revFullPair_sq n) q).toAddMonoidHom
  transfer q := (transferNative (fullPair n) (revFullPair n) (revFullPair_sq n) q).toAddMonoidHom
  wB a q := (w (levComplex F a) q).toAddMonoidHom
  forgetB a q := (forgetNative (levPair F a) (revPair F a) (revPair_sq F a) q).toAddMonoidHom
  transferB a q := (transferNative (levPair F a) (revPair F a) (revPair_sq F a) q).toAddMonoidHom
  resA a q := (nativePull (resPair F a) q).toAddMonoidHom
  resB a q := (HRmap (resHom F a) q).toAddMonoidHom
  cutA a b hab q := (nativePull (cutPair F hab) q).toAddMonoidHom
  cutB a b hab q := (HRmap (cutHom F hab) q).toAddMonoidHom
  exact_forget q x := exact_forgetNative (fullPair n) (revFullPair n) (revFullPair_sq n) q x
  exact_w q y := exact_wNative (fullPair n) (revFullPair n) (revFullPair_sq n) q y
  exact_wB a q y := exact_wNative (levPair F a) (revPair F a) (revPair_sq F a) q y
  natural_forget a q x :=
    (forgetNative_natural (revPair_sq F a) (revFullPair_sq n)
      (resPair F a) (resPair_equivariant F a) q x).symm
  natural_w a q y := (HRmap_w (resHom F a) q y).symm
  natural_transfer a q z :=
    transferNative_natural (revPair_sq F a) (revFullPair_sq n)
      (resPair F a) (resPair_equivariant F a) q z
  natural_cutA a b hab q z := by
    have h := TopPair.singularCohomologyMap_comp
      (R := Finsler.RelativeCohomology.coeff) (k := ZMod 2)
      (M := Finsler.RelativeCohomology.coeff) (cutPair F hab) (resPair F b) q
    have hz := ConcreteCategory.congr_hom h z
    change nativePull (cutPair F hab ≫ resPair F b) q z =
      nativePull (cutPair F hab) q (nativePull (resPair F b) q z) at hz
    rw [cutPair_resPair] at hz
    exact hz.symm
  natural_cutB a b hab q y := (gysinData F).natural_cutB a b hab q y
  natural_cut_transfer a b hab q z :=
    transferNative_natural (revPair_sq F a) (revPair_sq F b)
      (cutPair F hab) (cutPair_equivariant F hab) q z

/-- No comparison or Gysin hypothesis is postulated: the actual loop pairs
supply this filtered system in every degree and at every real cut. -/
theorem exists_nativeGysinData :
    Nonempty (Finsler.FilteredGysin.Data (fun q => native (fullPair n) q)
      (fun q => HR (fullComplex n) q) (fun a q => native (levPair F a) q)
      (fun a q => HR (levComplex F a) q)) :=
  ⟨nativeGysinData F⟩

end
end Finsler.BorelLoopComparison
