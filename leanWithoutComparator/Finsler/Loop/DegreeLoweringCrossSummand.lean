module

public import Finsler.Topology.DegreeLoweringHomology
public import Finsler.Topology.FilteredBilinearLoopProduct

/-! A native homogeneous factorization of two genuine closed operations
already determines their value on homology cross products. Work directly
with the actual cyclesCross and its quotient universal property; no
shifted tensor-complex map or extra sign convention is introduced. -/

@[expose] public section
namespace Finsler.DegreeLoweringCrossSummand

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1400000

variable {R : Type} [CommRing R]
  (C K D L E : ChainComplex (ModuleCat.{0} R) ℕ) (d e : ℕ)
  (a : DegreeLoweringHomology.Map C D d) (b : K ⟶ L)
  (f : DegreeLoweringHomology.Map (HomologicalComplex.tensorObj C K) E (e + d))
  (g : DegreeLoweringHomology.Map (HomologicalComplex.tensorObj D L) E e)
  (i j k : ℕ) (hij : i + j = e + k)
  (hs : (a.component i ⊗ₘ b.f j) ≫ ιTensorObj D L i j (e + k) hij ≫ g.component k =
    ιTensorObj C K (d + i) j ((e + d) + k) (by omega) ≫ f.component k)

include hs in
theorem cycles :
    cyclesCross C K (d + i) j ((e + d) + k) (by omega) ≫ f.cycles k =
    (a.cycles i ⊗ₘ cyclesMap b j) ≫ cyclesCross D L i j (e + k) hij ≫ g.cycles k := by
  apply (cancel_mono (E.iCycles k)).mp
  simp only [Category.assoc, DegreeLoweringHomology.Map.cycles_i]
  rw [← Category.assoc (cyclesCross C K (d + i) j ((e + d) + k) (by omega)), cyclesCross_iCycles]
  rw [← Category.assoc (cyclesCross D L i j (e + k) hij), cyclesCross_iCycles]
  simp only [Category.assoc]
  rw [tensorHom_comp_tensorHom_assoc]
  rw [DegreeLoweringHomology.Map.cycles_i, cyclesMap_i]
  rw [← tensorHom_comp_tensorHom_assoc]
  rw [hs]

include hs in
theorem homology :
    homologyCross C K (d + i) j ((e + d) + k) (by omega) ≫ f.homology k =
    (a.homology i ⊗ₘ homologyMap b j) ≫ homologyCross D L i j (e + k) hij ≫ g.homology k := by
  apply homology_tensor_homology_hom_ext C K (d + i) j
  simp only [homologyπ_tensorHom_homologyCross_assoc,
    DegreeLoweringHomology.Map.homologyπ_homology]
  rw [tensorHom_comp_tensorHom_assoc,
    DegreeLoweringHomology.Map.homologyπ_homology, homologyπ_naturality,
    ← tensorHom_comp_tensorHom_assoc]
  simp only [Category.assoc, homologyπ_tensorHom_homologyCross_assoc,
    DegreeLoweringHomology.Map.homologyπ_homology]
  rw [← Category.assoc, cycles C K D L E d e a b f g i j k hij hs]
  simp only [Category.assoc]

end
end Finsler.DegreeLoweringCrossSummand
