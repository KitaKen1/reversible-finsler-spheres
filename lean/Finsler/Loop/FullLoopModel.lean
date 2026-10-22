module

public import Finsler.Topology.SphereTopClass
public import Finsler.Topology.SupportedCapNaturality

/-! Remove the actual univ subtype in BorelLoop.fullPair.fst.
This is a genuine topological isomorphism and its constant-subspace
square, rather than an identification of different source models. -/

@[expose] public section
namespace Finsler.FullLoopModel
open CategoryTheory SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.BorelLoop
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

def forget (n : ℕ) : (fullPair n).fst ⟶ Loops n :=
  SupportedCap.subspaceMap (Loops n) Set.univ

def insert (n : ℕ) : Loops n ⟶ (fullPair n).fst :=
  TopCat.ofHom ⟨fun u => ⟨u, Set.mem_univ u⟩, continuous_id.subtype_mk _⟩

theorem forget_include (n : ℕ) : forget n ≫ insert n = 𝟙 (fullPair n).fst := by
  ext u : 1
  rfl

theorem include_forget (n : ℕ) : insert n ≫ forget n = 𝟙 (Loops n) := by
  ext u : 1
  rfl

def iso (n : ℕ) : (fullPair n).fst ≅ Loops n :=
  ⟨forget n, insert n, forget_include n, include_forget n⟩

def cohomologyEquiv (n k : ℕ) :
    cohomologyZMod2 (Loops n) k ≃ₗ[ZMod 2] cohomologyZMod2 (fullPair n).fst k :=
  ((singularCohomologyZMod2 k).mapIso (iso n).op).toLinearEquiv

theorem cohomology_apply (n k : ℕ) (a : cohomologyZMod2 (Loops n) k) :
    cohomologyEquiv n k a = (cohPullback (forget n) k).hom a := rfl

theorem constant_square (n : ℕ) : (fullPair n).map ≫ forget n =
    SupportedCap.subspaceMap (Loops n) (consts n) := by
  ext u : 1
  rfl

end
end Finsler.FullLoopModel
