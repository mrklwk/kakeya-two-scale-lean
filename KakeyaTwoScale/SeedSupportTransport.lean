module
public import KakeyaTwoScale.CellularPhysicalFamily
public import KakeyaTwoScale.FrozenStateBalance
public import KakeyaTwoScale.WholeCubeTupleSelection

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
attribute [local instance] Classical.propDecidable

theorem tupleCubeMass_eq_of_support {T C : Type*} [DecidableEq C]
    (Y : Finset T) (cube : T → C) (A B : Finset C) (hAB : A ⊆ B)
    (hY : ∀ y ∈ Y, cube y ∈ A) {p : ℝ} (hp : 0 < p) :
    tupleCubeMass Y cube A p=tupleCubeMass Y cube B p := by
  classical
  have hf : Y.filter (fun y => cube y ∈ A)=Y := Finset.filter_eq_self.mpr hY
  have ha := whole_cube_selection_mass Y cube A A (Finset.Subset.refl _) hp
  have hb := whole_cube_selection_mass Y cube B A hAB hp
  rw [hf] at ha hb
  exact ha.trans hb.symm

namespace FrozenGeometryState

theorem balanced_of_cube_support {n k : ℕ} {T C O : Type}
    [DecidableEq T] [DecidableEq C]
    (V : FrozenGeometryState n k T C O) (cube : T → C) (A B : Finset C)
    (hAB : A ⊆ B) (hY : ∀ y ∈ V.tuples, cube y ∈ A) {p : ℝ} (hp : 0 < p)
    (hb : V.Balanced cube A p) : V.Balanced cube B p := by
  classical
  have hm := tupleCubeMass_eq_of_support V.tuples cube A B hAB hY hp
  intro g hg
  have hmg := tupleCubeMass_eq_of_support (V.tuples.filter fun y => V.grain (cube y)=g)
    cube A B hAB (fun y hy => hY y (Finset.mem_filter.mp hy).1) hp
  simpa only [hm,hmg] using hb g hg

end FrozenGeometryState
namespace CellularPhysicalFamily

theorem valid_mono {n k : ℕ} {T C O G : Type}
    (W : CellularPhysicalFamily n k T O G) (Y Z : Finset T) (cube : T → C)
    (tube : T → Fin k → O) (Q : C → Set (EuclideanSpace ℝ (Fin n)))
    (grain : C → G) (δ maxLength : ℝ) (hZY : Z ⊆ Y)
    (hv : W.Valid Y cube tube Q grain δ maxLength) :
    W.Valid Z cube tube Q grain δ maxLength := by
  classical
  refine ⟨hv.1,hv.2.1,fun y hy => hv.2.2.1 y (hZY hy),
    fun y hy => hv.2.2.2.1 y (hZY hy),fun y hy => hv.2.2.2.2.1 y (hZY hy),?_⟩
  intro j o t ht u hu htu
  exact hv.2.2.2.2.2 j o
    ⟨Finset.image_subset_image hZY ht.1,ht.2⟩
    ⟨Finset.image_subset_image hZY hu.1,hu.2⟩ htu

end CellularPhysicalFamily
end KakeyaTwoScale
#print axioms KakeyaTwoScale.tupleCubeMass_eq_of_support
#print axioms KakeyaTwoScale.FrozenGeometryState.balanced_of_cube_support
#print axioms KakeyaTwoScale.CellularPhysicalFamily.valid_mono
