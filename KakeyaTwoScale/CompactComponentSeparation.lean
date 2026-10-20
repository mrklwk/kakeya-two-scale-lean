module
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.Order.Compact

@[expose] public section

open Set
noncomputable section
namespace KakeyaTwoScale

/-- Distinct components of a compact Hausdorff set admit disjoint AMBIENT
open neighborhoods covering the entire compact set. No finiteness of its
connected components is assumed. -/
theorem compact_component_pair_separation {X : Type*} [TopologicalSpace X]
    [T2Space X] [NormalSpace X] (K : Set X) (hK : IsCompact K)
    (x y : X) (hx : x∈K) (hy : y∈K) (hne : y∉connectedComponentIn K x) :
    ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧
      K⊆U∪V ∧ x∈U ∧ y∈V := by
  classical
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hn : (⟨y,hy⟩ : K)∉connectedComponent (⟨x,hx⟩ : K) := by
    intro hh
    apply hne
    rw [connectedComponentIn_eq_image hx]
    exact ⟨⟨y,hy⟩,hh,rfl⟩
  rw [connectedComponent_eq_iInter_isClopen] at hn
  simp only [mem_iInter] at hn
  push Not at hn
  obtain ⟨A,hAy⟩ := hn
  let KA : Set X := Subtype.val '' (A.val : Set K)
  let KB : Set X := Subtype.val '' (A.val : Set K)ᶜ
  have hKA : IsClosed KA := (A.property.1.1.isCompact.image continuous_subtype_val).isClosed
  have hKB : IsClosed KB := (A.property.1.compl.1.isCompact.image continuous_subtype_val).isClosed
  have hdis : Disjoint KA KB := by
    apply Set.disjoint_left.mpr
    rintro z ⟨za,hza,rfl⟩ ⟨zb,hzb,he⟩
    have hab : zb=za := Subtype.ext he
    exact hzb (hab ▸ hza)
  obtain ⟨U,V,hU,hV,hAU,hBV,hUV⟩ := normal_separation hKA hKB hdis
  refine ⟨U,V,hU,hV,hUV,?_,hAU ⟨⟨x,hx⟩,A.property.2,rfl⟩,hBV ⟨⟨y,hy⟩,hAy,rfl⟩⟩
  intro z hz
  by_cases ha : (⟨z,hz⟩ : K)∈A.val
  · exact Or.inl (hAU ⟨⟨z,hz⟩,ha,rfl⟩)
  · exact Or.inr (hBV ⟨⟨z,hz⟩,ha,rfl⟩)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.compact_component_pair_separation
