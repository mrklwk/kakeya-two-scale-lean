module
public import KakeyaTwoScale.CompactSublevelNeighborhood
public import Mathlib.Data.Finset.Lattice.Fold

@[expose] public section

open Set Metric
noncomputable section
namespace KakeyaTwoScale

/-- One positive sublevel parameter preserves any finite collection of actual
components of a compact zero set. Neither component finiteness nor a bound on
components is assumed. -/
theorem compact_sublevel_finite_component_separation
    {X : Type*} [MetricSpace X] [ProperSpace X]
    (Q : X→ℝ) (hQ : Continuous Q) (hQ0 : ∀ x, 0≤Q x)
    (center : X) (R : ℝ) (hR : 0≤R)
    {I : Type*} [Fintype I] (x : I→X)
    (hx : ∀ j, x j ∈ {z | Q z=0} ∩ closedBall center R)
    (hd : ∀ j k, j≠k → x k ∉ connectedComponentIn
      ({z | Q z=0} ∩ closedBall center R) (x j)) :
    ∃ epsilon : ℝ, 0<epsilon ∧ ∀ C : Set X, IsPreconnected C →
      C⊆{z | Q z<epsilon ∧ dist z center^2<R^2+epsilon} →
      ∀ j k, x j∈C → x k∈C → j=k := by
  classical
  let K := {z | Q z=0} ∩ closedBall center R
  have hK : IsCompact K := (isCompact_closedBall center R).inter_left
    (isClosed_eq hQ continuous_const)
  let T := {p : I×I // p.1≠p.2}
  have hp (p : T) : ∃ e : ℝ, 0<e ∧ ∃ U V : Set X,
      IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧ x p.val.1∈U ∧ x p.val.2∈V ∧
      ∀ d : ℝ, 0<d → d≤e →
        {z | Q z<d ∧ dist z center^2<R^2+d}⊆U∪V := by
    obtain ⟨U,V,hU,hV,hUV,hKU,hxU,hxV⟩ :=
      compact_component_pair_separation K hK (x p.val.1) (x p.val.2)
        (hx _) (hx _) (hd _ _ p.property)
    obtain ⟨e,he,hes⟩ := compact_zero_sublevels_shrink Q hQ hQ0 center R hR
      (U∪V) (hU.union hV) hKU
    exact ⟨e,he,U,V,hU,hV,hUV,hxU,hxV,hes⟩
  choose e he U V hU hV hUV hxU hxV hes using hp
  let B : Finset ℝ := insert 1 (Finset.univ.image e)
  have hB : B.Nonempty := ⟨1,Finset.mem_insert_self _ _⟩
  let epsilon := B.inf' hB id
  have heps : 0<epsilon := by
    apply (Finset.lt_inf'_iff hB).mpr
    intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hb
    · norm_num
    · obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hb
      exact he p
  refine ⟨epsilon,heps,?_⟩
  intro C hC hCs j k hj hk
  by_contra hjk
  let p : T := ⟨(j,k),hjk⟩
  have hep : epsilon≤e p := Finset.inf'_le _
    (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨p,Finset.mem_univ _,rfl⟩))
  have hCUV : C⊆U p∪V p := hCs.trans (hes p epsilon heps hep)
  have hCU : C⊆U p := IsPreconnected.subset_left_of_subset_union
    (hU p) (hV p) (hUV p) hCUV ⟨x j,hj,hxU p⟩ hC
  exact Set.disjoint_left.mp (hUV p) (hCU hk) (hxV p)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.compact_sublevel_finite_component_separation
