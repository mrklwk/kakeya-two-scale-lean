module
public import KakeyaTwoScale.BroadTupleContribution
public import KakeyaTwoScale.ExtensionPlane
public import Mathlib.LinearAlgebra.Dimension.RankNullity

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical

/-- Distance to a larger linear subspace cannot increase. -/
theorem normalProjection_norm_antitone {n : ℕ}
    (H L : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hHL : H ≤ L)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖normalProjection L x‖ ≤ ‖normalProjection H x‖ := by
  have he : normalProjection L (normalProjection H x)=normalProjection L x := by
    have hn : normalProjection H x=x-H.starProjection x :=
      by rw [normalProjection,Submodule.starProjection_orthogonal_val]
    rw [hn]
    rw [map_sub,normalProjection_zero L (hHL (H.starProjection_apply_mem x)),sub_zero]
  have hh := Lᗮ.norm_starProjection_apply_le (normalProjection H x)
  change ‖normalProjection L (normalProjection H x)‖ ≤ _ at hh
  rwa [he] at hh

/-- Every smaller subspace extends to the exact dimension tested by
broadness. This constructs the extension rather than assuming one. -/
theorem subspace_extend_finrank {n : ℕ}
    (H : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (d : ℕ)
    (hH : Module.finrank ℝ H ≤ d) (hd : d ≤ n) :
    ∃ L : Submodule ℝ (EuclideanSpace ℝ (Fin n)), H ≤ L ∧ Module.finrank ℝ L=d := by
  induction d generalizing H with
  | zero => exact ⟨H,le_rfl,Nat.eq_zero_of_le_zero hH⟩
  | succ d ih =>
    by_cases hh : Module.finrank ℝ H ≤ d
    · obtain ⟨L,hHL,hL⟩ := ih H hh (by omega)
      have hrank : Module.finrank ℝ L < Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
        rw [hL]; simp only [finrank_euclideanSpace, Fintype.card_fin]; omega
      obtain ⟨x,hx⟩ := L.exists_of_finrank_lt hrank
      have hxout : x ∉ L := by simpa using hx 1 one_ne_zero
      have hnorm : 0 < ‖normalProjection L x‖ := by
        apply norm_pos_iff.mpr
        intro he
        have he' : x=L.starProjection x := by
          simpa only [normalProjection,Submodule.starProjection_orthogonal_val,sub_eq_zero] using he
        exact hxout (he' ▸ L.starProjection_apply_mem x)
      refine ⟨extensionSubspace L (normalDirection L x),hHL.trans le_sup_left,?_⟩
      rw [extensionSubspace_finrank L _ (normalDirection_mem L x) (normalDirection_unit L hnorm),hL]
    · exact ⟨H,le_rfl,by omega⟩

/-- Actual broad choices avoid the span of any shorter tuple. No linear
independence assumption is needed to extend its span for this argument. -/
theorem broad_prefix_choices {n N k m : ℕ} (G : Finset (Fin N))
    (u : Fin N → EuclideanSpace ℝ (Fin n)) (rho : ℝ)
    (hu : ∀ j∈G, ‖u j‖=1) (hm : m < k) (hkn : k ≤ n)
    (hbroad : ∀ H : Submodule ℝ (EuclideanSpace ℝ (Fin n)),
      Module.finrank ℝ H=k-1 →
      ((G.filter fun j => planeAngle H (u j)≤rho).card:ℝ)<(G.card:ℝ)/2)
    (f : Fin m → Fin N) :
    ∃ outside : Finset (Fin N), outside⊆G ∧ (G.card:ℝ)/2 < (outside.card:ℝ) ∧
      ∀ j∈outside, (2/Real.pi)*rho <
        ‖normalProjection (Submodule.span ℝ (Set.range (fun i => u (f i)))) (u j)‖ := by
  let H := Submodule.span ℝ (Set.range (fun i => u (f i)))
  have hdim : Module.finrank ℝ H ≤ m := by
    simpa [H,Set.finrank] using (finrank_range_le_card (R:=ℝ) (fun i => u (f i)))
  obtain ⟨L,hHL,hL⟩ := subspace_extend_finrank H (k-1) (by omega) (by omega)
  obtain ⟨O,hOG,hO,hprops⟩ := broad_plane_extension_choices G u L rho hu (hbroad L hL)
  exact ⟨O,hOG,hO,fun j hj => ((hprops j hj).2).trans_le (normalProjection_norm_antitone H L hHL (u j))⟩

end KakeyaTwoScale
#print axioms KakeyaTwoScale.normalProjection_norm_antitone
#print axioms KakeyaTwoScale.subspace_extend_finrank
#print axioms KakeyaTwoScale.broad_prefix_choices
