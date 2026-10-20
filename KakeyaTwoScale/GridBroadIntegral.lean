module
public import KakeyaTwoScale.GridBroadPointwise
public import KakeyaTwoScale.BroadHolder

@[expose] public section

open MeasureTheory
noncomputable section
namespace KakeyaTwoScale
open Classical

/-- Empty cells cannot be broad when the tested subspace dimension exists.
Thus the literal broad predicate has finite-volume support. -/
theorem gridBroadRegion_subset_occupied {n N k : ℕ}
    (b v : Fin N → Fin n → ℝ) (u : Fin N → EuclideanSpace ℝ (Fin (n+1)))
    (d r : ℝ) (hk : k ≤ n+1) :
    gridBroadRegion b v u k d r ⊆
      occupiedGridRegion Finset.univ b v d (fun _ => Set.Icc (0:ℝ) 1) := by
  intro x hx
  by_contra hno
  have he : incidentPattern (fun j => gridPortion (b j) (v j) d (Set.Icc (0:ℝ) 1)) x=∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro j hj
    have hj' := (Finset.mem_filter.mp hj).2
    exact hno (Set.mem_iUnion₂.mpr ⟨j,Finset.mem_univ _,hj'⟩)
  obtain ⟨H,_,hH⟩ := subspace_extend_finrank (⊥ : Submodule ℝ (EuclideanSpace ℝ (Fin (n+1)))) k (by simp) hk
  apply hx
  refine ⟨H,hH,?_⟩
  rw [he]
  simp

/-- Integrated broad estimate on actual graph-grid cells and their original
variable-length capsules. The only analytic input is a genuine finite
multilinear norm bound; all geometric, measure and Holder steps are proved. -/
theorem grid_broad_integral_of_norm_bound {n N k : ℕ}
    (b v : Fin N → Fin n → ℝ) (i : Fin (n+1)) (d rho D B A : ℝ)
    (hd : 0 < d) (hrho : 0 < rho) (hD : 4*(n+2:ℝ)+1 ≤ D)
    (hB : 1 < B) (hA : 0 ≤ A) (hk : 1 ≤ k) (hkn : k ≤ n+1)
    (hnorm : eLpNorm (multilinearKakeyaFunction k (fun j => graphUnitDirection i (v j))
      (fun j => euclideanTube (euclideanUnsplit i (0,b j))
        (euclideanUnsplit i (1,v j)) (D*d)) B)
      (ENNReal.ofReal (B/(B-1))) volume ≤ ENNReal.ofReal A) :
    let S := gridBroadRegion b v (fun j => graphUnitDirection i (v j)) (k-1) d rho
    Integrable (gridMultiplicity Finset.univ b v d) (volume.restrict S) ∧
      (∫ x in S, gridMultiplicity Finset.univ b v d x) ≤
        A*(volume.real S)^(1/B)/(broadCoefficient (k-1) B*rho^(((k:ℝ)-1)/B)) := by
  dsimp only
  let S := gridBroadRegion b v (fun j => graphUnitDirection i (v j)) (k-1) d rho
  let M := multilinearKakeyaFunction k (fun j => graphUnitDirection i (v j))
    (fun j => euclideanTube (euclideanUnsplit i (0,b j))
      (euclideanUnsplit i (1,v j)) (D*d)) B
  have hm : Measurable M := measurable_multilinearKakeyaFunction k _ _ B
    (fun j => (isOpen_euclideanTube _ _ _).measurableSet)
  have hs : MeasurableSet S := measurableSet_gridBroadRegion _ _ _ _ _ _
  have hfin : volume S ≠ ⊤ := measure_ne_top_of_subset
    (gridBroadRegion_subset_occupied b v _ d rho (by omega : k-1≤n+1))
    (occupiedGridRegion_finite_volume Finset.univ b v hd _
      (fun _ _ => measurableSet_Icc) (fun _ _ => Set.Subset.rfl))
  apply broad_integral_of_norm_bound volume S hs hfin (gridMultiplicity Finset.univ b v d)
    (M ∘ euclideanUnsplit i) (measurable_gridMultiplicity _ _ _ _)
    (hm.comp (euclideanUnsplit_measurePreserving i).measurable)
    (broadCoefficient (k-1) B*rho^(((k:ℝ)-1)/B)) B A
    (mul_pos (broadCoefficient_pos _ _) (Real.rpow_pos_of_pos hrho _)) hB hA
  · intro x _; exact gridMultiplicity_nonneg _ _ _ _ _
  · intro x _
    exact multilinearKakeyaFunction_nonneg k (fun j => graphUnitDirection i (v j))
      (fun j => euclideanTube (euclideanUnsplit i (0,b j))
        (euclideanUnsplit i (1,v j)) (D*d)) B (euclideanUnsplit i x)
  · intro x hx
    exact grid_broad_multilinear_pointwise b v i d rho D B hd hrho hD (by linarith) hk hkn x hx
  · rw [eLpNorm_comp_measurePreserving hm.aestronglyMeasurable (euclideanUnsplit_measurePreserving i)]
    exact hnorm

end KakeyaTwoScale
#print axioms KakeyaTwoScale.gridBroadRegion_subset_occupied
#print axioms KakeyaTwoScale.grid_broad_integral_of_norm_bound
