module
public import KakeyaTwoScale.GridCubeGeometry

@[expose] public section

open Set Metric
noncomputable section
namespace KakeyaTwoScale

/-- Plane labels, one endpoint bit per coordinate, and a point in both trapped
component interiors recover the original cube. Thus no terminal component can
receive more than 2^d cube charges on one fixed grid plane. -/
theorem terminal_grid_cube_recover {d : ℕ} (a theta : Fin d→ℝ) (h : ℝ) (hh : 0<h)
    (k l : Fin d→ℤ) (sigma tau : Fin d→Option Bool)
    (hJ : gridFaceFixed sigma=gridFaceFixed tau)
    (hlabels : ∀ j∈gridFaceFixed sigma, gridFaceLabels k sigma j=gridFaceLabels l tau j)
    (hbits : (fun j => decide (sigma j=some true))=(fun j => decide (tau j=some true)))
    (x : EuclideanSpace ℝ (Fin d))
    (hx : x∈openFreeBox (fun j x => x j) (gridFaceFixed sigma)
      (gridLevel a theta h k) (fun j => gridLevel a theta h k j+h))
    (hy : x∈openFreeBox (fun j x => x j) (gridFaceFixed tau)
      (gridLevel a theta h l) (fun j => gridLevel a theta h l j+h)) : k=l := by
  funext j
  by_cases hj : j∈gridFaceFixed sigma
  · have hl := hlabels j hj
    have hb := congrFun hbits j
    by_cases hs : sigma j=some true <;> by_cases ht : tau j=some true <;>
      simp only [hs,ht,decide_true,decide_false,Bool.true_eq_false,Bool.false_eq_true] at hb
    all_goals simp [gridFaceLabels,hs,ht] at hl
    all_goals omega
  · have hj' : j∉gridFaceFixed tau := by rwa [← hJ]
    exact open_grid_interval_index_unique (a j) (theta j) h hh (k j) (l j) (x j)
      (hx j hj) (hy j hj')

end KakeyaTwoScale
#print axioms KakeyaTwoScale.terminal_grid_cube_recover
