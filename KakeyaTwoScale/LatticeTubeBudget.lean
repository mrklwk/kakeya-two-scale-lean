module
public import KakeyaTwoScale.ColoredAtlasBudget

@[expose] public section

open MvPolynomial Set MeasureTheory Metric
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- Closed radius-r neighborhood of a doubly infinite line, in actual
Euclidean distance. There is no length cutoff or directional separation. -/
def infiniteLineTube {N : ℕ} (b u : Fin N → ℝ) (r : ℝ) : Set (Fin N → ℝ) :=
  {x | ∃t : ℝ, ‖(WithLp.toLp 2 (x-(b+t • u)) : EuclideanSpace ℝ (Fin N))‖≤r}

/-- Every point of a cube meeting a tube projects into one enlarged transverse
box. The enlargement is dimension-only and independent of the tube's location. -/
theorem incident_cube_projection {n : ℕ}
    (R : EuclideanSpace ℝ (Fin (n+1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n+1)))
    (b z : Fin (n+1) → ℝ) (r : ℝ) (hr : 0≤r)
    (hi : (visibilityCube z ∩ infiniteLineTube b
      (orthogonalCoordinates R (Pi.single 0 1)) r).Nonempty)
    (y : Fin (n+1) → ℝ) (hy : y∈visibilityCube z) :
    transverseProjection n ((orthogonalCoordinates R).symm y) ∈
      closedBall (transverseProjection n ((orthogonalCoordinates R).symm b))
        (r+((n+1:ℕ):ℝ)) := by
  obtain ⟨x,hx,t,ht⟩ := hi
  have hdist : ‖(WithLp.toLp 2 (y-x) : EuclideanSpace ℝ (Fin (n+1)))‖≤((n+1:ℕ):ℝ) := by
    have he : (WithLp.toLp 2 (y-x) : EuclideanSpace ℝ (Fin (n+1)))=
        WithLp.toLp 2 (y-z)-WithLp.toLp 2 (x-z) := by ext i; simp
    rw [he]
    have hh := norm_sub_le (WithLp.toLp 2 (y-z) : EuclideanSpace ℝ (Fin (n+1))) (WithLp.toLp 2 (x-z))
    linarith [visibilityCube_euclidean_radius z y hy,visibilityCube_euclidean_radius z x hx]
  have hd : ‖(WithLp.toLp 2 (y-(b+t • orthogonalCoordinates R (Pi.single 0 1))) :
      EuclideanSpace ℝ (Fin (n+1)))‖≤r+((n+1:ℕ):ℝ) := by
    have he : (WithLp.toLp 2 (y-(b+t • orthogonalCoordinates R (Pi.single 0 1))) :
        EuclideanSpace ℝ (Fin (n+1))) = WithLp.toLp 2 (y-x)+
        WithLp.toLp 2 (x-(b+t • orthogonalCoordinates R (Pi.single 0 1))) := by ext i; simp
    rw [he]
    exact (norm_add_le _ _).trans (by linarith)
  have hh := translated_orthogonal_projection _ (by positivity) R
    (b+t • orthogonalCoordinates R (Pi.single 0 1)) y hd
  have hc : transverseProjection n ((orthogonalCoordinates R).symm
      (b+t • orthogonalCoordinates R (Pi.single 0 1))) =
      transverseProjection n ((orthogonalCoordinates R).symm b) := by
    ext j
    simp [map_add,map_smul,ContinuousLinearEquiv.symm_apply_apply,transverseProjection]
  rwa [hc] at hh

/-- The raw finite tube budget for the actual polynomial atlas. Each closed
lattice boundary is paid by the 2^(n+1) coloring; the same original degree is
charged once per color. -/
theorem polynomial_lattice_tube_budget {ι : Type*} [Fintype ι] {n : ℕ}
    (P : MvPolynomial (Fin (n+1)) ℝ) (hP : P≠0)
    (A : DisjointChartAtlas n {x | eval x P=0})
    (z : ι → Fin (n+1) → ℤ) (hz : Function.Injective z)
    (b : Fin (n+1) → ℝ) (u : EuclideanSpace ℝ (Fin (n+1))) (hu : ‖u‖=1)
    (r : ℝ) (hr : 0≤r)
    (hi : ∀i, (visibilityCube (fun j => (z i j:ℝ)) ∩ infiniteLineTube b (WithLp.ofLp u) r).Nonempty) :
    (∑i, (A.restrict (visibilityCube (fun j => (z i j:ℝ))) measurableSet_closedBall).directionalArea
      (WithLp.ofLp u)) ≤
      (2:ℝ≥0∞)^(n+1)*((P.totalDegree : ℝ≥0∞)*
        volume (closedBall (0 : Fin n → ℝ) (r+((n+1:ℕ):ℝ)))) := by
  obtain ⟨R,hR⟩ := exists_axis_isometry (0 : Fin (n+1)) u hu
  have he : orthogonalCoordinates R (Pi.single 0 1)=WithLp.ofLp u := by
    rw [orthogonalCoordinates_first_axis,hR]
  have hh := polynomial_lattice_projection_budget P hP A z hz R
    (closedBall (transverseProjection n ((orthogonalCoordinates R).symm b)) (r+((n+1:ℕ):ℝ)))
    measurableSet_closedBall (fun i y hy => incident_cube_projection R b _ r hr (by simpa [he] using hi i) y hy)
  rw [he] at hh
  simpa only [Real.volume_pi_closedBall _ (show 0≤r+((n+1:ℕ):ℝ) by positivity)] using hh

end KakeyaTwoScale
#print axioms KakeyaTwoScale.incident_cube_projection
#print axioms KakeyaTwoScale.polynomial_lattice_tube_budget
