module
public import KakeyaTwoScale.LatticePacking
public import KakeyaTwoScale.CapsuleCylinder

@[expose] public section

open Set Metric
noncomputable section
namespace KakeyaTwoScale

/-- The lower corner of an actual grid cube meeting a short flat cylinder
lies in a fixed multiple of the grid scale about the cylinder's start. -/
theorem shortCylinder_grid_corner_bound {n : ℕ} (A : ℝ)
    {δ L : ℝ} (hδ : 0 < δ) (hL : L ≤ A*δ)
    (b u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1)
    (z : Fin n → ℤ)
    (hmeet : ((WithLp.ofLp ⁻¹' gridCell δ z) ∩ flatCylinder b u L δ).Nonempty) :
    dist (latticePoint δ z) (WithLp.ofLp b) ≤ (A+2)*δ := by
  obtain ⟨x,hcell,t,ht,htL,_,herr⟩ := hmeet
  have hxb : dist x b < L+δ := by
    calc
      dist x b ≤ dist x (b+t • u) + dist (b+t • u) b := dist_triangle _ _ _
      _ < δ + t := by
        have he : dist (b+t • u) b = t := by
          rw [dist_eq_norm]
          simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, hu, mul_one,
            abs_of_pos ht]
        rw [he]
        have hd : dist x (b+t • u) < δ := herr
        linarith
      _ < L+δ := by linarith
  have hsup : dist (WithLp.ofLp x) (WithLp.ofLp b) ≤ dist x b := by
    apply (dist_pi_le_iff dist_nonneg).mpr
    intro j
    exact PiLp.dist_apply_le x b j
  have hround : gridRound δ (WithLp.ofLp x) = latticePoint δ z := by
    have hz := (mem_gridCell_iff hδ (WithLp.ofLp x) z).mp hcell
    funext j
    simp only [gridRound, latticePoint, hz]
  have hxcorner : dist (latticePoint δ z) (WithLp.ofLp x) ≤ δ := by
    simpa [hround, dist_comm] using dist_gridRound_le hδ (WithLp.ofLp x)
  calc
    dist (latticePoint δ z) (WithLp.ofLp b) ≤
      dist (latticePoint δ z) (WithLp.ofLp x) + dist (WithLp.ofLp x) (WithLp.ofLp b) :=
      dist_triangle _ _ _
    _ ≤ δ + dist x b := add_le_add hxcorner hsup
    _ ≤ (A+2)*δ := by linarith

/-- A genuinely constructed scale-uniform cap for the number of distinct
actual δ-grid cubes met by a cylinder of length at most Aδ. The packing
constant depends only on n,A, and precedes the scale, cylinder and finite family. -/
theorem exists_shortCylinder_grid_count (n : ℕ) (A : ℝ) :
    ∃ B : ℕ, 0 < B ∧ ∀ (δ L : ℝ), 0 < δ → L ≤ A*δ →
      ∀ (b u : EuclideanSpace ℝ (Fin n)), ‖u‖ = 1 →
      ∀ cubes : Finset (Fin n → ℤ),
      (∀ z ∈ cubes,
        ((WithLp.ofLp ⁻¹' gridCell δ z) ∩ flatCylinder b u L δ).Nonempty) →
      cubes.card ≤ B := by
  obtain ⟨B,hB⟩ := uniform_local_packing (X := Fin n → ℝ) (A+2)
  refine ⟨B+1, by omega, ?_⟩
  intro δ L hδ hL b u hu cubes hmeet
  apply (hB δ hδ (WithLp.ofLp b) cubes (latticePoint δ) ?_ ?_).trans (Nat.le_succ B)
  · intro z hz
    exact shortCylinder_grid_corner_bound A hδ hL b u hu z (hmeet z hz)
  · intro z _ w _ hne
    exact latticePoint_separated hδ hne

end KakeyaTwoScale
#print axioms KakeyaTwoScale.shortCylinder_grid_corner_bound
#print axioms KakeyaTwoScale.exists_shortCylinder_grid_count
