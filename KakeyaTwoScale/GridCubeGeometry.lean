module
public import KakeyaTwoScale.FiniteGridPlaneBank

@[expose] public section

open Set Metric
noncomputable section
namespace KakeyaTwoScale

theorem closedGridFace_subset_cube {d : ℕ} (a theta : Fin d→ℝ) (h : ℝ) (hh : 0≤h)
    (k : Fin d→ℤ) (sigma : Fin d→Option Bool) :
    closedGridFace a theta h k sigma⊆closedGridFace a theta h k (fun _=>none) := by
  intro x hx j
  have hxj := hx j
  cases he : sigma j with
  | none => simpa only [he] using hxj
  | some b =>
    cases b <;> simp only [he] at hxj
    · exact ⟨hxj.ge,by linarith⟩
    · exact ⟨by linarith,hxj.le⟩

theorem closed_grid_cube_diameter {d : ℕ} (a theta : Fin d→ℝ) (h : ℝ) (hh : 0≤h)
    (k : Fin d→ℤ) (x y : EuclideanSpace ℝ (Fin d))
    (hx : x∈closedGridFace a theta h k (fun _=>none))
    (hy : y∈closedGridFace a theta h k (fun _=>none)) :
    dist x y≤(d+1)*h := by
  have hs : (∑ j, (x j-y j)^2)≤(d:ℝ)*h^2 := by
    calc
      _ ≤ ∑ _j : Fin d, h^2 := by
        apply Finset.sum_le_sum
        intro j _
        have hxj : gridLevel a theta h k j≤x j ∧ x j≤gridLevel a theta h k j+h := hx j
        have hyj : gridLevel a theta h k j≤y j ∧ y j≤gridLevel a theta h k j+h := hy j
        have habs : |x j-y j|≤h := abs_le.mpr ⟨by linarith,by linarith⟩
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (x j-y j)) habs 2
      _ = _ := by simp
  have he : (∑ j, (x j-y j)^2)=dist x y^2 := by
    rw [dist_eq_norm,EuclideanSpace.real_norm_sq_eq]
    rfl
  rw [he] at hs
  have hd : (d:ℝ)≤(d+1)^2 := by nlinarith [sq_nonneg (d:ℝ)]
  have hm := mul_le_mul_of_nonneg_right hd (sq_nonneg h)
  have hp : 0≤((d:ℝ)+1)*h := by positivity
  nlinarith [dist_nonneg (x := x) (y := y)]

/-- Every point of any face of an occupied cube lies in the same controlled
larger ball. The clipping radius is uniform over all occupied cubes. -/
theorem grid_face_localization {d : ℕ} (a theta : Fin d→ℝ) (h : ℝ) (hh : 0≤h)
    (k : Fin d→ℤ) (sigma : Fin d→Option Bool)
    (center : EuclideanSpace ℝ (Fin d)) (R : ℝ)
    (y : EuclideanSpace ℝ (Fin d)) (hy : y∈closedGridFace a theta h k (fun _=>none))
    (hyR : y∈closedBall center R) :
    closedGridFace a theta h k sigma⊆closedBall center (R+(d+1)*h) := by
  intro x hx
  have hd := closed_grid_cube_diameter a theta h hh k x y
    (closedGridFace_subset_cube a theta h hh k sigma hx) hy
  have ht := dist_triangle x y center
  change dist x center≤R+((d:ℝ)+1)*h
  change dist y center≤R at hyR
  linarith

end KakeyaTwoScale
#print axioms KakeyaTwoScale.closedGridFace_subset_cube
#print axioms KakeyaTwoScale.closed_grid_cube_diameter
#print axioms KakeyaTwoScale.grid_face_localization
