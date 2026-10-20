module
public import KakeyaTwoScale.CoordinateSliceComponents

@[expose] public section

open Set Metric
noncomputable section
namespace KakeyaTwoScale

def gridFaceLabels {d : ℕ} (k : Fin d→ℤ) (sigma : Fin d→Option Bool) : Fin d→ℤ :=
  fun j => k j+(if sigma j=some true then 1 else 0)

theorem closedGridFace_eq_plane_box {d : ℕ} (a theta : Fin d→ℝ) (h : ℝ)
    (k : Fin d→ℤ) (sigma : Fin d→Option Bool) :
    closedGridFace a theta h k sigma =
      coordinateGridPlane a theta h (gridFaceLabels k sigma) (gridFaceFixed sigma) ∩
      closedFreeBox (fun j x => x j) (gridFaceFixed sigma)
        (gridLevel a theta h k) (fun j => gridLevel a theta h k j+h) := by
  ext x
  constructor
  · intro hx
    constructor
    · intro j hj
      have hsj : sigma j≠none := (mem_gridFaceFixed sigma j).mp hj
      cases he : sigma j with
      | none => exact False.elim (hsj he)
      | some b =>
        have hxj := hx j
        cases b <;> simpa [gridFaceLabels,gridLevel,he,add_mul,add_assoc] using hxj
    · intro j hj
      have he : sigma j=none := by simpa using hj
      simpa only [he] using hx j
  · rintro ⟨hp,hb⟩ j
    cases he : sigma j with
    | none => exact hb j (by simp [he])
    | some b =>
      have hj : j∈gridFaceFixed sigma := by simp [he]
      have hxj := hp j hj
      cases b <;> simpa [gridFaceLabels,gridLevel,he,add_mul,add_assoc] using hxj

/-- A selected terminal face traps an actual component of the ball-clipped
algebraic coordinate slice. All clipping hypotheses concern the representative;
no regularity of the clipping sphere is required. -/
theorem terminal_grid_face_component {d : ℕ}
    (Z : Set (EuclideanSpace ℝ (Fin d))) (a theta : Fin d→ℝ) (h : ℝ)
    (k : Fin d→ℤ) (sigma : Fin d→Option Bool)
    (hterminal : Z∩closedGridFace a theta h k sigma ⊆
      openFreeBox (fun j x => x j) (gridFaceFixed sigma)
        (gridLevel a theta h k) (fun j => gridLevel a theta h k j+h))
    (center : EuclideanSpace ℝ (Fin d)) (R : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (hx : x∈Z∩closedGridFace a theta h k sigma)
    (hxR : x∈closedBall center R) :
    let K := (Z∩coordinateGridPlane a theta h (gridFaceLabels k sigma) (gridFaceFixed sigma)) ∩
      closedBall center R
    connectedComponentIn K x ∈ actualSetComponents K ∧
      connectedComponentIn K x ⊆ openFreeBox (fun j x => x j) (gridFaceFixed sigma)
        (gridLevel a theta h k) (fun j => gridLevel a theta h k j+h) := by
  dsimp only
  have hxf := hx.2
  rw [closedGridFace_eq_plane_box] at hxf
  have hxK := And.intro (And.intro hx.1 hxf.1) hxR
  refine ⟨⟨x,hxK,rfl⟩,?_⟩
  apply component_trapped_in_openFreeBox (fun j x => x j)
    (fun j => (continuous_apply j).comp (PiLp.continuous_ofLp 2 _)) _ _ _ _ _ x hxK hxf.2
  rintro y ⟨hy,hb⟩
  apply hterminal
  refine ⟨hy.1.1,?_⟩
  rw [closedGridFace_eq_plane_box]
  exact ⟨hy.1.2,hb⟩

/-- Distinct open intervals of one translated grid do not overlap. -/
theorem open_grid_interval_index_unique (a theta h : ℝ) (hh : 0<h) (k l : ℤ) (x : ℝ)
    (hk : a+theta+k*h<x ∧ x<a+theta+k*h+h)
    (hl : a+theta+l*h<x ∧ x<a+theta+l*h+h) : k=l := by
  by_contra he
  rcases lt_or_gt_of_ne he with hkl | hlk
  · have hi : (k:ℝ)+1≤l := by exact_mod_cast hkl
    nlinarith [hk.2,hl.1]
  · have hi : (l:ℝ)+1≤k := by exact_mod_cast hlk
    nlinarith [hl.2,hk.1]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.closedGridFace_eq_plane_box
#print axioms KakeyaTwoScale.terminal_grid_face_component
#print axioms KakeyaTwoScale.open_grid_interval_index_unique
