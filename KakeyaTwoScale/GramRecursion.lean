module
public import KakeyaTwoScale.BroadTupleContribution
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
open Classical

 theorem det_gram_cons_span_row_zero {n k : ℕ}
    (v : Fin k → EuclideanSpace ℝ (Fin n)) (u z : EuclideanSpace ℝ (Fin n))
    (hz : z∈Submodule.span ℝ (Set.range v)) :
    ((Matrix.gram ℝ (Fin.cons (α := fun _ => EuclideanSpace ℝ (Fin n)) u v)).updateRow 0
      (fun j : Fin (k+1) => inner ℝ z (Fin.cons (α := fun _ => EuclideanSpace ℝ (Fin n)) u v j))).det=0 := by
  let M := Matrix.gram ℝ (Fin.cons (α := fun _ => EuclideanSpace ℝ (Fin n)) u v)
  change (M.updateRow 0 (fun j : Fin (k+1) => inner ℝ z (Fin.cons (α := fun _ => EuclideanSpace ℝ (Fin n)) u v j))).det=0
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i,rfl⟩ := hx
    have he : (fun j : Fin (k+1) => inner ℝ (v i) (Fin.cons (α := fun _ => EuclideanSpace ℝ (Fin n)) u v j))=M i.succ := by
      funext j
      simp [M,Matrix.gram_apply]
    rw [he]
    exact Matrix.det_updateRow_eq_zero (Fin.succ_ne_zero i)
  | zero =>
    apply Matrix.det_eq_zero_of_row_eq_zero 0
    intro j
    simp
  | add x y hx hy ihx ihy =>
    have he : (fun j : Fin (k+1) => inner ℝ (x+y) (Fin.cons (α := fun _ => EuclideanSpace ℝ (Fin n)) u v j))=
        (fun j : Fin (k+1) => inner ℝ x (Fin.cons (α := fun _ => EuclideanSpace ℝ (Fin n)) u v j))+(fun j : Fin (k+1) => inner ℝ y (Fin.cons (α := fun _ => EuclideanSpace ℝ (Fin n)) u v j)) := by
      funext j
      exact inner_add_left _ _ _
    rw [he,Matrix.det_updateRow_add,ihx,ihy,add_zero]
  | smul a x hx ih =>
    have he : (fun j : Fin (k+1) => inner ℝ (a • x) (Fin.cons (α := fun _ => EuclideanSpace ℝ (Fin n)) u v j))=
        a • (fun j : Fin (k+1) => inner ℝ x (Fin.cons (α := fun _ => EuclideanSpace ℝ (Fin n)) u v j)) := by
      funext j
      simp only [inner_smul_left,conj_trivial,Pi.smul_apply,smul_eq_mul]
    rw [he,Matrix.det_updateRow_smul,ih,mul_zero]

 theorem det_gram_cons_normal {n k : ℕ}
    (v : Fin k → EuclideanSpace ℝ (Fin n)) (u : EuclideanSpace ℝ (Fin n)) :
    (Matrix.gram ℝ (Fin.cons (α := fun _ => EuclideanSpace ℝ (Fin n)) u v)).det =
      ‖normalProjection (Submodule.span ℝ (Set.range v)) u‖^2*(Matrix.gram ℝ v).det := by
  let H := Submodule.span ℝ (Set.range v)
  let z := normalProjection H u
  let t := H.starProjection u
  let M := Matrix.gram ℝ (Fin.cons (α := fun _ => EuclideanSpace ℝ (Fin n)) u v)
  have ht : t∈H := H.starProjection_apply_mem u
  have hz : z∈Hᗮ := normalProjection_mem H u
  have hsplit : u=z+t := by
    dsimp [z,t,normalProjection]
    rw [Submodule.starProjection_orthogonal_val]
    abel
  have hrow : M 0=(fun j : Fin (k+1) => inner ℝ z (Fin.cons (α := fun _ => EuclideanSpace ℝ (Fin n)) u v j))+
      (fun j : Fin (k+1) => inner ℝ t (Fin.cons (α := fun _ => EuclideanSpace ℝ (Fin n)) u v j)) := by
    funext j
    change inner ℝ u (Fin.cons (α := fun _ => EuclideanSpace ℝ (Fin n)) u v j)=_
    calc
      _ = inner ℝ (z+t) (Fin.cons (α := fun _ => EuclideanSpace ℝ (Fin n)) u v j) := congrArg (fun a => inner ℝ a (Fin.cons (α := fun _ => EuclideanSpace ℝ (Fin n)) u v j)) hsplit
      _ = _ := inner_add_left _ _ _
  have hdet : M.det=(M.updateRow 0 (fun j : Fin (k+1) => inner ℝ z (Fin.cons (α := fun _ => EuclideanSpace ℝ (Fin n)) u v j))).det := by
    have hh := Matrix.det_updateRow_add M 0
      (fun j : Fin (k+1) => inner ℝ z (Fin.cons (α := fun _ => EuclideanSpace ℝ (Fin n)) u v j)) (fun j : Fin (k+1) => inner ℝ t (Fin.cons (α := fun _ => EuclideanSpace ℝ (Fin n)) u v j))
    rw [← hrow,Matrix.updateRow_eq_self] at hh
    have htzero := det_gram_cons_span_row_zero v u t ht
    change (M.updateRow 0 (fun j : Fin (k+1) => inner ℝ t (Fin.cons (α := fun _ => EuclideanSpace ℝ (Fin n)) u v j))).det=0 at htzero
    rw [htzero,add_zero] at hh
    exact hh
  rw [hdet,Matrix.det_succ_row_zero,Fin.sum_univ_succ]
  have hzu : inner ℝ z u=‖z‖^2 := by
    have hh := inner_tangent Hᗮ u
    change inner ℝ u z=‖z‖^2 at hh
    rwa [real_inner_comm] at hh
  have hzero : ∀ i : Fin k, inner ℝ z (v i)=0 := by
    intro i
    rw [real_inner_comm]
    exact (Submodule.mem_orthogonal H z).mp hz (v i) (Submodule.subset_span ⟨i,rfl⟩)
  have hminor : (M.updateRow 0 (fun j : Fin (k+1) => inner ℝ z (Fin.cons (α := fun _ => EuclideanSpace ℝ (Fin n)) u v j))).submatrix Fin.succ Fin.succ =
      Matrix.gram ℝ v := by
    ext i j
    simp [M,Matrix.updateRow_apply,Matrix.gram_apply]
  have hsum : (∑ j : Fin k, (-1:ℝ)^(j.succ:ℕ)*
      (M.updateRow 0 (fun j : Fin (k+1) => inner ℝ z (Fin.cons (α := fun _ => EuclideanSpace ℝ (Fin n)) u v j))) 0 j.succ *
      ((M.updateRow 0 (fun j : Fin (k+1) => inner ℝ z (Fin.cons (α := fun _ => EuclideanSpace ℝ (Fin n)) u v j))).submatrix Fin.succ j.succ.succAbove).det)=0 := by
    apply Finset.sum_eq_zero
    intro i _
    simp [Matrix.updateRow_apply,hzero]
  rw [hsum]
  simp [Matrix.updateRow_apply,hzu,hminor,z,H]

/-- Exact Gram-volume recursion, with no independence hypothesis. -/
theorem tupleWedgeVolume_cons {n k : ℕ}
    (v : Fin k → EuclideanSpace ℝ (Fin n)) (u : EuclideanSpace ℝ (Fin n)) :
    tupleWedgeVolume (Fin.cons u v) = tupleWedgeVolume v *
      ‖normalProjection (Submodule.span ℝ (Set.range v)) u‖ := by
  unfold tupleWedgeVolume
  rw [det_gram_cons_normal,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs,abs_norm,mul_comm]

/-- The first unit vector contributes exactly one, preserving the source's
k-1 transversality exponent rather than introducing an unnecessary rho. -/
theorem tupleWedgeVolume_singleton {n : ℕ}
    (v : Fin 1 → EuclideanSpace ℝ (Fin n)) : tupleWedgeVolume v=‖v 0‖ := by
  simp [tupleWedgeVolume,Matrix.gram_apply]

/-- Quantitative recursion for the geometric greedy construction. -/
theorem tupleWedgeVolume_cons_lower {n k : ℕ}
    (v : Fin k → EuclideanSpace ℝ (Fin n)) (u : EuclideanSpace ℝ (Fin n))
    (A η : ℝ) (hη : 0≤η)
    (hv : A≤tupleWedgeVolume v)
    (hu : η≤‖normalProjection (Submodule.span ℝ (Set.range v)) u‖) :
    A*η≤tupleWedgeVolume (Fin.cons u v) := by
  rw [tupleWedgeVolume_cons]
  exact mul_le_mul hv hu hη (tupleWedgeVolume_nonneg v)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.det_gram_cons_span_row_zero
#print axioms KakeyaTwoScale.det_gram_cons_normal

#print axioms KakeyaTwoScale.tupleWedgeVolume_cons
#print axioms KakeyaTwoScale.tupleWedgeVolume_singleton
#print axioms KakeyaTwoScale.tupleWedgeVolume_cons_lower
