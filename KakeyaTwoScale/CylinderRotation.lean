module
public import KakeyaTwoScale.CapsuleCylinder
public import KakeyaTwoScale.ZahlContract
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

@[expose] public section

open MeasureTheory Metric
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- Canonical coordinate cylinder, with axis indexed by i. -/
def coordinateCylinder {n : ℕ} (i : Fin n) (L r : ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | 0 < x i ∧ x i < L ∧ ‖x-(x i) • EuclideanSpace.single i 1‖ < r}

 theorem coordinateCylinder_eq_flatCylinder {n : ℕ} (i : Fin n) (L r : ℝ) :
    coordinateCylinder i L r = flatCylinder 0 (EuclideanSpace.single i 1) L r := by
  ext x
  constructor
  · rintro ⟨h0,hL,hr⟩
    refine ⟨x i,h0,hL,?_,by simpa using hr⟩
    simp [EuclideanSpace.inner_single_left]
  · rintro ⟨t,h0,hL,hi,hr⟩
    have ht : x i=t := by simpa [EuclideanSpace.inner_single_left,sub_eq_zero] using hi
    exact ⟨ht ▸ h0, ht ▸ hL, by simpa [ht] using hr⟩

/-- The coordinate residual is precisely the Euclidean transverse radius. -/
theorem coordinateCylinder_mem_iff_sum {n : ℕ} (i : Fin n)
    (x : EuclideanSpace ℝ (Fin n)) (L r : ℝ) :
    x ∈ coordinateCylinder i L r ↔
      0 < x i ∧ x i < L ∧ Real.sqrt (∑ j ∈ Finset.univ.erase i, (x j)^2) < r := by
  classical
  have hn : ‖x-(x i) • EuclideanSpace.single i 1‖ =
      Real.sqrt (∑ j ∈ Finset.univ.erase i, (x j)^2) := by
    rw [EuclideanSpace.norm_eq]
    congr 1
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    simp only [PiLp.single_apply, ite_true, mul_one, sub_self, norm_zero,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
    apply Finset.sum_congr rfl
    intro j hj
    have hji := (Finset.mem_erase.mp hj).1
    simp [hji, Real.norm_eq_abs, sq_abs]
  simp only [coordinateCylinder, Set.mem_ofPred_eq, hn]

/-- The affine orthogonal map transports the entire flat-cylinder set exactly. -/
theorem flatCylinder_isometry_image {n : ℕ}
    (R : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (b u : EuclideanSpace ℝ (Fin n)) (L r : ℝ) :
    (fun x => b+R x) '' flatCylinder 0 u L r = flatCylinder b (R u) L r := by
  ext x
  constructor
  · rintro ⟨y,⟨t,h0,hL,hi,hr⟩,rfl⟩
    have he : b+R y-(b+t • R u)= R (y-(0+t • u)) := by simp
    refine ⟨t,h0,hL,?_,?_⟩
    · rw [he, R.inner_map_map]; exact hi
    · rw [he, R.norm_map]; exact hr
  · rintro ⟨t,h0,hL,hi,hr⟩
    refine ⟨R.symm (x-b),⟨t,h0,hL,?_,?_⟩,by simp⟩
    · have he : R (R.symm (x-b)-(0+t • u))=x-(b+t • R u) := by simp; module
      rw [← R.inner_map_map,he]; exact hi
    · rw [← R.norm_map (R.symm (x-b)-(0+t • u))]
      simpa [map_sub,map_smul,sub_sub] using hr

/-- Equal-length vectors can be aligned by an explicitly existing orthogonal map. -/
theorem exists_axis_isometry {n : ℕ} (i : Fin n)
    (u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖=1) :
    ∃ R : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n),
      R (EuclideanSpace.single i 1)=u := by
  refine ⟨(ℝ ∙ (EuclideanSpace.single i 1-u))ᗮ.reflection,?_⟩
  apply Submodule.reflection_sub
  simpa using hu.symm

/-- Every unit-axis flat cylinder is a translated orthogonal copy of the
canonical coordinate cylinder; no normalization is assumed as an input. -/
theorem flatCylinder_eq_coordinate_isometry_image {n : ℕ} (i : Fin n)
    (b u : EuclideanSpace ℝ (Fin n)) (L r : ℝ) (hu : ‖u‖=1) :
    ∃ R : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n),
      R (EuclideanSpace.single i 1)=u ∧
      flatCylinder b u L r = (fun x => b+R x) '' coordinateCylinder i L r := by
  obtain ⟨R,hR⟩ := exists_axis_isometry i u hu
  refine ⟨R,hR,?_⟩
  rw [coordinateCylinder_eq_flatCylinder,flatCylinder_isometry_image,hR]

/-- Orthogonal normalization preserves the actual Gram-volume wedge factor. -/
theorem tupleWedgeVolume_isometry {n k : ℕ}
    (R : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (v : Fin k → EuclideanSpace ℝ (Fin n)) :
    tupleWedgeVolume (fun i => R (v i))=tupleWedgeVolume v := by
  have he : Matrix.gram ℝ (fun i => R (v i)) = Matrix.gram ℝ v := by
    ext i j
    exact R.inner_map_map _ _
  simp only [tupleWedgeVolume,he]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.coordinateCylinder_eq_flatCylinder
#print axioms KakeyaTwoScale.coordinateCylinder_mem_iff_sum
#print axioms KakeyaTwoScale.flatCylinder_isometry_image
#print axioms KakeyaTwoScale.exists_axis_isometry
#print axioms KakeyaTwoScale.flatCylinder_eq_coordinate_isometry_image
#print axioms KakeyaTwoScale.tupleWedgeVolume_isometry
