module
public import KakeyaTwoScale.PrescribedCubeVisibility

@[expose] public section

open Set Metric MeasureTheory
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

def cubeFamilyRadius {n J : ℕ} (z : Fin J → Fin (n+1) → ℝ) : ℝ :=
  (finite_visibility_cubes_bounded z).choose

theorem cubeFamilyRadius_nonneg {n J : ℕ} (z : Fin J → Fin (n+1) → ℝ) :
    0≤cubeFamilyRadius z := (finite_visibility_cubes_bounded z).choose_spec.choose

theorem cubeFamilyRadius_bound {n J : ℕ} (z : Fin J → Fin (n+1) → ℝ) :
    ∀ j x, x∈visibilityCube (z j) →
      ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (n+1)))‖≤cubeFamilyRadius z :=
  (finite_visibility_cubes_bounded z).choose_spec.choose_spec

def prescribedCubeBody (n D J : ℕ) (z : Fin J → Fin (n+1) → ℝ)
    (ε : ℝ) (p : FullCoefficientSphere (n+1) D) (j : Fin J) : Set (Fin (n+1) → ℝ) :=
  fullCubeVisibilityBody n D (z j) (cubeFamilyRadius z)
    (cubeFamilyRadius_nonneg z) (cubeFamilyRadius_bound z j) ε p

theorem fullCubeVisibilityBody_volume_pos (n D : ℕ) (z : Fin (n+1) → ℝ)
    (r : ℝ) (hr : 0≤r)
    (hb : ∀ x∈visibilityCube z, ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (n+1)))‖≤r)
    (ε : ℝ) (hε : 0<ε) (hε2 : ε<2) (p : FullCoefficientSphere (n+1) D) :
    0<volume.real (fullCubeVisibilityBody n D z r hr hb ε p) := by
  let m := fullDegreeFinMonomial (n+1) D
  have hm := fullDegreeFinMonomial_injective (n+1) D
  have hmD := fullDegreeFinMonomial_degree (n+1) D
  let s := mollifiedAreaSeminorm m hm hmD (visibilityCube z)
    isClosed_closedBall.measurableSet (Or.inr isClosed_closedBall) r hr hb ε p
  have hs : Continuous s := by
    have hh := (continuous_mollifiedArea_joint m hm hmD (visibilityCube z)
      isClosed_closedBall.measurableSet (Or.inr isClosed_closedBall) r hr hb ε hε hε2).comp
      (show Continuous (fun v : EuclideanSpace ℝ (Fin (n+1)) => (p,v)) from
        continuous_const.prodMk continuous_id)
    exact hh
  have hv := mollifiedVisibilityBody_volume_bounds m hm hmD (visibilityCube z)
    isClosed_closedBall.measurableSet (Or.inr isClosed_closedBall) r hr hb ε hε p
  change 0<volume (seminormVisibilityBody s) ∧ volume (seminormVisibilityBody s)<∞ at hv
  rw [← coordinateVisibilityBody_volume s hs] at hv
  exact ENNReal.toReal_pos hv.1.ne' hv.2.ne

/-- The ordinary visibility inequality, with a positive finite body volume. -/
theorem visibility_of_powered_volume {N : ℕ} (hN : 0<N) (V v : ℝ)
    (hV : 0≤V) (hv : 0<v) (h : V^N*v≤1) :
    V≤v^(-((N:ℝ)⁻¹)) := by
  have hh : V≤(v⁻¹)^((N:ℝ)⁻¹) := by
    apply (Real.le_rpow_inv_iff_of_pos hV (inv_nonneg.mpr hv.le) (Nat.cast_pos.mpr hN)).mpr
    rw [Real.rpow_natCast]
    simpa only [one_div] using (le_div_iff₀ hv).mpr h
  have he : (v⁻¹)^((N:ℝ)⁻¹)=v^(-((N:ℝ)⁻¹)) := by
    rw [← Real.rpow_neg_one v,← Real.rpow_mul hv.le]
    congr 1
    ring
  exact hh.trans_eq he

/-- Complete prescribed visibility on any finite family of translated closed
unit cubes, for all nonnegative targets. The coefficient sphere is the full
total-degree sphere; the polynomial and its degree are actual outputs. -/
theorem prescribed_visibility (n : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ (J : ℕ) (z : Fin J → Fin (n+1) → ℝ)
      (V : Fin J → ℝ), (∀ j, 0≤V j) →
      ∃ D : ℕ, (D:ℝ)≤C*(∑ j,(V j)^(n+1))^(((n+1:ℕ):ℝ)⁻¹) ∧
      ∃ δ>0, δ<2 ∧ ∀ ε : ℝ, 0<ε → ε≤δ →
        ∃ p : FullCoefficientSphere (n+1) D,
          coefficientPolynomial (fullDegreeFinMonomial (n+1) D) p.val≠0 ∧
          (coefficientPolynomial (fullDegreeFinMonomial (n+1) D) p.val).totalDegree≤D ∧
          ∀ j, V j≤(volume.real (prescribedCubeBody n D J z ε p j))^(-(((n+1:ℕ):ℝ)⁻¹)) := by
  obtain ⟨K,hK,h⟩ := prescribed_cube_visibility n
  refine ⟨K^(((n+1:ℕ):ℝ)⁻¹),Real.rpow_pos_of_pos hK _,?_⟩
  intro J z V hV
  have hsum : 0≤∑ j,(V j)^(n+1) := Finset.sum_nonneg (fun j _ => pow_nonneg (hV j) _)
  obtain ⟨D,hD,δ,hδ,hδ2,hall⟩ := h J z (fun j => (V j)^(n+1))
    (fun j => pow_nonneg (hV j) _) (cubeFamilyRadius z) (cubeFamilyRadius_nonneg z) (cubeFamilyRadius_bound z)
  have hdegree : (D:ℝ)≤(K*(∑ j,(V j)^(n+1)))^(((n+1:ℕ):ℝ)⁻¹) := by
    apply (Real.le_rpow_inv_iff_of_pos (Nat.cast_nonneg D) (mul_nonneg hK.le hsum) (by positivity)).mpr
    simpa only [Real.rpow_natCast] using hD
  rw [Real.mul_rpow hK.le hsum] at hdegree
  refine ⟨D,hdegree,δ,hδ,hδ2,?_⟩
  intro ε hε hεδ
  obtain ⟨p,hp⟩ := hall ε hε hεδ
  refine ⟨p,coefficientPolynomial_nonzero _ (fullDegreeFinMonomial_injective _ _) _ ?_,
    coefficientPolynomial_degree _ (fullDegreeFinMonomial_degree _ _) _,?_⟩
  · exact coefficientSphere_nonzero (metricCoefficient p)
  · intro j
    exact visibility_of_powered_volume (by omega : 0<n+1) (V j) _ (hV j)
      (fullCubeVisibilityBody_volume_pos n D (z j) (cubeFamilyRadius z)
        (cubeFamilyRadius_nonneg z) (cubeFamilyRadius_bound z j) ε hε (hεδ.trans_lt hδ2) p) (hp j)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.prescribed_visibility
