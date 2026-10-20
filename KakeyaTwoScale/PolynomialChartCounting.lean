module
public import KakeyaTwoScale.PolynomialHRZVolume
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

open MeasureTheory Set Metric MvPolynomial
open scoped ENNReal BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- Actual separated direction balls carry counting mass. Covering just their
centers would not suffice for this theorem or the subsequent sweep bound. -/
theorem separated_direction_ball_volume_le {m : ℕ} {I : Type*}
    (T : Finset I) (v : I → Fin m → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → δ ≤ dist (v i) (v j))
    (E : Set (Fin m → ℝ)) (hcover : ∀ i ∈ T, ball (v i) (δ/2) ⊆ E) :
    (T.card : ℝ≥0∞) * ENNReal.ofReal (δ^m) ≤ volume E := by
  classical
  have hdis : Set.PairwiseDisjoint (↑T : Set I) (fun i => ball (v i) (δ/2)) := by
    intro i hi j hj hij
    apply ball_disjoint_ball
    have hh := hsep i hi j hj hij
    linarith
  have hball (i : I) : volume (ball (v i) (δ/2))=ENNReal.ofReal (δ^m) := by
    rw [Real.volume_pi_ball _ (by positivity)]
    congr 1
    simp only [Fintype.card_fin]
    congr 1
    ring
  calc
    (T.card : ℝ≥0∞) * ENNReal.ofReal (δ^m) =
        volume (⋃ i ∈ T, ball (v i) (δ/2)) := by
      rw [measure_biUnion_finset hdis (fun _ _ => measurableSet_ball)]
      simp [hball]
    _ ≤ volume E := measure_mono (iUnion₂_subset hcover)

/-- Conditional only on concrete chart geometry: actual slope balls are
covered by finitely many polynomial images, and every actual chart sweep lies
in E. Multiplicity and analytic volume comparison are proved internally. -/
theorem polynomial_chart_direction_counting (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : ℕ) {I J : Type*}
      (T : Finset I) (charts : Finset J) (v : I → Fin m → ℝ)
      (P Q : J → Fin m → MvPolynomial (Fin m) ℝ)
      (S : J → Set (Fin m → ℝ)) (E : Set ((Fin m → ℝ) × ℝ))
      (δ a L : ℝ), 0 < δ → 0 < L →
      (∀ i ∈ T, ∀ j ∈ T, i ≠ j → δ ≤ dist (v i) (v j)) →
      (∀ j ∈ charts, IsCompact (S j)) →
      (∀ j ∈ charts, ∀ k, (P j k).totalDegree ≤ D) →
      (∀ j ∈ charts, ∀ k, (Q j k).totalDegree ≤ D) →
      (∀ i ∈ T, ball (v i) (δ/2) ⊆ ⋃ j ∈ charts, polynomialMapPi (Q j) '' S j) →
      (∀ j ∈ charts, differentiableLineSweep (polynomialMapPi (P j))
        (polynomialMapPi (Q j)) (S j) a L ⊆ E) →
      ((T.card : ℝ≥0∞) * ENNReal.ofReal (δ^m)) * ENNReal.ofReal (L^(m+1)) ≤
        ((ENNReal.ofReal C * (((4*D+1)^m : ℕ) : ℝ≥0∞)) * charts.card) *
          (volume.prod volume) E := by
  obtain ⟨C,hC,h⟩ := polynomialLineSweep_direction_volume m
  refine ⟨C,hC,?_⟩
  intro D I J T charts v P Q S E δ a L hδ hL hsep hS hP hQ hcover hsweep
  classical
  have hp := separated_direction_ball_volume_le T v hδ hsep _ hcover
  have hsum : volume (⋃ j ∈ charts, polynomialMapPi (Q j) '' S j) ≤
      ∑ j ∈ charts, volume (polynomialMapPi (Q j) '' S j) := measure_biUnion_finset_le _ _
  calc
    _ ≤ (∑ j ∈ charts, volume (polynomialMapPi (Q j) '' S j)) *
        ENNReal.ofReal (L^(m+1)) := mul_le_mul (hp.trans hsum) le_rfl zero_le zero_le
    _ = ∑ j ∈ charts, volume (polynomialMapPi (Q j) '' S j) *
        ENNReal.ofReal (L^(m+1)) := Finset.sum_mul _ _ _
    _ ≤ ∑ j ∈ charts, (ENNReal.ofReal C * (((4*D+1)^m : ℕ) : ℝ≥0∞)) *
        (volume.prod volume) E := by
      apply Finset.sum_le_sum
      intro j hj
      exact (h D (P j) (Q j) (hP j hj) (hQ j hj) (S j) (hS j hj) a L hL).trans
        (mul_le_mul le_rfl (measure_mono (hsweep j hj)) zero_le zero_le)
    _ = _ := by simp [mul_assoc,mul_comm,mul_left_comm]

/-- Approximation-compatible counting: the uncovered directions are retained
as an actual exceptional set with an explicit additive volume cost. -/
theorem polynomial_chart_direction_counting_with_error (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : ℕ) {I J : Type*}
      (T : Finset I) (charts : Finset J) (v : I → Fin m → ℝ)
      (P Q : J → Fin m → MvPolynomial (Fin m) ℝ)
      (S : J → Set (Fin m → ℝ)) (E : Set ((Fin m → ℝ) × ℝ))
      (Bad : Set (Fin m → ℝ)) (δ a L : ℝ), 0 < δ → 0 < L →
      (∀ i ∈ T, ∀ j ∈ T, i ≠ j → δ ≤ dist (v i) (v j)) →
      (∀ j ∈ charts, IsCompact (S j)) →
      (∀ j ∈ charts, ∀ k, (P j k).totalDegree ≤ D) →
      (∀ j ∈ charts, ∀ k, (Q j k).totalDegree ≤ D) →
      (∀ i ∈ T, ball (v i) (δ/2) ⊆ Bad ∪ ⋃ j ∈ charts, polynomialMapPi (Q j) '' S j) →
      (∀ j ∈ charts, differentiableLineSweep (polynomialMapPi (P j))
        (polynomialMapPi (Q j)) (S j) a L ⊆ E) →
      ((T.card : ℝ≥0∞) * ENNReal.ofReal (δ^m)) * ENNReal.ofReal (L^(m+1)) ≤
        volume Bad * ENNReal.ofReal (L^(m+1)) +
        ((ENNReal.ofReal C * (((4*D+1)^m : ℕ) : ℝ≥0∞)) * charts.card) *
          (volume.prod volume) E := by
  obtain ⟨C,hC,h⟩ := polynomialLineSweep_direction_volume m
  refine ⟨C,hC,?_⟩
  intro D I J T charts v P Q S E Bad δ a L hδ hL hsep hS hP hQ hcover hsweep
  classical
  have hp := separated_direction_ball_volume_le T v hδ hsep _ hcover
  have hsum : volume (Bad ∪ ⋃ j ∈ charts, polynomialMapPi (Q j) '' S j) ≤
      volume Bad + ∑ j ∈ charts, volume (polynomialMapPi (Q j) '' S j) :=
    (measure_union_le _ _).trans (add_le_add le_rfl (measure_biUnion_finset_le _ _))
  calc
    _ ≤ (volume Bad + ∑ j ∈ charts, volume (polynomialMapPi (Q j) '' S j)) *
        ENNReal.ofReal (L^(m+1)) := mul_le_mul (hp.trans hsum) le_rfl zero_le zero_le
    _ = volume Bad * ENNReal.ofReal (L^(m+1)) +
        ∑ j ∈ charts, volume (polynomialMapPi (Q j) '' S j) *
          ENNReal.ofReal (L^(m+1)) := by rw [add_mul,Finset.sum_mul]
    _ ≤ volume Bad * ENNReal.ofReal (L^(m+1)) +
        ∑ j ∈ charts, (ENNReal.ofReal C * (((4*D+1)^m : ℕ) : ℝ≥0∞)) *
          (volume.prod volume) E := by
      apply add_le_add le_rfl
      apply Finset.sum_le_sum
      intro j hj
      exact (h D (P j) (Q j) (hP j hj) (hQ j hj) (S j) (hS j hj) a L hL).trans
        (mul_le_mul le_rfl (measure_mono (hsweep j hj)) zero_le zero_le)
    _ = _ := by simp [mul_assoc,mul_comm,mul_left_comm]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.separated_direction_ball_volume_le
#print axioms KakeyaTwoScale.polynomial_chart_direction_counting

#print axioms KakeyaTwoScale.polynomial_chart_direction_counting_with_error
