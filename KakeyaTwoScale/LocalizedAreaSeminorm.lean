module
public import KakeyaTwoScale.BoundedDirectionalArea
public import Mathlib.Analysis.Normed.Module.Seminorm.Norm

@[expose] public section

open MvPolynomial MeasureTheory Set Metric
open scoped ENNReal NNReal
noncomputable section
namespace KakeyaTwoScale

/-- Convert a proved finite directional functional to a real seminorm. -/
def DisjointChartAtlas.finiteSeminorm {n : ℕ} {Z : Set (Fin (n+1) → ℝ)}
    (A : DisjointChartAtlas n Z) (hfinite : ∀ v, A.directionalArea v ≠ ∞) :
    Seminorm ℝ (EuclideanSpace ℝ (Fin (n+1))) :=
  Seminorm.of (fun u => (A.directionalArea (WithLp.ofLp u)).toReal)
    (by
      intro u v
      have hh := ENNReal.toReal_mono (by simp [hfinite])
        (A.directionalArea_add_le (WithLp.ofLp u) (WithLp.ofLp v))
      rw [ENNReal.toReal_add (hfinite _) (hfinite _)] at hh
      exact hh)
    (by
      intro c u
      change (A.directionalArea (c • WithLp.ofLp u)).toReal = _
      rw [A.directionalArea_smul,ENNReal.toReal_mul,ENNReal.toReal_ofReal (abs_nonneg _)]
      rfl)

/-- The actual localized polynomial area seminorm. Finiteness is derived from
nonzeroness, bounded localization and the proved framed degree budget. -/
def polynomialLocalizedAreaSeminorm {n : ℕ}
    (P : MvPolynomial (Fin (n+1)) ℝ) (hP : P ≠ 0)
    (A : DisjointChartAtlas n {x | eval x P = 0})
    (K : Set (Fin (n+1) → ℝ)) (hK : MeasurableSet K)
    (r : ℝ) (hr : 0 ≤ r)
    (hbound : ∀ x ∈ K, ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (n+1)))‖ ≤ r) :
    Seminorm ℝ (EuclideanSpace ℝ (Fin (n+1))) :=
  (A.restrict K hK).finiteSeminorm
    (fun v => (polynomial_bounded_area_lt_top P hP A K hK r hr hbound v).ne)

theorem polynomialLocalizedAreaSeminorm_apply {n : ℕ}
    (P : MvPolynomial (Fin (n+1)) ℝ) (hP : P ≠ 0)
    (A : DisjointChartAtlas n {x | eval x P = 0})
    (K : Set (Fin (n+1) → ℝ)) (hK : MeasurableSet K)
    (r : ℝ) (hr : 0 ≤ r)
    (hbound : ∀ x ∈ K, ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (n+1)))‖ ≤ r)
    (u : EuclideanSpace ℝ (Fin (n+1))) :
    polynomialLocalizedAreaSeminorm P hP A K hK r hr hbound u =
      ((A.restrict K hK).directionalArea (WithLp.ofLp u)).toReal := rfl

/-- Explicit real norm bound; toReal is used only with a proved finite upper bound. -/
theorem polynomialLocalizedAreaSeminorm_le {n : ℕ}
    (P : MvPolynomial (Fin (n+1)) ℝ) (hP : P ≠ 0)
    (A : DisjointChartAtlas n {x | eval x P = 0})
    (K : Set (Fin (n+1) → ℝ)) (hK : MeasurableSet K)
    (r : ℝ) (hr : 0 ≤ r)
    (hbound : ∀ x ∈ K, ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (n+1)))‖ ≤ r)
    (u : EuclideanSpace ℝ (Fin (n+1))) :
    polynomialLocalizedAreaSeminorm P hP A K hK r hr hbound u ≤
      ((P.totalDegree : ℝ≥0∞) * volume (closedBall (0 : Fin n → ℝ) r)).toReal * ‖u‖ := by
  have ht : ENNReal.ofReal ‖u‖ * ((P.totalDegree : ℝ≥0∞) * volume (closedBall (0 : Fin n → ℝ) r)) ≠ ∞ :=
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.mul_lt_top (by simp) measure_closedBall_lt_top)).ne
  have hh := ENNReal.toReal_mono ht
    (polynomial_bounded_area_norm_le P hP A K hK r hr hbound (WithLp.ofLp u))
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (norm_nonneg _)] at hh
  simpa only [polynomialLocalizedAreaSeminorm_apply,mul_comm] using hh

/-- Continuity in the direction for each fixed polynomial and bounded region.
This does not assert continuity as the polynomial coefficients vary. -/
theorem polynomialLocalizedAreaSeminorm_continuous {n : ℕ}
    (P : MvPolynomial (Fin (n+1)) ℝ) (hP : P ≠ 0)
    (A : DisjointChartAtlas n {x | eval x P = 0})
    (K : Set (Fin (n+1) → ℝ)) (hK : MeasurableSet K)
    (r : ℝ) (hr : 0 ≤ r)
    (hbound : ∀ x ∈ K, ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (n+1)))‖ ≤ r) :
    Continuous (polynomialLocalizedAreaSeminorm P hP A K hK r hr hbound) := by
  let C : ℝ≥0 := ⟨((P.totalDegree : ℝ≥0∞) * volume (closedBall (0 : Fin n → ℝ) r)).toReal,
    ENNReal.toReal_nonneg⟩
  apply Seminorm.continuous_of_le
    (q := C • normSeminorm ℝ (EuclideanSpace ℝ (Fin (n+1))))
  · change Continuous (fun u : EuclideanSpace ℝ (Fin (n+1)) => (C : ℝ) * ‖u‖)
    exact continuous_const.mul continuous_norm
  · intro u
    exact polynomialLocalizedAreaSeminorm_le P hP A K hK r hr hbound u

end KakeyaTwoScale
#print axioms KakeyaTwoScale.DisjointChartAtlas.finiteSeminorm
#print axioms KakeyaTwoScale.polynomialLocalizedAreaSeminorm
#print axioms KakeyaTwoScale.polynomialLocalizedAreaSeminorm_le
#print axioms KakeyaTwoScale.polynomialLocalizedAreaSeminorm_continuous
