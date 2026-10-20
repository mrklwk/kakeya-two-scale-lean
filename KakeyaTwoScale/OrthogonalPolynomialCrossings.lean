module
public import KakeyaTwoScale.CoordinatePolynomialCrossings
public import KakeyaTwoScale.OrthogonalPolynomialTransport
public import KakeyaTwoScale.CylinderRotation
public import Mathlib.Algebra.MvPolynomial.Funext

@[expose] public section

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- Orthogonal pullback preserves nonzeroness, proved from evaluations. -/
theorem polynomial_isometry_pullback_ne_zero {n : ℕ}
    (P : MvPolynomial (Fin n) ℝ) (hP : P≠0)
    (R : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    polynomialLinearPullback R.toContinuousLinearEquiv.toContinuousLinearMap P≠0 := by
  intro h
  apply hP
  apply MvPolynomial.funext
  intro x
  have hh := polynomialLinearPullback_eval R.toContinuousLinearEquiv.toContinuousLinearMap
    P (R.symm (WithLp.toLp 2 x))
  rw [h] at hh
  simpa using hh.symm

/-- Projection count in genuine orthogonal coordinates; the base carries
(n-dimensional) coordinate volume, not zero ambient volume on a hyperplane. -/
def frameCrossingCount {n : ℕ} (P : MvPolynomial (Fin (n+1)) ℝ)
    (R : EuclideanSpace ℝ (Fin (n+1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n+1)))
    (y : Fin n→ℝ) : ℝ≥0∞ :=
  ({t : ℝ | MvPolynomial.eval (R (WithLp.toLp 2 (Fin.cons t y))) P=0}:Set ℝ).encard.toENNReal

theorem frameCrossingCount_eq_coordinate {n : ℕ} (P : MvPolynomial (Fin (n+1)) ℝ)
    (R : EuclideanSpace ℝ (Fin (n+1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n+1))) (y : Fin n→ℝ) :
    frameCrossingCount P R y = coordinateCrossingCount
      (polynomialLinearPullback R.toContinuousLinearEquiv.toContinuousLinearMap P) y := by
  unfold frameCrossingCount coordinateCrossingCount coordinateZeroFiber
  congr 2
  ext t
  exact Iff.of_eq ((congrArg (fun z : ℝ => z=0)
    (polynomialLinearPullback_eval R.toContinuousLinearEquiv.toContinuousLinearMap P
      (WithLp.toLp 2 (Fin.cons t y)))).symm)

/-- Uniform count bound in every orthogonal frame, including exceptional
whole lines only on an intrinsic-base null set. -/
theorem ae_frame_crossing_count_le {n : ℕ} (P : MvPolynomial (Fin (n+1)) ℝ) (hP : P≠0)
    (R : EuclideanSpace ℝ (Fin (n+1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n+1))) :
    ∀ᵐ y : Fin n→ℝ, frameCrossingCount P R y ≤ (P.totalDegree:ℝ≥0∞) := by
  have ha := ae_coordinate_crossing_count_le _ (polynomial_isometry_pullback_ne_zero P hP R)
  have hd : ((polynomialLinearPullback R.toContinuousLinearEquiv.toContinuousLinearMap P).totalDegree:ℝ≥0∞)
      ≤ (P.totalDegree:ℝ≥0∞) := by
    exact_mod_cast polynomialLinearPullback_degree R.toContinuousLinearEquiv.toContinuousLinearMap P
  filter_upwards [ha] with y hy
  rw [frameCrossingCount_eq_coordinate]
  exact hy.trans hd

theorem frame_crossing_integral_le {n : ℕ} (P : MvPolynomial (Fin (n+1)) ℝ) (hP : P≠0)
    (R : EuclideanSpace ℝ (Fin (n+1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n+1))) (D : Set (Fin n→ℝ)) :
    (∫⁻ y in D, frameCrossingCount P R y) ≤ (P.totalDegree:ℝ≥0∞)*volume D := by
  have h := lintegral_mono_ae (ae_restrict_of_ae (s:=D) (ae_frame_crossing_count_le P hP R))
  simpa only [lintegral_const,Measure.restrict_apply_univ] using h

/-- Every unit direction admits actual orthogonal base coordinates with the
projection-count budget. No rotation or count bound is an extra premise. -/
theorem exists_direction_crossing_budget {n : ℕ}
    (P : MvPolynomial (Fin (n+1)) ℝ) (hP : P≠0)
    (u : EuclideanSpace ℝ (Fin (n+1))) (hu : ‖u‖=1) :
    ∃ R : EuclideanSpace ℝ (Fin (n+1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n+1)),
      R (EuclideanSpace.single 0 1)=u ∧
      (∀ y : Fin n→ℝ, inner ℝ (R (WithLp.toLp 2 (Fin.cons 0 y))) u=0) ∧
      ∀ D : Set (Fin n→ℝ),
        (∫⁻ y in D, ({t : ℝ | MvPolynomial.eval
          (R (WithLp.toLp 2 (Fin.cons 0 y))+t • u) P=0}:Set ℝ).encard.toENNReal)
        ≤ (P.totalDegree:ℝ≥0∞)*volume D := by
  obtain ⟨R,hR⟩ := exists_axis_isometry (0:Fin (n+1)) u hu
  refine ⟨R,hR,?_,?_⟩
  · intro y
    rw [←hR,R.inner_map_map]
    rw [EuclideanSpace.inner_single_right]
    change (1:ℝ)*0=0
    ring
  · intro D
    have he (y : Fin n→ℝ) (t : ℝ) :
        R (WithLp.toLp 2 (Fin.cons t y))=R (WithLp.toLp 2 (Fin.cons 0 y))+t • u := by
      have hv : (WithLp.toLp 2 (Fin.cons t y):EuclideanSpace ℝ (Fin (n+1)))=
          WithLp.toLp 2 (Fin.cons 0 y)+t • EuclideanSpace.single 0 1 := by
        ext i
        refine Fin.cases ?_ (fun j => ?_) i <;> simp
      rw [hv,map_add,map_smul,hR]
    have hec (y : Fin n→ℝ) : frameCrossingCount P R y=
        ({t : ℝ | MvPolynomial.eval (R (WithLp.toLp 2 (Fin.cons 0 y))+t • u) P=0}:Set ℝ).encard.toENNReal := by
      unfold frameCrossingCount
      congr 2
      ext t
      change (MvPolynomial.eval (R (WithLp.toLp 2 (Fin.cons t y))) P=0) ↔
        (MvPolynomial.eval (R (WithLp.toLp 2 (Fin.cons 0 y))+t • u) P=0)
      rw [he y t]
    have hh := frame_crossing_integral_le P hP R D
    simpa only [hec] using hh

end KakeyaTwoScale
#print axioms KakeyaTwoScale.polynomial_isometry_pullback_ne_zero
#print axioms KakeyaTwoScale.frameCrossingCount_eq_coordinate
#print axioms KakeyaTwoScale.ae_frame_crossing_count_le
#print axioms KakeyaTwoScale.frame_crossing_integral_le
#print axioms KakeyaTwoScale.exists_direction_crossing_budget
