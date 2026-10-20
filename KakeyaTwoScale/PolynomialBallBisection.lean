module
public import KakeyaTwoScale.BisectionScalarNormalization

@[expose] public section

open Set MeasureTheory Metric
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

theorem coordinateOpenBox_volume (N : ℕ) (b : ℝ) :
    volume (coordinateOpenBox N b) = (ENNReal.ofReal (2*b))^N := by
  change Measure.pi (fun _ : Fin N => (volume : Measure ℝ)) (univ.pi (fun _ => Ioo (-b) b)) = _
  rw [Measure.pi_pi]
  simp [Real.volume_Ioo,sub_neg_eq_add,two_mul]

/-- Complete robust unit-ball bisection-to-actual-area theorem. The positive
constant is selected by dimension before the polynomial and before every atlas.
Only actual strict-sign masses are hypotheses; repeated factors are allowed. -/
theorem polynomial_ball_bisection (n : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (P : MvPolynomial (Fin (n+1)) ℝ)
      (A : DisjointChartAtlas n {x | MvPolynomial.eval x P=0}),
      (2/5:ℝ)*volume.real (coordinateEuclideanBall (n+1) 1) ≤
        volume.real (coordinateEuclideanBall (n+1) 1 ∩ {x | 0 < MvPolynomial.eval x P}) →
      (2/5:ℝ)*volume.real (coordinateEuclideanBall (n+1) 1) ≤
        volume.real (coordinateEuclideanBall (n+1) 1 ∩ {x | MvPolynomial.eval x P < 0}) →
      ENNReal.ofReal c * volume (coordinateEuclideanBall (n+1) 1) ≤ coordinateAreaSum P A := by
  obtain ⟨α,b,ha,ha1,hb,hb1,hbudget,hpow⟩ := exists_bisection_scales (n+1) (by omega)
  let B := coordinateEuclideanBall (n+1) 1
  let I := coordinateEuclideanBall (n+1) α
  let V : ℝ≥0∞ := volume B
  let W : ℝ≥0∞ := volume (coordinateOpenBox (n+1) b)
  let M : ℝ := 2^(n+2)
  have hV : 0 < V := coordinateEuclideanBall_positive _ _ (by norm_num)
  have hVf : V ≠ ∞ := (coordinateEuclideanBall_finite _ _).ne
  have hW : 0 < W := by
    dsimp [W]; rw [coordinateOpenBox_volume]; positivity
  have hWf : W ≠ ∞ := by
    dsimp [W]; rw [coordinateOpenBox_volume]; finiteness
  have hWr : 0 < W.toReal := ENNReal.toReal_pos hW.ne' hWf
  have hM : 0 < M := by dsimp [M]; positivity
  have hMe : ENNReal.ofReal M = (2:ℝ≥0∞)^(n+2) := by simp [M,ENNReal.ofReal_pow]
  have hI : MeasurableSet I := (coordinateEuclideanBall_open _ _).measurableSet
  have hIB : I ⊆ B := fun x hx => ball_subset_ball ha1.le hx
  have hi : (9/10:ℝ)*volume.real B ≤ volume.real I := by
    change (9/10:ℝ)*V.toReal ≤ (volume (coordinateEuclideanBall (n+1) α)).toReal
    rw [coordinateEuclideanBall_scale _ _ ha,ENNReal.toReal_mul,ENNReal.toReal_ofReal (pow_nonneg ha.le _)]
    exact mul_le_mul_of_nonneg_right hpow.le ENNReal.toReal_nonneg
  refine ⟨(9/100:ℝ)*W.toReal/(2*M),by positivity,?_⟩
  intro P A hp hn
  let S0 := B ∩ {x | 0 < MvPolynomial.eval x P}
  let T0 := B ∩ {x | MvPolynomial.eval x P < 0}
  let S := S0 ∩ I
  let T := T0 ∩ I
  have hS : MeasurableSet S := ((coordinateEuclideanBall_open _ _).measurableSet.inter
    (isOpen_lt continuous_const P.continuous_eval).measurableSet).inter hI
  have hT : MeasurableSet T := ((coordinateEuclideanBall_open _ _).measurableSet.inter
    (isOpen_lt P.continuous_eval continuous_const).measurableSet).inter hI
  have hs : (3/10:ℝ)*V.toReal ≤ (volume S).toReal :=
    retained_mass_lower volume B I S0 hI hVf hIB inter_subset_left hp hi
  have ht : (3/10:ℝ)*V.toReal ≤ (volume T).toReal :=
    retained_mass_lower volume B I T0 hI hVf hIB inter_subset_left hn hi
  have hsV : volume S ≤ V := measure_mono (inter_subset_left.trans inter_subset_left)
  have htV : volume T ≤ V := measure_mono (inter_subset_left.trans inter_subset_left)
  have hass := bisection_weighted_area_assembly P A α b ha.le hb.le hbudget S T hS hT
    (fun _ hx => ⟨hx.2,hx.1.2⟩) (fun _ hx => ⟨hx.2,hx.1.2⟩)
  have hfinal : volume S * volume T * W ≤
      (volume T+volume S)*ENNReal.ofReal M*coordinateAreaSum P A := by
    calc
      _ ≤ _ := hass
      _ ≤ (volume T+volume S)*((2:ℝ≥0∞)^(n+2)*coordinateAreaSum P A) :=
        mul_le_mul le_rfl (weightedCoordinateArea_le P A α b ha1.le hb1) zero_le zero_le
      _ = _ := by rw [hMe,mul_assoc]
  exact bisection_scalar_normalization (volume S) (volume T) V W (coordinateAreaSum P A) M
    hV hVf hW hWf hM hsV htV hs ht hfinal

/-- Concrete area obtained from the previously constructed full polynomial atlas. -/
def polynomialBallCoordinateArea {n : ℕ} (P : MvPolynomial (Fin (n+1)) ℝ) (hP : P ≠ 0) : ℝ≥0∞ :=
  coordinateAreaSum P (polynomial_disjoint_chart_atlas P hP).some

/-- Dependency-closed bisection statement for the constructed actual polynomial
area: no atlas, count bound or geometric estimate is supplied by the caller. -/
theorem actual_polynomial_ball_bisection (n : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (P : MvPolynomial (Fin (n+1)) ℝ) (hP : P ≠ 0),
      (2/5:ℝ)*volume.real (coordinateEuclideanBall (n+1) 1) ≤
        volume.real (coordinateEuclideanBall (n+1) 1 ∩ {x | 0 < MvPolynomial.eval x P}) →
      (2/5:ℝ)*volume.real (coordinateEuclideanBall (n+1) 1) ≤
        volume.real (coordinateEuclideanBall (n+1) 1 ∩ {x | MvPolynomial.eval x P < 0}) →
      ENNReal.ofReal c * volume (coordinateEuclideanBall (n+1) 1) ≤ polynomialBallCoordinateArea P hP := by
  obtain ⟨c,hc,h⟩ := polynomial_ball_bisection n
  exact ⟨c,hc,fun P hP => h P (polynomial_disjoint_chart_atlas P hP).some⟩

end KakeyaTwoScale
#print axioms KakeyaTwoScale.coordinateOpenBox_volume
#print axioms KakeyaTwoScale.polynomial_ball_bisection
#print axioms KakeyaTwoScale.actual_polynomial_ball_bisection
