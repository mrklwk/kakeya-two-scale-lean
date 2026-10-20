module
public import KakeyaTwoScale.VisibilityScaling

@[expose] public section

open Set MeasureTheory Metric
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

def prescribedCubeSeminorm (n D J : ℕ) (z : Fin J → Fin (n+1) → ℝ)
    (ε : ℝ) (c : FullCoefficientSphere (n+1) D) (j : Fin J) :
    Seminorm ℝ (EuclideanSpace ℝ (Fin (n+1))) :=
  mollifiedAreaSeminorm (fullDegreeFinMonomial (n+1) D)
    (fullDegreeFinMonomial_injective (n+1) D) (fullDegreeFinMonomial_degree (n+1) D)
    (visibilityCube (z j)) measurableSet_closedBall (Or.inr isClosed_closedBall)
    (cubeFamilyRadius z) (cubeFamilyRadius_nonneg z) (cubeFamilyRadius_bound z j) ε c

def localCubeAreaConstant (n : ℕ) : ℝ :=
  volume.real (closedBall (0 : Fin n → ℝ) (((n+1:ℕ):ℝ)/2))

theorem prescribedCubeSeminorm_continuous (n D J : ℕ) (z : Fin J → Fin (n+1) → ℝ)
    (ε : ℝ) (hε : 0 < ε) (hε2 : ε < 2) (c : FullCoefficientSphere (n+1) D) (j : Fin J) :
    Continuous (prescribedCubeSeminorm n D J z ε c j) := by
  have hh := (continuous_mollifiedArea_joint (fullDegreeFinMonomial (n+1) D)
    (fullDegreeFinMonomial_injective (n+1) D) (fullDegreeFinMonomial_degree (n+1) D)
    (visibilityCube (z j)) measurableSet_closedBall (Or.inr isClosed_closedBall)
    (cubeFamilyRadius z) (cubeFamilyRadius_nonneg z) (cubeFamilyRadius_bound z j) ε hε hε2).comp
    (show Continuous (fun v : EuclideanSpace ℝ (Fin (n+1)) => (c,v)) from
      continuous_const.prodMk continuous_id)
  exact hh

theorem prescribedCubeSeminorm_upper (n D J : ℕ) (z : Fin J → Fin (n+1) → ℝ)
    (ε : ℝ) (hε : 0 < ε) (c : FullCoefficientSphere (n+1) D) (j : Fin J)
    (v : EuclideanSpace ℝ (Fin (n+1))) :
    prescribedCubeSeminorm n D J z ε c j v ≤ localCubeAreaConstant n*(D:ℝ)*‖v‖ := by
  have hh := mollified_cube_area_bound (fullDegreeFinMonomial (n+1) D)
    (fullDegreeFinMonomial_injective (n+1) D) (fullDegreeFinMonomial_degree (n+1) D)
    (z j) (cubeFamilyRadius z) (cubeFamilyRadius_nonneg z) (cubeFamilyRadius_bound z j) ε hε c v
  simpa only [prescribedCubeSeminorm,ENNReal.toReal_mul,ENNReal.toReal_natCast,mul_comm,localCubeAreaConstant,Measure.real]
    using hh

/-- Prescribed visibility inflated once so that the actual mollified
seminorms dominate the Euclidean norm on every positive prescription.
The degree constant is fixed before the cubes and targets. -/
theorem inflated_prescribed_visibility (n : ℕ) :
    ∃Cdeg : ℝ, 0 < Cdeg ∧ ∀(J : ℕ) (z : Fin J → Fin (n+1) → ℝ)
      (m : Fin J → ℝ), (∀j, 0 ≤ m j) → (∑j, m j)=1 →
      ∃(D : ℕ) (lam ε : ℝ) (c : FullCoefficientSphere (n+1) D),
        1 ≤ lam ∧ (D:ℝ) ≤ Cdeg*lam ∧ 0 < ε ∧ ε < 2 ∧
        (∀j, lam^(n+1)*m j*volume.real
          (coordinateVisibilityBody (prescribedCubeSeminorm n D J z ε c j)) ≤ 1) ∧
        (∀j, 0 < m j → ∀v, ‖v‖ ≤ prescribedCubeSeminorm n D J z ε c j v) := by
  obtain ⟨K,hK,hpres⟩ := prescribed_cube_visibility n
  let Cdeg := K^(((n+1:ℕ):ℝ)⁻¹)
  have hCdeg : 0 < Cdeg := Real.rpow_pos_of_pos hK _
  refine ⟨Cdeg,hCdeg,?_⟩
  intro J z m hm hsum
  let U := localCubeAreaConstant n
  have hU : 0 ≤ U := measureReal_nonneg
  let L := max 1 (U*Cdeg)
  have hL : 1 ≤ L := le_max_left _ _
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  obtain ⟨lam,hlam,hlarge⟩ := exists_visibility_inflation m hm
    (((n+1:ℕ):ℝ)^(n+1)*L^n) (by positivity)
  have hlam0 : 0 < lam := lt_of_lt_of_le zero_lt_one hlam
  obtain ⟨D,hD,δ,hδ,hδ2,hall⟩ := hpres J z (fun j => lam^(n+1)*m j)
    (fun j => mul_nonneg (pow_nonneg hlam0.le _) (hm j))
    (cubeFamilyRadius z) (cubeFamilyRadius_nonneg z) (cubeFamilyRadius_bound z)
  rw [← Finset.mul_sum,hsum,mul_one] at hD
  have hdeg : (D:ℝ) ≤ Cdeg*lam := by
    have hh : (D:ℝ) ≤ (K*lam^(n+1))^(((n+1:ℕ):ℝ)⁻¹) := by
      apply (Real.le_rpow_inv_iff_of_pos (Nat.cast_nonneg D)
        (mul_nonneg hK.le (pow_nonneg hlam0.le _)) (by positivity)).mpr
      simpa only [Real.rpow_natCast] using hD
    rw [Real.mul_rpow hK.le (pow_nonneg hlam0.le _),
      Real.pow_rpow_inv_natCast hlam0.le (by omega : n+1≠0)] at hh
    exact hh
  obtain ⟨c,hvol⟩ := hall δ hδ le_rfl
  refine ⟨D,lam,δ,c,hlam,hdeg,hδ,hδ2,hvol,?_⟩
  intro j hj
  apply norm_le_seminorm_of_small_visibility_body _
    (prescribedCubeSeminorm_continuous n D J z δ hδ hδ2 c j)
    (U*(D:ℝ)) (mul_nonneg hU (Nat.cast_nonneg D))
    (prescribedCubeSeminorm_upper n D J z δ hδ c j)
  apply inflated_volume_below_direction_threshold _ _ L lam (m j) measureReal_nonneg
    (mul_nonneg hU (Nat.cast_nonneg D)) hL hlam ?_ hj (hlarge j hj) (hvol j)
  have hh := mul_le_mul_of_nonneg_left hdeg hU
  have hh' := mul_le_mul_of_nonneg_right (le_max_right 1 (U*Cdeg)) hlam0.le
  dsimp [L]
  nlinarith only [hh,hh']

end KakeyaTwoScale
#print axioms KakeyaTwoScale.prescribedCubeSeminorm_continuous
#print axioms KakeyaTwoScale.prescribedCubeSeminorm_upper
#print axioms KakeyaTwoScale.inflated_prescribed_visibility
