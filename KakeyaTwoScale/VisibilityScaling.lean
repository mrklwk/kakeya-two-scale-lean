module
public import KakeyaTwoScale.MollifiedTubeBudget

@[expose] public section

open Set MeasureTheory Metric
noncomputable section
namespace KakeyaTwoScale

/-- Finite positive targets admit one common visibility inflation. Zero
prescriptions impose no coercivity requirement. -/
theorem exists_visibility_inflation {J : ℕ} (m : Fin J → ℝ)
    (hm : ∀j, 0 ≤ m j) (H : ℝ) (hH : 0 ≤ H) :
    ∃lam : ℝ, 1 ≤ lam ∧ ∀j, 0 < m j → H < lam*m j := by
  let lam := 1+∑j, H/m j
  have hs : 0 ≤ ∑j, H/m j := Finset.sum_nonneg (fun j _ => div_nonneg hH (hm j))
  refine ⟨lam,by dsimp [lam]; linarith,?_⟩
  intro j hj
  have hh : H/m j ≤ ∑i, H/m i := Finset.single_le_sum
    (fun i _ => div_nonneg hH (hm i)) (Finset.mem_univ j)
  have hh' : H/m j < lam := by dsimp [lam]; linarith
  exact (div_lt_iff₀ hj).mp hh'

/-- Exact scalar comparison giving the ambient-minus-one visibility
threshold. It applies to the literal positive body volume. -/
theorem inflated_volume_below_direction_threshold {n : ℕ}
    (v C L lam m : ℝ) (hv : 0 ≤ v) (_hC : 0 ≤ C) (hL : 1 ≤ L) (hlam : 1 ≤ lam)
    (hupper : C ≤ L*lam) (_hm : 0 < m)
    (hlarge : ((n+1:ℕ):ℝ)^(n+1)*L^n < lam*m)
    (hvol : lam^(n+1)*m*v ≤ 1) :
    v  <  (1/((n+1:ℕ):ℝ))*(1/(((n+1:ℕ):ℝ)*max 1 C))^n := by
  let N : ℝ := (n+1:ℕ)
  let A : ℝ := max 1 C
  have hN : 0 < N := by dsimp [N]; positivity
  have hA : 0 < A := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hlam0 : 0 < lam := lt_of_lt_of_le zero_lt_one hlam
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hAL : A ≤ L*lam := max_le (by nlinarith) hupper
  have hp : A^n ≤ L^n*lam^n := by simpa only [mul_pow] using pow_le_pow_left₀ hA.le hAL n
  have hcoef : N^(n+1)*A^n < lam^(n+1)*m := by
    have hh := mul_lt_mul_of_pos_right hlarge (pow_pos hlam0 n)
    have hle := mul_le_mul_of_nonneg_left hp (pow_nonneg hN.le (n+1))
    dsimp [N] at hle ⊢
    rw [pow_succ lam n]
    nlinarith only [hh,hle]
  have hden : 0 < N^(n+1)*A^n := mul_pos (pow_pos hN _) (pow_pos hA _)
  have he : (1/N)*(1/(N*A))^n = 1/(N^(n+1)*A^n) := by
    rw [one_div_pow,mul_pow,pow_succ]
    field_simp
  change v < (1/N)*(1/(N*A))^n
  rw [he]
  apply (lt_div_iff₀ hden).mpr
  by_cases hv0 : v=0
  · simp [hv0]
  have hh := mul_lt_mul_of_pos_right hcoef (lt_of_le_of_ne hv (Ne.symm hv0))
  nlinarith only [hh,hvol]

/-- The visibility inflation cancels with exactly k directional factors and
N-k upper-bound factors. No residual prescription-dependent constant remains. -/
theorem visibility_wedge_inflation_cancel {N k : ℕ} (hk : k ≤ N)
    (w B v F C U lam m P Q : ℝ)
    (hB : 0 < B) (_hv : 0 ≤ v) (hF : 0 ≤ F) (hC : 0 ≤ C)
    (_hU : 0 ≤ U) (hlam : 0 < lam) (hm : 0 ≤ m) (hP : 0 ≤ P) (_hQ : 0 ≤ Q)
    (hw : w*B ≤ v*F*C^(N-k)*P)
    (hvol : lam^N*m*v ≤ 1) (hupper : C ≤ U*lam) (hprod : P=lam^k*Q) :
    w*m ≤ (F*U^(N-k)/B)*Q := by
  have hh := mul_le_mul_of_nonneg_right hw (mul_nonneg (pow_nonneg hlam.le N) hm)
  have hh' := mul_le_mul_of_nonneg_right hvol
    (show 0 ≤ F*C^(N-k)*P from by positivity)
  have hstep : (w*m*B)*lam^N ≤ F*C^(N-k)*P := by nlinarith only [hh,hh']
  have hstep' : F*C^(N-k)*P ≤ F*(U*lam)^(N-k)*P := by gcongr
  have he : F*(U*lam)^(N-k)*P=(F*U^(N-k)*Q)*lam^N := by
    rw [hprod,mul_pow]
    have hexp : lam^(N-k)*lam^k=lam^N := by rw [← pow_add]; congr 1; omega
    calc
      _ = (F*U^(N-k)*Q)*(lam^(N-k)*lam^k) := by ring
      _ = _ := by rw [hexp]
  rw [he] at hstep'
  have hf := (mul_le_mul_iff_left₀ (pow_pos hlam N)).mp (hstep.trans hstep')
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ hB).mpr hf

end KakeyaTwoScale
#print axioms KakeyaTwoScale.exists_visibility_inflation
#print axioms KakeyaTwoScale.inflated_volume_below_direction_threshold

#print axioms KakeyaTwoScale.visibility_wedge_inflation_cancel
