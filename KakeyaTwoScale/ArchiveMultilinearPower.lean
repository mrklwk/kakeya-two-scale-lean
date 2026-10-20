module
public import KakeyaTwoScale.ActualArchiveMultilinear

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- Exact grain saving in the terminal multilinear estimate. In particular,
the denominator is G, not G^(k-1), after raising to the (k-1)st power. -/
theorem multilinear_grain_budget_power {k : ℕ} (hk : 2≤k)
    (θ H C G A : ℝ) (N : Fin k→ℝ)
    (hθ : 0≤θ) (hH : 0≤H) (_hC : 0≤C) (hG : 0<G) (hA : 0≤A)
    (hN : ∀j, 0≤N j)
    (h : θ^(1/((k-1:ℕ):ℝ))*H ≤ C*G*(∏j, A*N j/G)^(1/((k-1:ℕ):ℝ))) :
    θ*H^(k-1) ≤ C^(k-1)*A^k*(∏j, N j)/G := by
  have hk1 : k-1≠0 := by omega
  have hh := pow_le_pow_left₀ (mul_nonneg (Real.rpow_nonneg hθ _) hH) h (k-1)
  rw [mul_pow,mul_pow,mul_pow] at hh
  rw [one_div,Real.rpow_inv_natCast_pow hθ hk1,
    Real.rpow_inv_natCast_pow (Finset.prod_nonneg (fun j _ => div_nonneg (mul_nonneg hA (hN j)) hG.le)) hk1] at hh
  apply hh.trans_eq
  rw [Finset.prod_div_distrib,Finset.prod_mul_distrib,Finset.prod_const,Finset.prod_const,
    Finset.card_univ,Fintype.card_fin]
  have he : G^k=G^(k-1)*G := by rw [←pow_succ]; congr 1; omega
  rw [he]
  field_simp

end KakeyaTwoScale
#print axioms KakeyaTwoScale.multilinear_grain_budget_power
