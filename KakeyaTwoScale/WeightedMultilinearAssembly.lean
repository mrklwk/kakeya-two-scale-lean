module
public import KakeyaTwoScale.ActualMultilinearFactors
public import KakeyaTwoScale.ShortComponentTerminal

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- Finite Holder with zero family budgets included. -/
theorem finite_geometric_holder {Q : Type*} [Fintype Q] {k : ℕ} (hk : 0<k)
    (b : Fin k → Q → ℝ) (T : Fin k → ℝ)
    (hb : ∀j q, 0≤b j q) (hT : ∀j, 0≤T j)
    (hsum : ∀j, (∑q, b j q)≤T j) :
    (∑q, (∏j, b j q)^(1/(k:ℝ)))≤(∏j, T j)^(1/(k:ℝ)) := by
  classical
  by_cases hp : ∀j, 0<T j
  · exact sum_product_rpow_le_of_family_sums Finset.univ hk b T hb hp hsum le_rfl
  push Not at hp
  obtain ⟨j,hj⟩ := hp
  have hz : T j=0 := le_antisymm hj (hT j)
  have hzero (q : Q) : b j q=0 := by
    have hh := (Finset.single_le_sum (fun q _ => hb j q) (Finset.mem_univ q)).trans (hsum j)
    exact le_antisymm (hh.trans_eq hz) (hb j q)
  have hprod (q : Q) : (∏i, b i q)=0 := Finset.prod_eq_zero (Finset.mem_univ j) (hzero q)
  simp only [hprod,Real.zero_rpow (by positivity : 1/(k:ℝ)≠0),Finset.sum_const_zero]
  exact Real.rpow_nonneg (Finset.prod_nonneg (fun j _ => hT j)) _

/-- The normalized variational step in the weighted multilinear proof. It
includes zero masses and has the exact exponent 1/(k-1). -/
theorem finite_multilinear_variational_bound {J k : ℕ} (hk : 2≤k)
    (F : Fin J → ℝ) (hF : ∀q, 0≤F q) (A : ℝ) (hA : 0≤A)
    (T : Fin k → ℝ) (hT : ∀j, 0≤T j)
    (hfactor : ∀m : Fin J → ℝ, (∀q, 0 ≤ m q) → (∑q, m q)=1 →
      ∃b : Fin k → Fin J → ℝ, (∀j q, 0≤b j q) ∧
        (∀q, F q*m q≤A*∏j, b j q) ∧ (∀j, (∑q, b j q)≤T j)) :
    (∑q, (F q)^(1/((k-1:ℕ):ℝ)))≤(A*∏j, T j)^(1/((k-1:ℕ):ℝ)) := by
  classical
  have hk0 : 0<k := by omega
  have hk1 : 0<k-1 := by omega
  let G := fun q => (F q)^(1/((k-1:ℕ):ℝ))
  let H := ∑q, G q
  have hG (q) : 0≤G q := Real.rpow_nonneg (hF q) _
  have hH : 0≤H := Finset.sum_nonneg (fun q _ => hG q)
  change H≤_
  by_cases hHz : H=0
  · rw [hHz]
    exact Real.rpow_nonneg (mul_nonneg hA (Finset.prod_nonneg (fun j _ => hT j))) _
  have hH0 : 0<H := lt_of_le_of_ne hH (Ne.symm hHz)
  let m := fun q => G q/H
  have hm (q) : 0 ≤ m q := div_nonneg (hG q) hH
  have hmsum : (∑q, m q)=1 := by
    dsimp [m]
    rw [← Finset.sum_div]
    exact div_self hHz
  obtain ⟨b,hb,hpoint,hsum⟩ := hfactor m hm hmsum
  have hpT : 0≤∏j, T j := Finset.prod_nonneg (fun j _ => hT j)
  have hpow (q) : (G q)^(k-1)=F q := by
    simpa only [G,one_div] using Real.rpow_inv_natCast_pow (hF q) (Nat.ne_of_gt hk1)
  have he (q) : (F q*m q)^(1/(k:ℝ))=G q/H^(1/(k:ℝ)) := by
    have halg : F q*m q=(G q)^k/H := by
      have heq : (G q)^k=(G q)^(k-1)*G q := by rw [← pow_succ]; congr 1; omega
      rw [heq,← hpow q]
      dsimp [m]
      ring
    rw [halg,Real.div_rpow (pow_nonneg (hG q) k) hH,one_div,
      Real.pow_rpow_inv_natCast (hG q) (Nat.ne_of_gt hk0)]
  have hh : H/H^(1/(k:ℝ))≤A^(1/(k:ℝ))*(∏j, T j)^(1/(k:ℝ)) := by
    calc
      _ = ∑q, (F q*m q)^(1/(k:ℝ)) := by simp_rw [he]; rw [← Finset.sum_div]
      _ ≤ ∑q, (A*∏j, b j q)^(1/(k:ℝ)) := Finset.sum_le_sum (fun q _ =>
        Real.rpow_le_rpow (mul_nonneg (hF q) (hm q)) (hpoint q) (by positivity))
      _ = A^(1/(k:ℝ))*(∑q, (∏j, b j q)^(1/(k:ℝ))) := by
        simp_rw [Real.mul_rpow hA (Finset.prod_nonneg (fun j _ => hb j _))]
        rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (finite_geometric_holder hk0 b T hb hT hsum)
        (Real.rpow_nonneg hA _)
  have hroot : H≤(A*(∏j, T j)*H)^(1/(k:ℝ)) := by
    rw [Real.mul_rpow (mul_nonneg hA hpT) hH,Real.mul_rpow hA hpT]
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hH0 _)).mp hh
  have hkR : 0<(k:ℝ) := Nat.cast_pos.mpr hk0
  rw [one_div] at hroot
  have hp := (Real.le_rpow_inv_iff_of_pos hH (mul_nonneg (mul_nonneg hA hpT) hH) hkR).mp hroot
  rw [Real.rpow_natCast] at hp
  have hpower : H^(k-1)≤A*(∏j, T j) := by
    have heq : H^k=H^(k-1)*H := by rw [← pow_succ]; congr 1; omega
    rw [heq] at hp
    exact (mul_le_mul_iff_left₀ hH0).mp hp
  rw [one_div]
  apply (Real.le_rpow_inv_iff_of_pos hH (mul_nonneg hA hpT) (Nat.cast_pos.mpr hk1)).mpr
  simpa only [Real.rpow_natCast] using hpower

end KakeyaTwoScale
#print axioms KakeyaTwoScale.finite_geometric_holder
#print axioms KakeyaTwoScale.finite_multilinear_variational_bound
