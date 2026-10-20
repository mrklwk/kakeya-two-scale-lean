module
public import KakeyaTwoScale.RetainedTupleGeometricIncidence
public import KakeyaTwoScale.ActualMassToLength

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- A common nonnegative factor passes exactly through the k-family geometric mean. -/
theorem geometric_mean_const_mul {k : ℕ} (hk : 0<k) (A : ℝ) (hA : 0≤A)
    (f : Fin k→ℝ) (hf : ∀ j, 0≤f j) :
    (∏ j, A*f j)^(1/(k:ℝ)) = A*(∏ j, f j)^(1/(k:ℝ)) := by
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [Real.mul_rpow (pow_nonneg hA _) (Finset.prod_nonneg (fun j _ => hf j))]
  rw [one_div, Real.pow_rpow_inv_natCast hA (Nat.ne_of_gt hk)]

/-- The full archived record upper budgets, including frozen families,
control the geometric mean without transferring any lower marginal count. -/
theorem geometric_mean_le_count_budget {k : ℕ} (hk : 0<k)
    (R N : Fin k→ℝ) (U P : ℝ) (hR : ∀ j, 0≤R j) (hN : ∀ j, 0≤N j)
    (hU : 0≤U) (hP : 0≤P) (hbound : ∀ j, R j≤U*(N j*P)) :
    (∏ j, R j)^(1/(k:ℝ)) ≤ U*P*(∏ j, N j)^(1/(k:ℝ)) := by
  have hprod : ∏ j, R j ≤ ∏ j, (U*P)*N j := by
    apply Finset.prod_le_prod₀ (fun j _ => hR j)
    intro j _
    exact (hbound j).trans_eq (by ring)
  exact (Real.rpow_le_rpow (Finset.prod_nonneg (fun j _ => hR j)) hprod
    (by positivity)).trans_eq (geometric_mean_const_mul hk (U*P) (mul_nonneg hU hP) N hN)

/-- Exact cancellation of the root tuple scale in the repaired bound.
There is no original-marginal density ratio: only the cap multiplier C remains. -/
theorem root_tuple_scale_cancel {k : ℕ} (hk : 0<k) {μ C p X Y : ℝ}
    (hμ : 0<μ) (hC : 0≤C)
    (h : X*(μ^k)^p ≤ Y*(C*μ^k)^(p-1/(k:ℝ))) :
    X*μ ≤ Y*C^(p-1/(k:ℝ)) := by
  have hb : 0<μ^k := pow_pos hμ _
  have hid : (μ^k)^p = μ*(μ^k)^(p-1/(k:ℝ)) := by
    calc
      _ = (μ^k)^(1/(k:ℝ))*(μ^k)^(p-1/(k:ℝ)) := by
        rw [←Real.rpow_add hb]
        congr 1
        ring
      _ = _ := by rw [one_div,Real.pow_rpow_inv_natCast hμ.le (Nat.ne_of_gt hk)]
  rw [hid, Real.mul_rpow hC hb.le] at h
  have hh : (X*μ)*(μ^k)^(p-1/(k:ℝ)) ≤
      (Y*C^(p-1/(k:ℝ)))*(μ^k)^(p-1/(k:ℝ)) := by
    simpa only [mul_assoc] using h
  exact (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hb _)).mp hh

/-- The repaired physical maximal-length estimate. It uses an upper cap on
actual tuple fibers, never the product of original marginal upper caps.
The same dimension-only incidence constant precedes all finite data. -/
theorem exists_actual_geometric_mass_to_length (n : ℕ) :
    ∃ B : ℕ, 0<B ∧ ∀ {k : ℕ} {T O : Type} [DecidableEq T] [DecidableEq O],
    ∀ (S : FrozenGeometryState n k T (Fin n→ℤ) O), S.tuples.Nonempty →
    ∀ (Y₀ : Finset T) (cube : T→Fin n→ℤ) (tube : T→Fin k→O)
      (cubes : Finset (Fin n→ℤ)) (δ : ℝ), 0<δ →
      S.Valid Y₀ cube tube (fun q => WithLp.ofLp ⁻¹' gridCell δ q) δ →
      (∀ y∈Y₀, cube y∈cubes) →
      (∀ y∈Y₀, ∀ z∈Y₀, cube y=cube z → tube y=tube z → y=z) →
      0<k → ∀ (p M : ℝ), 1/(k:ℝ)≤p → 0≤M →
      (∀ q∈cubes, (ParentLevel.capacity S.tuples cube q:ℝ)≤M) →
    ∀ Lmax : ℝ, (∀ j, S.length δ j≤Lmax) →
      tupleCubeMass S.tuples cube cubes p*δ ≤
        (B:ℝ)*M^(p-1/(k:ℝ))*Lmax*(∏ j, (S.count j:ℝ))^(1/(k:ℝ)) := by
  classical
  obtain ⟨B,hB,hphysical⟩ := exists_actual_marginal_incidence_bound n
  refine ⟨B,hB,?_⟩
  intro k T O _ _ S hS Y₀ cube tube cubes δ hδ hv hsupport hinj hk p M hp hM hcap Lmax hmax
  have hL : 0≤Lmax := by
    have hpL : 0≤S.length δ ⟨0,hk⟩ := by
      unfold FrozenGeometryState.length
      positivity
    exact hpL.trans (hmax ⟨0,hk⟩)
  let I : Fin k→ℝ := fun j => ∑ q∈cubes, ((retainedCubeMarginal S.tuples cube tube j q).card:ℝ)
  have hI (j) : 0≤I j := Finset.sum_nonneg (fun q _ => Nat.cast_nonneg _)
  have hbound (j) : I j≤((B:ℝ)*Lmax/δ)*(S.count j:ℝ) := by
    have hh := hphysical S Y₀ cube tube δ hδ hv cubes j
    apply hh.trans
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (hmax j) hδ.le)
        (Nat.cast_nonneg B)) (Nat.cast_nonneg (S.count j))
    simpa only [mul_div_assoc] using h
  have hprod : (∏ j, I j)^(1/(k:ℝ)) ≤
      ((B:ℝ)*Lmax/δ)*(∏ j, (S.count j:ℝ))^(1/(k:ℝ)) := by
    have hh := Real.rpow_le_rpow (Finset.prod_nonneg (s := Finset.univ) (fun j _ => hI j))
      (Finset.prod_le_prod₀ (fun j _ => hI j) (fun j _ => hbound j))
      (by positivity : 0≤1/(k:ℝ))
    exact hh.trans_eq (geometric_mean_const_mul hk _ (by positivity) _ (fun j => Nat.cast_nonneg _))
  have hmass := retained_tuple_mass_le_cap_geometric_incidence hk S.tuples hS cube cubes
    (fun y hy => hsupport y (hv.1 hy)) tube
    (fun y hy z hz he ho => hinj y (hv.1 hy) z (hv.1 hz) he ho) hp hM hcap
  have hcombine := hmass.trans (mul_le_mul_of_nonneg_left hprod (Real.rpow_nonneg hM _))
  have hh := mul_le_mul_of_nonneg_right hcombine hδ.le
  convert hh using 1
  field_simp

end KakeyaTwoScale
#print axioms KakeyaTwoScale.geometric_mean_const_mul
#print axioms KakeyaTwoScale.geometric_mean_le_count_budget
#print axioms KakeyaTwoScale.exists_actual_geometric_mass_to_length

#print axioms KakeyaTwoScale.root_tuple_scale_cancel
