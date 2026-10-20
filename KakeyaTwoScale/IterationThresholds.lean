module
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Tactic

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Filter
open scoped Topology

def iterationRho (M k : ℕ) : ℝ := 100*(1-(k:ℝ)/(M:ℝ))
def iterationLossExponent (M k : ℕ) : ℝ := -1/(M:ℝ)-(k:ℝ)/(M:ℝ)^2
def iterationEpsilon (N : ℝ) (M k : ℕ) : ℝ := N^(iterationLossExponent M k)
def iterationPopularity (N : ℝ) (M : ℕ) : ℕ := Nat.ceil (N^(100/(M:ℝ)))
def iterationFiberThreshold (N V : ℝ) (M k : ℕ) : ℕ := Nat.ceil (V*N^(iterationRho M k-2))
def iterationMassThreshold (N V : ℝ) (M k : ℕ) : ℕ := Nat.ceil (iterationEpsilon N M k*V)

theorem ceil_scale_bounds (x : ℝ) (hx : 1 ≤ x) : x ≤ (Nat.ceil x : ℝ) ∧ (Nat.ceil x : ℝ) ≤ 2*x := by
  exact ⟨Nat.le_ceil x, le_of_lt (lt_of_lt_of_le (Nat.ceil_lt_add_one (by linarith)) (by linarith))⟩

theorem iterationRho_endpoints (M : ℕ) (hM : 0 < M) :
    iterationRho M 0 = 100 ∧ iterationRho M M = 0 := by
  have hm : (M:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hM
  simp [iterationRho,hm]

theorem iterationRho_nonneg (M k : ℕ) (hM : 0 < M) (hk : k ≤ M) : 0 ≤ iterationRho M k := by
  have hm : (0:ℝ) < M := by exact_mod_cast hM
  have hk' : (k:ℝ) ≤ M := by exact_mod_cast hk
  have hdiv := (div_le_one hm).mpr hk'
  dsimp [iterationRho]
  linarith

theorem iterationEpsilon_step (N : ℝ) (M k : ℕ) (hN : 0 < N) :
    iterationEpsilon N M (k+1) = iterationEpsilon N M k * N^(-1/(M:ℝ)^2) := by
  rw [iterationEpsilon,iterationEpsilon,← Real.rpow_add hN]
  congr 1
  dsimp [iterationLossExponent]
  push_cast
  ring

theorem iterationLossExponent_bounds (M k : ℕ) (hM : 0 < M) (hk : k ≤ M) :
    -2/(M:ℝ) ≤ iterationLossExponent M k ∧ iterationLossExponent M k ≤ -1/(M:ℝ) := by
  have hm : (0:ℝ) < M := by exact_mod_cast hM
  have hk' : (k:ℝ) ≤ M := by exact_mod_cast hk
  have hid : (1/(M:ℝ))*(M:ℝ)^2 = M := by field_simp
  have hd : (k:ℝ)/(M:ℝ)^2 ≤ 1/(M:ℝ) := by
    apply (div_le_iff₀ (sq_pos_of_pos hm)).mpr
    rw [hid]
    exact hk'
  have hz : 0 ≤ (k:ℝ)/(M:ℝ)^2 := by positivity
  dsimp [iterationLossExponent]
  simp only [div_eq_mul_inv] at hd hz ⊢
  constructor <;> linarith

theorem popularity_relative_to_epsilon (N : ℝ) (M k : ℕ)
    (hN : 1 ≤ N) (hM : 0 < M) (hk : k ≤ M) :
    N^(-100/(M:ℝ)) ≤ iterationEpsilon N M k * N^(-98/(M:ℝ)) := by
  have he := Real.rpow_le_rpow_of_exponent_le hN (iterationLossExponent_bounds M k hM hk).1
  have hmul := mul_le_mul_of_nonneg_right he (Real.rpow_nonneg (by linarith : 0 ≤ N) (-98/(M:ℝ)))
  have hi : -100/(M:ℝ) = -2/(M:ℝ)+ -98/(M:ℝ) := by ring
  rw [hi,Real.rpow_add (by linarith : 0 < N)]
  exact hmul

/-- One threshold N0 works for EVERY level k≤M. This is the actual scale
gap that lets next-level deletion and popularity losses fit inside current
uniform mass. A and B may depend on the fixed finite slope families. -/
theorem eventually_refinement_loss_dominated (M : ℕ) (hM : 0 < M)
    (A B η : ℝ) (hB : 0 ≤ B) (hη : 0 < η) :
    ∀ᶠ N : ℝ in atTop, ∀ k ≤ M,
      A*iterationEpsilon N M (k+1)+B*N^(-100/(M:ℝ)) ≤ η*iterationEpsilon N M k := by
  have hm : (0:ℝ) < M := by exact_mod_cast hM
  have ht1 : Tendsto (fun N : ℝ => N^(-1/(M:ℝ)^2)) atTop (𝓝 0) := by
    simpa only [neg_div] using tendsto_rpow_neg_atTop (by positivity : 0 < 1/(M:ℝ)^2)
  have ht2 : Tendsto (fun N : ℝ => N^(-98/(M:ℝ))) atTop (𝓝 0) := by
    simpa only [neg_div] using tendsto_rpow_neg_atTop (by positivity : 0 < 98/(M:ℝ))
  have ht : Tendsto (fun N : ℝ => A*N^(-1/(M:ℝ)^2)+B*N^(-98/(M:ℝ))) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul ht1).add (tendsto_const_nhds.mul ht2)
  have hs := ht.eventually (gt_mem_nhds hη)
  filter_upwards [eventually_ge_atTop (1:ℝ),hs] with N hN hs
  intro k hk
  have hpop := mul_le_mul_of_nonneg_left (popularity_relative_to_epsilon N M k hN hM hk) hB
  rw [iterationEpsilon_step N M k (by linarith)]
  have hep : 0 ≤ iterationEpsilon N M k := Real.rpow_nonneg (by linarith) _
  have hh := mul_le_mul_of_nonneg_left hs.le hep
  nlinarith

/-- Explicit two-sided rounding bound for the popularity denominator. -/
theorem iterationPopularity_bounds (N : ℝ) (M : ℕ) (hN : 1 ≤ N) :
    N^(100/(M:ℝ)) ≤ (iterationPopularity N M : ℝ) ∧
      (iterationPopularity N M : ℝ) ≤ 2*N^(100/(M:ℝ)) := by
  exact ceil_scale_bounds _ (Real.one_le_rpow hN (by positivity))

theorem iterationPopularity_inverse (N : ℝ) (M : ℕ) (hN : 1 ≤ N) :
    0 < iterationPopularity N M ∧
      1/(iterationPopularity N M : ℝ) ≤ N^(-100/(M:ℝ)) := by
  have hp : 0 < N^(100/(M:ℝ)) := Real.rpow_pos_of_pos (by linarith) _
  constructor
  · exact Nat.ceil_pos.mpr hp
  · have h := one_div_le_one_div_of_le hp (Nat.le_ceil (N^(100/(M:ℝ))))
    rw [neg_div, Real.rpow_neg (by linarith : 0 ≤ N)]
    simpa only [iterationPopularity,one_div] using h

theorem iterationMassThreshold_bounds (N V : ℝ) (M k : ℕ)
    (h : 1 ≤ iterationEpsilon N M k*V) :
    iterationEpsilon N M k*V ≤ (iterationMassThreshold N V M k : ℝ) ∧
      (iterationMassThreshold N V M k : ℝ) ≤ 2*(iterationEpsilon N M k*V) :=
  ceil_scale_bounds _ h

theorem iterationFiberThreshold_bounds (N V : ℝ) (M k : ℕ)
    (h : 1 ≤ V*N^(iterationRho M k-2)) :
    V*N^(iterationRho M k-2) ≤ (iterationFiberThreshold N V M k : ℝ) ∧
      (iterationFiberThreshold N V M k : ℝ) ≤ 2*(V*N^(iterationRho M k-2)) :=
  ceil_scale_bounds _ h

end KakeyaTwoScale
#print axioms KakeyaTwoScale.ceil_scale_bounds
#print axioms KakeyaTwoScale.iterationRho_endpoints
#print axioms KakeyaTwoScale.iterationRho_nonneg
#print axioms KakeyaTwoScale.iterationEpsilon_step
#print axioms KakeyaTwoScale.iterationLossExponent_bounds
#print axioms KakeyaTwoScale.popularity_relative_to_epsilon
#print axioms KakeyaTwoScale.eventually_refinement_loss_dominated
#print axioms KakeyaTwoScale.iterationPopularity_bounds

#print axioms KakeyaTwoScale.iterationPopularity_inverse
#print axioms KakeyaTwoScale.iterationMassThreshold_bounds
#print axioms KakeyaTwoScale.iterationFiberThreshold_bounds
