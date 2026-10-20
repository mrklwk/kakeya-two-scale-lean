module
public import KakeyaTwoScale.ProgressionEnergy

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical
open scoped BigOperators Pointwise

def inverseProgression (p m j : ℕ) [NeZero p] : Finset (ZMod p) :=
  (positiveFieldInterval p m).image (fun x => (j:ZMod p)⁻¹*x)

theorem finite_sum_mul_real (p : ℕ) [Fact p.Prime] (f : ZMod p → ℝ) (a : ZMod p) (ha : a ≠ 0) :
    ∑ x, f (a*x) = ∑ x, f x := by
  apply Fintype.sum_equiv (Equiv.mulLeft₀ a ha)
  intro x
  rfl

/-- Sumset Cauchy–Schwarz applied to the actual dilated cutoff. The product
form is valid before any positivity of the energy is inferred. -/
theorem progression_sumset_energy_lower (p m j : ℕ) [Fact p.Prime]
    (hm0 : 0 < m) (hj : (j:ZMod p) ≠ 0) (A : Finset (ZMod p))
    (ha : (p:ℝ)/(m:ℝ) ≤ (A.card:ℝ)) (D : ℝ) (hD : 0 < D)
    (ψ : ZMod p → ℝ) (hψ : ∀ x, 0 ≤ ψ x)
    (hsupp : ∀ x, x ∉ positiveFieldInterval p m → ψ x = 0)
    (hmass : (m:ℝ)/(2*D) ≤ ∑ x, ψ x) :
    1 ≤ ((A+inverseProgression p m j).card:ℝ)*
      (4*D^2*(p:ℝ)*progressionEnergy p A (fun x => (ψ x:ℂ)) j) := by
  have hp : 0 < (p:ℝ) := by exact_mod_cast NeZero.pos p
  have hm : 0 < (m:ℝ) := by exact_mod_cast hm0
  have hsum : 0 ≤ ∑ x, ψ x := Finset.sum_nonneg (fun x _ => hψ x)
  have hsupport (x : ZMod p) (hx : x ∉ inverseProgression p m j) :
      (ψ ((j:ZMod p)*x):ℂ) = 0 := by
    rw [hsupp]
    · rfl
    · intro h
      apply hx
      refine Finset.mem_image.mpr ⟨(j:ZMod p)*x,h,?_⟩
      field_simp
  have h := smoothed_sumset_energy_bound p A (inverseProgression p m j)
    (fun x => if x ∈ A then (1:ℂ) else 0) (fun x => (ψ ((j:ZMod p)*x):ℂ))
    (by intro x hx; simp [hx]) hsupport
  have hsumc : (∑ x : ZMod p, (ψ ((j:ZMod p)*x):ℂ)) = ((∑ x, ψ x : ℝ):ℂ) := by
    rw [← Complex.ofReal_sum,finite_sum_mul_real p ψ _ hj]
  rw [hsumc] at h
  simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hsum] at h
  have hsumA : ‖∑ x : ZMod p, if x ∈ A then (1:ℂ) else 0‖ = (A.card:ℝ) := by simp
  rw [hsumA] at h
  change (A.card:ℝ)^2*(∑ x, ψ x)^2 ≤
    ((A+inverseProgression p m j).card:ℝ)*(p:ℝ)^3*progressionEnergy p A (fun x => (ψ x:ℂ)) j at h
  have hprod : (p:ℝ)/(2*D) ≤ (A.card:ℝ)*(∑ x, ψ x) := by
    have hh := mul_le_mul ha hmass (by positivity : 0 ≤ (m:ℝ)/(2*D)) (Nat.cast_nonneg A.card : (0:ℝ) ≤ A.card)
    convert hh using 1
    field_simp
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ (p:ℝ)/(2*D)) hprod 2
  rw [mul_pow] at hsq
  have hlower := hsq.trans h
  have hc : 0 ≤ 4*D^2/(p:ℝ)^2 := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hlower hc
  convert hscaled using 1 <;> field_simp
  all_goals ring

end KakeyaTwoScale
#print axioms KakeyaTwoScale.finite_sum_mul_real
#print axioms KakeyaTwoScale.progression_sumset_energy_lower
