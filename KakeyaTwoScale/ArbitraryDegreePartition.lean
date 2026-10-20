module
public import KakeyaTwoScale.PartitionComponentMass
public import Mathlib.Data.Nat.Log

@[expose] public section

open MeasureTheory
noncomputable section
namespace KakeyaTwoScale

/-- Choose a dyadic scale within an arbitrary integer budget, losing less
than a factor of two. This is unconditional arithmetic. -/
theorem exists_dyadic_degree_budget (A D : ℕ) (hA : 0 < A) (hD : A ≤ D) :
    ∃ t : ℕ, A*2^t ≤ D ∧ D < 2*A*2^t := by
  let q := D/A
  let t := Nat.log 2 q
  have hq : q ≠ 0 := Nat.ne_of_gt (Nat.div_pos hD hA)
  have hlo : 2^t ≤ q := Nat.pow_log_le_self 2 hq
  have hhi : q < 2^(t+1) := Nat.lt_pow_succ_log_self (by norm_num) q
  refine ⟨t,?_,?_⟩
  · exact (Nat.mul_le_mul_left A hlo).trans (Nat.mul_div_le D A)
  · calc
      D < A*(q+1) := Nat.lt_mul_div_succ D hA
      _ ≤ A*2^(t+1) := Nat.mul_le_mul_left A (by omega)
      _ = 2*A*2^t := by rw [pow_succ]; ring

/-- Conversion of the dyadic mass fraction to an arbitrary degree budget.
No geometric or topological estimate is assumed here. -/
theorem dyadic_partition_mass_conversion (n D t : ℕ) (hD : 0 < D)
    (hscale : D < 4*n^2*2^t) (M : ℝ) (hM : 0 ≤ M) :
    M/(2:ℝ)^(n*t) ≤ ((4*(n:ℝ)^2)/(D:ℝ))^n*M := by
  have hDr : (0:ℝ) < D := by exact_mod_cast hD
  have hs : (D:ℝ) ≤ 4*(n:ℝ)^2*(2:ℝ)^t := by exact_mod_cast hscale.le
  have hp : (0:ℝ) < (2:ℝ)^t := by positivity
  have hr : (1:ℝ)/(2:ℝ)^t ≤ (4*(n:ℝ)^2)/(D:ℝ) := by
    apply (div_le_div_iff₀ hp hDr).mpr
    simpa using hs
  have hpow : ((1:ℝ)/(2:ℝ)^t)^n ≤ ((4*(n:ℝ)^2)/(D:ℝ))^n := by
    gcongr
  calc
    M/(2:ℝ)^(n*t) = ((1:ℝ)/(2:ℝ)^t)^n*M := by
      rw [div_pow, one_pow, ← pow_mul]
      simp [div_eq_mul_inv, mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_right hpow hM

/-- Prescribed-degree ambient partitioning for every positive integer D.
Each actual complementary component has at most (4*n²/D)^n of the mass.
The higher-dimensional odd-sphere zero premise is unchanged and explicit. -/
theorem exists_degree_budget_component_partition_of_oddSphereZero
    (n : ℕ) (hn : 0 < n) (D : ℕ) (hD : 0 < D)
    (hBU : ∀ d M, M < (d+1)^n → BoxOddSphereZero n d M)
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : Integrable w) (hwn : ∀ x, 0 ≤ w x) :
    ∃ P : MvPolynomial (Fin n) ℝ, P ≠ 0 ∧ P.totalDegree ≤ D ∧
      volume {x : EuclideanSpace ℝ (Fin n) | MvPolynomial.eval (fun i => x i) P = 0} = 0 ∧
      ∀ x, MvPolynomial.eval (fun i => x i) P ≠ 0 →
        (∫ y in connectedComponentIn {y | MvPolynomial.eval (fun i => y i) P ≠ 0} x, w y)
          ≤ ((4*(n:ℝ)^2)/(D:ℝ))^n*(∫ y, w y) := by
  have hm : (0:ℝ) ≤ ∫ y, w y := integral_nonneg hwn
  by_cases hbig : 2*n^2 ≤ D
  · obtain ⟨t,htlo,hthi⟩ := exists_dyadic_degree_budget (2*n^2) D (by positivity) hbig
    obtain ⟨P,hP,hd,hnull,hcomp⟩ :=
      exists_dyadic_component_partition_of_oddSphereZero n hn t hBU w hw hwn
    refine ⟨P,hP,hd.trans htlo,hnull,fun x hx => (hcomp x hx).trans ?_⟩
    apply dyadic_partition_mass_conversion n D t hD _ _ hm
    nlinarith
  · refine ⟨1,one_ne_zero,by simp,polynomial_zero_volume_euclidean _ one_ne_zero,?_⟩
    intro x _
    have hr : (1:ℝ) ≤ 4*(n:ℝ)^2/(D:ℝ) := by
      apply (le_div_iff₀ (by exact_mod_cast hD)).mpr
      have hnat : D ≤ 4*n^2 := by omega
      simpa only [one_mul] using (show (D:ℝ) ≤ 4*(n:ℝ)^2 by exact_mod_cast hnat)
    have hpow : (1:ℝ) ≤ (4*(n:ℝ)^2/(D:ℝ))^n := one_le_pow₀ hr
    exact (setIntegral_le_integral hw (Filter.Eventually.of_forall hwn)).trans
      (by simpa using mul_le_mul_of_nonneg_right hpow hm)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.exists_dyadic_degree_budget
#print axioms KakeyaTwoScale.dyadic_partition_mass_conversion
#print axioms KakeyaTwoScale.exists_degree_budget_component_partition_of_oddSphereZero
