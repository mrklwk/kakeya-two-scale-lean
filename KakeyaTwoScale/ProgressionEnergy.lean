module
public import KakeyaTwoScale.CutoffSpectralBound
public import KakeyaTwoScale.SmoothedSumsetEnergy

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical
open scoped BigOperators

def progressionEnergy (p : ℕ) [NeZero p] (A : Finset (ZMod p)) (ψ : ZMod p → ℂ) (j : ℕ) : ℝ :=
  (p:ℝ)⁻¹*∑ x, ‖normalizedConvolution p (fun x => if x ∈ A then (1:ℂ) else 0)
    (fun x => ψ ((j:ZMod p)*x)) x‖^2

theorem progressionEnergy_nonneg (p : ℕ) [NeZero p] (A : Finset (ZMod p))
    (ψ : ZMod p → ℂ) (j : ℕ) : 0 ≤ progressionEnergy p A ψ j := by
  unfold progressionEnergy
  positivity

theorem progressionEnergy_spectral_sum (p : ℕ) [Fact p.Prime] (J : Finset ℕ)
    (hJ : ∀ j ∈ J, (j:ZMod p) ≠ 0) (A : Finset (ZMod p)) (ψ : ZMod p → ℂ) :
    ∑ j ∈ J, progressionEnergy p A ψ j =
      ∑ k : ZMod p, ‖normalizedFourier p (fun x => if x ∈ A then (1:ℂ) else 0) k‖^2*
        ∑ j ∈ J, ‖normalizedFourier p ψ ((j:ZMod p)⁻¹*k)‖^2 := by
  simp only [progressionEnergy,normalized_convolution_parseval]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [normalizedFourier_dilation p ψ _ (hJ j hj)]

/-- Full spectral energy bound, with the zero mode explicitly separated. -/
theorem progressionEnergy_sum_bound (p m U D E : ℕ) [Fact p.Prime]
    (J : Finset ℕ) (hJ : ∀ j ∈ J, (j:ZMod p) ≠ 0) (A : Finset (ZMod p))
    (C : ℝ) (hC : 0 ≤ C) (ψ : ZMod p → ℂ)
    (hdec : ∀ k, ‖normalizedFourier p ψ k‖ ≤ C*((m:ℝ)/(p:ℝ))/(1+frequencySize k*(m:ℝ)/(p:ℝ))^D)
    (hcount : ∀ k : ZMod p, k ≠ 0 → (smallFrequencyIndices p U J k).card ≤ E) :
    ∑ j ∈ J, progressionEnergy p A ψ j ≤
      (C*((m:ℝ)/(p:ℝ)))^2 *
        (((A.card:ℝ)/(p:ℝ))^2*(J.card:ℝ)+
          ((A.card:ℝ)/(p:ℝ))*((E:ℝ)+(J.card:ℝ)/(1+(U:ℝ)*(m:ℝ)/(p:ℝ))^(2*D))) := by
  let w := fun k => ‖normalizedFourier p (fun x => if x ∈ A then (1:ℂ) else 0) k‖^2
  let v := fun k => ∑ j ∈ J, ‖normalizedFourier p ψ ((j:ZMod p)⁻¹*k)‖^2
  let V := (C*((m:ℝ)/(p:ℝ)))^2
  let Q := V*((E:ℝ)+(J.card:ℝ)/(1+(U:ℝ)*(m:ℝ)/(p:ℝ))^(2*D))
  have hQ : 0 ≤ Q := by dsimp [Q,V]; positivity
  have hV : 0 ≤ V := sq_nonneg _
  have hw (k : ZMod p) : 0 ≤ w k := sq_nonneg _
  have hw0 : w 0 = ((A.card:ℝ)/(p:ℝ))^2 := by
    dsimp [w]
    rw [normalizedFourier_zero]
    simp [norm_inv,div_eq_mul_inv,mul_comm]
  have hv0 : v 0 ≤ (J.card:ℝ)*V := by
    have h := cutoff_fourier_sq_bound p m D C hC ψ hdec 0 (by norm_num) 0 (frequencySize_nonneg _)
    simp only [zero_mul,zero_div,add_zero,one_pow,div_one] at h
    dsimp [v]
    simpa only [mul_zero,Finset.sum_const,nsmul_eq_mul] using
      Finset.sum_le_sum (fun j (_ : j ∈ J) => h)
  have hrest : (∑ k ∈ (Finset.univ : Finset (ZMod p)).erase 0, w k*v k) ≤
      ((A.card:ℝ)/(p:ℝ))*Q := by
    calc
      _ ≤ ∑ k ∈ (Finset.univ : Finset (ZMod p)).erase 0, w k*Q := by
        apply Finset.sum_le_sum
        intro k hk
        apply mul_le_mul_of_nonneg_left _ (hw k)
        exact cutoff_dilation_spectral_bound p m U D E J C hC ψ hdec k
          (hcount k (Finset.mem_erase.mp hk).1)
      _ = (∑ k ∈ (Finset.univ : Finset (ZMod p)).erase 0, w k)*Q := by rw [Finset.sum_mul]
      _ ≤ (∑ k : ZMod p, w k)*Q := by
        apply mul_le_mul_of_nonneg_right _ hQ
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (fun k _ _ => hw k)
      _ = ((A.card:ℝ)/(p:ℝ))*Q := by rw [normalizedFourier_indicator_mass]
  rw [progressionEnergy_spectral_sum p J hJ A ψ]
  change (∑ k : ZMod p, w k*v k) ≤ _
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0:ZMod p))]
  have hz := mul_le_mul_of_nonneg_left hv0 (hw 0)
  rw [hw0] at hz ⊢
  calc
    _ ≤ ((A.card:ℝ)/(p:ℝ))*Q+((A.card:ℝ)/(p:ℝ))^2*((J.card:ℝ)*V) := add_le_add hrest hz
    _ = _ := by dsimp [Q,V]; ring

end KakeyaTwoScale
#print axioms KakeyaTwoScale.progressionEnergy_nonneg
#print axioms KakeyaTwoScale.progressionEnergy_spectral_sum
#print axioms KakeyaTwoScale.progressionEnergy_sum_bound
