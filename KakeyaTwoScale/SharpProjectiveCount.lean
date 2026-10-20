module
public import KakeyaTwoScale.ConcreteRootAmbient
public import KakeyaTwoScale.SpherePacking

@[expose] public section

noncomputable section
namespace KakeyaTwoScale

/-- The projective convention in the published contract implies sharp sphere
packing, with exponent d−1 in ambient dimension d=n+1. -/
theorem projective_direction_count_sharp (n : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ (N : ℕ) (u : Fin N → EuclideanSpace ℝ (Fin (n + 1))),
      (∀ j, ‖u j‖ = 1) →
      (∀ i j, i ≠ j → δ ≤ Real.arccos |inner ℝ (u i) (u j)|) →
      (N : ℝ) ≤ K * δ ^ (1 - (n + 1 : ℝ)) := by
  let K : ℝ := (2 * (n + 1 : ℝ) * 2 ^ n * 3 ^ n) * 2 ^ n
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro δ hδ hδ1 N u hu hsep
  have h := sphere_packing_bound n (by simp) Finset.univ u
    (show 0 < δ / 2 by positivity) (show δ / 2 ≤ 1 by linarith)
    (fun j _ => hu j)
    (fun i _ j _ hij => projective_separation_half_chord (u i) (u j) (hu i) (hu j) δ (hsep i j hij))
  simp only [Finset.card_univ, Fintype.card_fin, div_pow] at h
  have hmul : (N : ℝ) * δ ^ n ≤ K := by
    have hh := mul_le_mul_of_nonneg_right h (show 0 ≤ (2 : ℝ) ^ n by positivity)
    have he : (N : ℝ) * (δ ^ n / 2 ^ n) * 2 ^ n = N * δ ^ n := by field_simp
    rw [he] at hh
    exact hh
  have hdiv := (le_div_iff₀ (pow_pos hδ n)).mpr hmul
  have he : δ ^ (1 - (n + 1 : ℝ)) = (δ ^ n)⁻¹ := by
    rw [show 1 - (n + 1 : ℝ) = -(n : ℝ) by ring, Real.rpow_neg hδ.le, Real.rpow_natCast]
  simpa only [he, div_eq_mul_inv] using hdiv

end KakeyaTwoScale
#print axioms KakeyaTwoScale.projective_direction_count_sharp
