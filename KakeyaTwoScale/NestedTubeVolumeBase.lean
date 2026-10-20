module
public import KakeyaTwoScale.NestedTubeSetGeometry
public import KakeyaTwoScale.PolynomialNeighborhoodGrowth

@[expose] public section

open Set Metric MeasureTheory
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- The actual deepest recursive set has the required finite base volume. -/
theorem uniform_nestedTube_volume_base (n r e D : ℕ) (B kappa beta : ℝ) (hB : 0≤B) :
    ∃ C : ℝ, 0<C ∧ ∀ (p : TubeRecursionParameter n r e→ℝ) (i : Fin r) (s : ℕ), s≤n+1 →
      ∀ Q : Fin s→MvPolynomial (Fin (n+1)) ℝ, (∀ k, (Q k).totalDegree≤D) →
      (∀ x, rectangularPolynomialMap Q x=0 → (fderiv ℝ (rectangularPolynomialMap Q) x).range=⊤) →
      nestedPolynomialZero D p i={x | rectangularPolynomialMap Q x=0} →
      0<p (Sum.inl .radius) → 0<p (Sum.inl (.length i)) →
      p (Sum.inl .radius)≤p (Sum.inl (.length i))/4 →
      volume (nestedTubeSet D B kappa beta [i] p)≤
        ENNReal.ofReal (C*(p (Sum.inl .radius))^s*(p (Sum.inl (.length i)))^(n+1-s)) := by
  obtain ⟨C,hC,hgrowth⟩ := uniform_regular_polynomial_neighborhood_growth (n+1) D
  refine ⟨C*2^(n+1)*(B+2)^(n+1),by positivity,?_⟩
  intro p i s hs Q hQ hreg hzero hrho hL hscale
  rw [nestedTubeSet_singleton D B kappa beta p i hB hrho hL,hzero]
  have hh := hgrowth s hs Q hQ hreg (nestedCenter p) (2*p (Sum.inl .radius))
    ((B+2)*p (Sum.inl (.length i))) (by positivity) (by
      nlinarith [mul_nonneg hB hL.le])
  refine hh.trans (ENNReal.ofReal_le_ofReal ?_)
  have htwo : (2:ℝ)^s≤2^(n+1) := pow_le_pow_right₀ (by norm_num) hs
  have hBpow : (B+2)^(n+1-s)≤(B+2)^(n+1) := pow_le_pow_right₀ (by linarith) (Nat.sub_le _ _)
  calc
    _ = C*2^s*(B+2)^(n+1-s)*(p (Sum.inl .radius))^s*(p (Sum.inl (.length i)))^(n+1-s) := by
      rw [mul_pow,mul_pow]; ring
    _ ≤ _ := by gcongr

end KakeyaTwoScale
#print axioms KakeyaTwoScale.uniform_nestedTube_volume_base
