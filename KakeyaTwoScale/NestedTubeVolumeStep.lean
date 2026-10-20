module
public import KakeyaTwoScale.NestedTubeSetGeometry
public import KakeyaTwoScale.PrescribedFatVolume

@[expose] public section

open Set Metric MeasureTheory
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- One step for the exact recursively constructed family. Joint format,
actual Fat volume, and actual thickness are all discharged internally. -/
theorem uniform_nestedTube_volume_step (n r e D : ℕ) (B kappa beta : ℝ)
    (hbeta : 0<beta) (i j : Fin r) (rest : List (Fin r)) :
    ∃ C : ℝ, 0<C ∧ ∀ (p : TubeRecursionParameter n r e→ℝ) (s : ℕ), s≤n+1 →
      ∀ Q : Fin s→MvPolynomial (Fin (n+1)) ℝ, (∀ k, (Q k).totalDegree≤D) →
      (∀ x, rectangularPolynomialMap Q x=0 → (fderiv ℝ (rectangularPolynomialMap Q) x).range=⊤) →
      nestedPolynomialZero D p i={x | rectangularPolynomialMap Q x=0} →
      0<p (Sum.inl .radius) → 1≤p (Sum.inr i) →
      beta*p (Sum.inl .radius)≤kappa*p (Sum.inl (.length j)) →
      1≤p (Sum.inr i)*beta →
      volume (nestedTubeSet D B kappa beta (j::rest) p)≠⊤ →
      volume (nestedTubeSet D B kappa beta (i::j::rest) p)≤
        ENNReal.ofReal (C*(p (Sum.inr i))^(n+1-s))*
          volume (nestedTubeSet D B kappa beta (j::rest) p) := by
  obtain ⟨C,hC,hstep⟩ := uniform_prescribedFat_polynomial_step (n+1) D
    (nestedTubeFamily (n := n) (e := e) D B kappa beta (j::rest))
    (nestedTubeFamily_sign n r e D B kappa beta (j::rest))
  let H := max 1 (2/beta)
  refine ⟨C*H^(n+1),by dsimp [H]; positivity,?_⟩
  intro p s hs Q hQ hreg hzero hrho ha hlen hscale hfinite
  let a := p (Sum.inr i)
  let rho := p (Sum.inl .radius)
  have ha0 : 0<a := lt_of_lt_of_le zero_lt_one ha
  have hh := hstep p s hs Q hQ hreg a (kappa*p (Sum.inl (.length j))) (beta*rho)
    (2*rho) ha (mul_pos hbeta hrho) hlen (by positivity) (by
      have hh := mul_le_mul_of_nonneg_right hscale hrho.le
      dsimp [a,rho]
      nlinarith) hfinite
  rw [nestedTubeSet_cons D B kappa beta p i j rest hrho,hzero]
  refine hh.trans ?_
  apply mul_le_mul _ le_rfl zero_le zero_le
  apply ENNReal.ofReal_le_ofReal
  have he : 2*rho/(a*(beta*rho))=(2/beta)/a := by field_simp [show rho≠0 from ne_of_gt hrho]
  have hcancel : ((2/beta)/a)^s*a^(n+1)=(2/beta)^s*a^(n+1-s) := by
    rw [show a^(n+1)=a^s*a^(n+1-s) by rw [← pow_add,Nat.add_sub_of_le hs],div_pow]
    field_simp
  have hp : (2/beta)^s≤H^(n+1) :=
    (pow_le_pow_left₀ (by positivity) (le_max_right _ _) s).trans
      (pow_le_pow_right₀ (le_max_left _ _) hs)
  calc
    C*(2*rho/(a*(beta*rho)))^s*a^(n+1) = C*((2/beta)^s*a^(n+1-s)) := by rw [he,mul_assoc,hcancel]
    _ ≤ C*(H^(n+1)*a^(n+1-s)) := by gcongr
    _ = _ := by ring

end KakeyaTwoScale
#print axioms KakeyaTwoScale.uniform_nestedTube_volume_step
