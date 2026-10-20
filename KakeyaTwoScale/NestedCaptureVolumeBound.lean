module
public import KakeyaTwoScale.UniversalNestedCaptureSweep
public import KakeyaTwoScale.NestedTubeVolumeTelescope

@[expose] public section

open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- The actual recursive target supplies the product-of-length upper bound for
all eligible directions. The unpadded equations carry the rank hypothesis;
padded capture equations are used only to define the eligible relation. -/
theorem uniform_nested_capture_volume_bound (n r e D : ℕ) (C : ℝ) (hC : 0≤C)
    (h : Fin (n+1)) (outer : Fin r) (rest : List (Fin r)) :
    ∃ K : ℝ, 0<K ∧ ∃ M : ℕ,
      ∀ (P : Fin r→Fin e→MvPolynomial (Fin (n+1)) ℝ),
      (∀ i j, (P i j).totalDegree≤D) →
      ∀ (center : EuclideanSpace ℝ (Fin (n+1))) (L A : Fin r→ℝ) (rho s ell : ℝ)
        (sigma : Fin r→ℕ) (Q : ∀ i, Fin (sigma i)→MvPolynomial (Fin (n+1)) ℝ),
      0<rho → 0<ell →
      (∀ i∈outer::rest, sigma i≤n+1 ∧ (∀ j, (Q i j).totalDegree≤D) ∧
        (∀ x, rectangularPolynomialMap (Q i) x=0 →
          (fderiv ℝ (rectangularPolynomialMap (Q i)) x).range=⊤) ∧
        captureZeroSet (P i)={x | rectangularPolynomialMap (Q i) x=0} ∧
        0<L i ∧ rho≤L i/4 ∧ recursionDilation n (C+4)≤A i) →
      (outer::rest).IsChain (fun i j => sigma j=sigma i+1 ∧ L j≤L i ∧
        A i=recursionDilation n (C+4)*L i/L j) →
      volume {v | ∃ a, universalEligibleLine D C h outer
        (captureParameters P center L rho s ell) v a} * ENNReal.ofReal (ell^(n+1)) ≤
        (ENNReal.ofReal (K*(rho^(sigma outer+rest.length)*L outer^(n+1-sigma outer)/
          (rest.map L).prod)))*M := by
  have hB : 0≤C+4 := by linarith
  obtain ⟨K,hK,M,hsweep⟩ := universal_nested_capture_sweep_volume n r e D C hC h outer rest
  obtain ⟨V,hV,hvol⟩ := uniform_nestedTube_volume_telescope n r e D (C+4)
    (recursionKappa n) (recursionBeta n) (recursionDilation n (C+4)) hB
    (recursionBeta_pos n) (recursionDilation_ge_one n (C+4) hB) outer rest
  refine ⟨K*V,mul_pos hK hV,M,?_⟩
  intro P hP center L A rho s ell sigma Q hrho hell hdata hchain
  have hscale : ∀ i∈outer::rest, 0<L i ∧ rho≤L i/4 :=
    fun i hi => ⟨(hdata i hi).2.2.2.2.1,(hdata i hi).2.2.2.2.2.1⟩
  have hc := hchain.imp (fun i j hh => hh.2)
  have hs := hsweep P hP center L A rho s ell hell hscale hc
  have hv := hvol (nestedRecursionParameters P center L A rho) sigma Q hrho (by
    intro i hi
    obtain ⟨hd,hdeg,hrank,hzero,hL,hrL,hA⟩ := hdata i hi
    have hcond := recursion_scale_conditions n (C+4) (L i) (L i) rho hB hL le_rfl hrho hrL
    refine ⟨hd,hdeg,hrank,?_,hL,hrL,hcond.2.1,?_,?_⟩
    · exact (nestedPolynomialZero_specialize D P hP center L A rho i).trans hzero
    · exact (recursionDilation_ge_one n (C+4) hB).trans hA
    · have hh := mul_le_mul_of_nonneg_right hA (recursionBeta_pos n).le
      rw [recursionDilation_beta] at hh
      change 1≤A i*recursionBeta n
      linarith) (hchain.imp (fun i j hh => ⟨hh.1,hh.2.2⟩))
  refine hs.trans ((mul_le_mul le_rfl hv zero_le zero_le).trans_eq ?_)
  simp only [nestedRecursionParameters,captureParameters,Sum.elim_inl]
  rw [show (K*V)*(rho^(sigma outer+rest.length)*L outer^(n+1-sigma outer)/(rest.map L).prod) =
    K*(V*(rho^(sigma outer+rest.length)*L outer^(n+1-sigma outer)/(rest.map L).prod)) by ring,
    ENNReal.ofReal_mul hK.le]
  ring

end KakeyaTwoScale
#print axioms KakeyaTwoScale.uniform_nested_capture_volume_bound
