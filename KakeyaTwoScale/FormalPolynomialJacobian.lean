module
public import KakeyaTwoScale.RegularPolynomialFibers
public import Mathlib.Analysis.Calculus.Deriv.Pi

@[expose] public section

open MvPolynomial
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

theorem pderiv_totalDegree_le {σ : Type*} (P : MvPolynomial σ ℝ) (j : σ) :
    (pderiv j P).totalDegree ≤ P.totalDegree := by
  classical
  apply Finset.sup_le
  intro s hs
  have hc := MvPolynomial.mem_support_iff.mp hs
  rw [coeff_pderiv] at hc
  have hsp : s+Finsupp.single j 1 ∈ P.support :=
    MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hc)
  have hh := MvPolynomial.le_totalDegree hsp
  simp [Finsupp.sum_add_index] at hh
  omega

theorem polynomial_matrix_det_degree {σ : Type*} {n D : ℕ}
    (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℝ))
    (hM : ∀ i j, (M i j).totalDegree ≤ D) : M.det.totalDegree ≤ n*D := by
  rw [Matrix.det_apply]
  apply totalDegree_finsetSum_le
  intro s _
  apply (totalDegree_smul_le _ _).trans
  apply (totalDegree_finsetProd _ _).trans
  simpa using Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hM (s i) i)

def formalPolynomialJacobian {n : ℕ} (P : Fin n → MvPolynomial (Fin n) ℝ) :
    MvPolynomial (Fin n) ℝ := Matrix.det (fun i j => pderiv j (P i))

theorem formalPolynomialJacobian_degree {n D : ℕ} (P : Fin n → MvPolynomial (Fin n) ℝ)
    (hP : ∀ i, (P i).totalDegree ≤ D) : (formalPolynomialJacobian P).totalDegree ≤ n*D :=
  polynomial_matrix_det_degree _ (fun i j => (pderiv_totalDegree_le (P i) j).trans (hP i))

theorem polynomial_fderiv_coordinate {n : ℕ} (P : Fin n → MvPolynomial (Fin n) ℝ)
    (x : Fin n → ℝ) (i j : Fin n) :
    (fderiv ℝ (polynomialMapPi P) x) (Pi.single j 1) i = eval x (pderiv j (P i)) := by
  have hd := ((polynomialMapPi_contDiff P 1).differentiable (by norm_num) x).hasFDerivAt
  have hu := hasDerivAt_update x j (x j)
  have hd' : HasFDerivAt (polynomialMapPi P) (fderiv ℝ (polynomialMapPi P) x)
      (Function.update x j (x j)) := by simpa using hd
  have hc := hd'.comp_hasDerivAt (x j) hu
  have he := (ContinuousLinearMap.proj i).hasFDerivAt.comp_hasDerivAt (x j) hc
  have hp := polynomial_coordinate_hasDerivAt (P i) x j (x j)
  have he' : HasDerivAt (fun t => eval (Function.update x j t) (P i))
      ((fderiv ℝ (polynomialMapPi P) x) (Pi.single j 1) i) (x j) := by
    simpa [Function.comp_def,polynomialMapPi] using he
  exact he'.unique (by simpa using hp)

theorem formalPolynomialJacobian_eval {n : ℕ} (P : Fin n → MvPolynomial (Fin n) ℝ)
    (x : Fin n → ℝ) :
    eval x (formalPolynomialJacobian P) = LinearMap.det (fderiv ℝ (polynomialMapPi P) x).toLinearMap := by
  have hm := (eval x).map_det (fun i j : Fin n => pderiv j (P i))
  change eval x (Matrix.det (fun i j : Fin n => pderiv j (P i))) = _
  rw [hm]
  rw [← LinearMap.det_toMatrix']
  congr 1
  ext i j
  exact (polynomial_fderiv_coordinate P x i j).symm

end KakeyaTwoScale
#print axioms KakeyaTwoScale.pderiv_totalDegree_le
#print axioms KakeyaTwoScale.polynomial_matrix_det_degree
#print axioms KakeyaTwoScale.formalPolynomialJacobian_degree
#print axioms KakeyaTwoScale.polynomial_fderiv_coordinate
#print axioms KakeyaTwoScale.formalPolynomialJacobian_eval
