module
public import KakeyaTwoScale.OrthogonalPolynomialTransport
public import Mathlib.Algebra.MvPolynomial.Funext

@[expose] public section

open Set MvPolynomial
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- Literal substitution for the polynomial Q(b+B x), in coordinate functions. -/
def polynomialAffinePullback {N : ℕ}
    (B : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ)) (b : Fin N → ℝ)
    (Q : MvPolynomial (Fin N) ℝ) : MvPolynomial (Fin N) ℝ :=
  eval₂Hom C (fun i => C (b i) + ∑ j, C (B (Pi.single j 1) i) * X j) Q

theorem polynomialAffinePullback_eval {N : ℕ}
    (B : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ)) (b : Fin N → ℝ)
    (Q : MvPolynomial (Fin N) ℝ) (x : Fin N → ℝ) :
    eval x (polynomialAffinePullback B b Q) = eval (b+B x) Q := by
  have hx : ∑ j, x j • Pi.single j (1:ℝ) = x := by
    ext i
    simp [Pi.single_apply]
  have hcoord (i : Fin N) : (∑ j, B (Pi.single j 1) i * x j) = B x i := by
    have hh := congrArg (fun y => B y i) hx
    simpa [map_sum,map_smul,mul_comm] using hh
  change (eval₂Hom (RingHom.id ℝ) x)
    (Q.eval₂ C (fun i => C (b i) + ∑ j, C (B (Pi.single j 1) i) * X j)) = _
  rw [eval₂_comp_left]
  have hc : (eval₂Hom (RingHom.id ℝ) x).comp C = RingHom.id ℝ := by ext r; simp
  rw [hc]
  congr 1
  funext i
  simpa using congrArg (b i + ·) (hcoord i)

theorem polynomialAffinePullback_ne_zero {N : ℕ}
    (B : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ)) (b : Fin N → ℝ)
    (Q : MvPolynomial (Fin N) ℝ) (hQ : Q ≠ 0) :
    polynomialAffinePullback B b Q ≠ 0 := by
  intro h
  apply hQ
  apply MvPolynomial.funext
  intro y
  have he := polynomialAffinePullback_eval B b Q (B.symm (y-b))
  simpa [h] using he.symm

/-- Affine substitution preserves the degree budget. -/
theorem polynomialAffinePullback_degree {N : ℕ}
    (B : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ)) (b : Fin N → ℝ)
    (Q : MvPolynomial (Fin N) ℝ) :
    (polynomialAffinePullback B b Q).totalDegree ≤ Q.totalDegree := by
  let f : Fin N → MvPolynomial (Fin N) ℝ :=
    fun i => C (b i) + ∑ j, C (B (Pi.single j 1) i) * X j
  have hf (i) : (f i).totalDegree ≤ 1 := by
    apply (totalDegree_add _ _).trans
    apply max_le (by simp)
    apply totalDegree_finsetSum_le
    intro j _
    exact (totalDegree_mul _ _).trans (by simp)
  change (Q.eval₂ C f).totalDegree ≤ _
  rw [eval₂_eq]
  apply totalDegree_finsetSum_le
  intro s hs
  apply le_trans (totalDegree_mul _ _)
  simp only [totalDegree_C,zero_add]
  apply le_trans (totalDegree_finsetProd _ _)
  apply le_trans _ (le_totalDegree hs)
  apply Finset.sum_le_sum
  intro i _
  exact (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (s i) (hf i))

end KakeyaTwoScale
#print axioms KakeyaTwoScale.polynomialAffinePullback_eval
#print axioms KakeyaTwoScale.polynomialAffinePullback_ne_zero
#print axioms KakeyaTwoScale.polynomialAffinePullback_degree
