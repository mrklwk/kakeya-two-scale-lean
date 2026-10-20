module
public import KakeyaTwoScale.FiniteNarrowTransfer
public import KakeyaTwoScale.BrushScale

@[expose] public section

noncomputable section
namespace KakeyaTwoScale

/-- Exact source-index and two-scale conversion: ambient dimension n+1,
broad tuple size k+2, selected plane rank k+1, delta=rho^20. -/
theorem finite_narrow_dyadic_scale (n k q : ℕ) :
    (dyadicRadius q)^n*((dyadicRadius q)^(k+1))^theta*
      (dyadicRadius (20*q)/dyadicRadius q)^((n:ℝ)*theta)*
      ((dyadicRadius q)^n)^a =
    Real.exp (-Real.log 2*transferExponent (n+1:ℕ) (k+2:ℕ)*q) := by
  have hr : dyadicRadius (20*q)/dyadicRadius q=Real.exp (-Real.log 2*19*q) := by
    rw [dyadicRadius,dyadicRadius,← Real.exp_sub]
    congr 1
    push_cast
    ring
  rw [hr,brush_dyadic_scale,dyadicRadius,←Real.exp_nat_mul,
    ←Real.exp_mul,←Real.exp_mul,←Real.exp_add,←Real.exp_add]
  congr 1
  norm_num [transferExponent,omega,gamma,a,theta]
  ring

end KakeyaTwoScale
#print axioms KakeyaTwoScale.finite_narrow_dyadic_scale
