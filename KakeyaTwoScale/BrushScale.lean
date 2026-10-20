module
public import KakeyaTwoScale.ActualWeightedBrush
public import KakeyaTwoScale.UniformTransfer

@[expose] public section

noncomputable section
namespace KakeyaTwoScale

/-- Exact source exponent after converting the brush's natural-number
ambient/base-plane indexing and its dyadic power factors. -/
theorem brush_dyadic_scale (n k q : ℕ) :
    (dyadicRadius q)^n*((dyadicRadius q)^(k+1))^theta =
      Real.exp (-Real.log 2*gamma (n+1:ℕ) (k+2:ℕ)*q) := by
  rw [dyadicRadius,← Real.exp_nat_mul,← Real.exp_nat_mul,← Real.exp_mul,← Real.exp_add]
  congr 1
  simp only [gamma,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
  ring

end KakeyaTwoScale
#print axioms KakeyaTwoScale.brush_dyadic_scale
