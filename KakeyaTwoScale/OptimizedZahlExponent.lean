module
public import KakeyaTwoScale.DegreeOptimization
public import KakeyaTwoScale.ZahlExponents

@[expose] public section

namespace KakeyaTwoScale

/-- The exact coefficient produced by the finite optimizer gives the same
multilinear exponent used by the existing two-scale geometric interface. -/
theorem optimized_exponent_matches_zahl {n m k : ℕ} (hn : 0 < n) (h : n=m+k) :
    (k:ℝ)+(m:ℝ)*(m+1)/(2*n) = zahlB n k := by
  have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hreal : (n:ℝ)=(m:ℝ)+k := by exact_mod_cast h
  have hd : (n:ℝ)-k=m := by linarith
  have hh := zahlB_sub_k n k hn'
  rw [hd] at hh
  linarith

end KakeyaTwoScale
#print axioms KakeyaTwoScale.optimized_exponent_matches_zahl
