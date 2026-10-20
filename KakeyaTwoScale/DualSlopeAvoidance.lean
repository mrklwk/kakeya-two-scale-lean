module
public import KakeyaTwoScale.DualSlope
public import Mathlib.Algebra.Polynomial.Roots

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical Polynomial
open scoped BigOperators

def dualDenPoly (a p s : ℚ) : ℚ[X] := (X-C s)+C a*(X-C p)
def dualNumPoly (a p s : ℚ) : ℚ[X] := -(X-C s)+C (a*s)*(X-C p)

@[simp] theorem dualDenPoly_eval (a p s r : ℚ) :
    (dualDenPoly a p s).eval r = dualDenominator a p s r := by
  simp [dualDenPoly, dualDenominator]
@[simp] theorem dualNumPoly_eval (a p s r : ℚ) :
    (dualNumPoly a p s).eval r = dualNumerator a p s r := by
  simp [dualNumPoly, dualNumerator]

theorem dualDenPoly_ne_zero (a p s : ℚ) (hps : p ≠ s) : dualDenPoly a p s ≠ 0 := by
  intro h
  have he := congrArg (Polynomial.eval p) h
  simp [dualDenominator, sub_ne_zero.mpr hps] at he

theorem dualFixedPoly_ne_zero (a p s : ℚ) (hps : p ≠ s) (hp : p ≠ -1) :
    X*dualDenPoly a p s-dualNumPoly a p s ≠ 0 := by
  intro h
  have he := congrArg (Polynomial.eval p) h
  simp [dualDenominator, dualNumerator] at he
  have hz : (p+1)*(p-s)=0 := by nlinarith
  have hp1 : p+1 ≠ 0 := by intro h; apply hp; linarith
  exact mul_ne_zero hp1 (sub_ne_zero.mpr hps) hz

theorem dualValuePoly_ne_zero (a p s y : ℚ) (ha : a ≠ 0) (hps : p ≠ s)
    (hs : s ≠ -1) : dualNumPoly a p s-C y*dualDenPoly a p s ≠ 0 := by
  intro h
  by_cases hy : y = -1
  · subst y
    have he := congrArg (Polynomial.eval s) h
    simp [dualDenominator, dualNumerator] at he
    have hz : a*(s-p)*(s+1)=0 := by nlinarith
    have hs1 : s+1 ≠ 0 := by intro h; apply hs; linarith
    exact mul_ne_zero (mul_ne_zero ha (sub_ne_zero.mpr hps.symm)) hs1 hz
  · have he := congrArg (Polynomial.eval p) h
    simp [dualDenominator, dualNumerator] at he
    have hz : (y+1)*(p-s)=0 := by nlinarith
    have hy1 : y+1 ≠ 0 := by intro h; apply hy; linarith
    exact mul_ne_zero hy1 (sub_ne_zero.mpr hps) hz

/-- Rational slopes and their duals can avoid ANY prescribed finite set,
while avoiding the pole, the vertical slope and each other. All exceptional
values are excluded by a nonzero polynomial over the infinite field Q. -/
theorem finite_dual_slope_exceptions (a p s : ℚ) (ha : a ≠ 0) (hps : p ≠ s)
    (hp : p ≠ -1) (hs : s ≠ -1) (F : Finset ℚ) :
    ∃ bad : Finset ℚ, ∀ r ∉ bad, r ∉ F ∧ r ≠ p ∧ r ≠ s ∧ r ≠ -1 ∧
      dualDenominator a p s r ≠ 0 ∧ dualSlope a p s r ∉ F ∧
      dualSlope a p s r ≠ r ∧ dualSlope a p s r ≠ -1 ∧ dualSlope a p s r ≠ s := by
  let E := insert p (insert s (insert (-1) F))
  let D := dualDenPoly a p s
  let U := dualNumPoly a p s
  let P := D*(X*D-U)*(∏ y ∈ E, (U-C y*D))*(∏ y ∈ E, (X-C y))
  have hD : D ≠ 0 := dualDenPoly_ne_zero a p s hps
  have hfix : X*D-U ≠ 0 := dualFixedPoly_ne_zero a p s hps hp
  have hval : (∏ y ∈ E, (U-C y*D)) ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun y _ => dualValuePoly_ne_zero a p s y ha hps hs)
  have hlin : (∏ y ∈ E, (X-C y)) ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun y _ => Polynomial.X_sub_C_ne_zero y)
  have hP : P ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero hD hfix) hval) hlin
  let finiteRoots := Polynomial.finite_setOfPred_isRoot hP
  refine ⟨finiteRoots.toFinset,?_⟩
  intro r hr
  have heval : P.eval r ≠ 0 := by simpa only [Set.Finite.mem_toFinset, Polynomial.IsRoot, Set.mem_ofPred_eq] using hr
  dsimp [P] at heval
  rw [Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_mul] at heval
  obtain ⟨⟨⟨hd,hfixed⟩,hvalues⟩,hlinear⟩ :=
    (mul_ne_zero_iff.mp heval).imp_left (fun h =>
      (mul_ne_zero_iff.mp h).imp_left (fun h => mul_ne_zero_iff.mp h))
  have hnotE : r ∉ E := by
    intro hmem
    rw [Polynomial.eval_prod] at hlinear
    have ht := Finset.prod_ne_zero_iff.mp hlinear r hmem
    simp at ht
  have hnot : r ∉ F ∧ r ≠ p ∧ r ≠ s ∧ r ≠ -1 := by
    simpa [E, and_comm, and_left_comm, and_assoc] using hnotE
  have hdr : dualDenominator a p s r ≠ 0 := by simpa [D] using hd
  have hdualE : dualSlope a p s r ∉ E := by
    intro hmem
    rw [Polynomial.eval_prod] at hvalues
    have ht := Finset.prod_ne_zero_iff.mp hvalues (dualSlope a p s r) hmem
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C] at ht
    apply ht
    dsimp [U,D]
    rw [dualNumPoly_eval,dualDenPoly_eval]
    exact sub_eq_zero.mpr ((div_eq_iff hdr).mp (rfl : dualSlope a p s r = dualSlope a p s r))
  have hdualF : dualSlope a p s r ∉ F := by
    intro hmem
    exact hdualE (by simp [E,hmem])
  have hne : dualSlope a p s r ≠ r := by
    intro he
    have ht := (div_eq_iff hdr).mp he
    apply hfixed
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X]
    dsimp [D,U]
    rw [dualDenPoly_eval,dualNumPoly_eval]
    exact sub_eq_zero.mpr ht.symm
  exact ⟨hnot.1,hnot.2.1,hnot.2.2.1,hnot.2.2.2,hdr,hdualF,hne,
    dualSlope_proper a p s r ha hs hnot.2.1 hdr,
    dualSlope_ne_vertical a p s r hs hnot.2.2.1 hdr⟩

theorem exists_dual_slope_avoiding (a p s : ℚ) (ha : a ≠ 0) (hps : p ≠ s)
    (hp : p ≠ -1) (hs : s ≠ -1) (F : Finset ℚ) :
    ∃ r : ℚ, r ∉ F ∧ r ≠ p ∧ r ≠ s ∧ r ≠ -1 ∧
      dualDenominator a p s r ≠ 0 ∧ dualSlope a p s r ∉ F ∧
      dualSlope a p s r ≠ r ∧ dualSlope a p s r ≠ -1 ∧ dualSlope a p s r ≠ s := by
  obtain ⟨bad,hbad⟩ := finite_dual_slope_exceptions a p s ha hps hp hs F
  obtain ⟨r,hr⟩ := Infinite.exists_notMem_finset bad
  exact ⟨r,hbad r hr⟩

end KakeyaTwoScale
#print axioms KakeyaTwoScale.dualDenPoly_eval
#print axioms KakeyaTwoScale.dualNumPoly_eval
#print axioms KakeyaTwoScale.dualDenPoly_ne_zero
#print axioms KakeyaTwoScale.dualFixedPoly_ne_zero
#print axioms KakeyaTwoScale.dualValuePoly_ne_zero
#print axioms KakeyaTwoScale.exists_dual_slope_avoiding

#print axioms KakeyaTwoScale.finite_dual_slope_exceptions
