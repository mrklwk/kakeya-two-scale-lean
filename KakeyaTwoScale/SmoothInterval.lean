module
public import KakeyaTwoScale.IntervalAverage

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical
open scoped BigOperators

/-- k+1 factors; the successor is a genuine finite average. -/
def smoothInterval (p q : ℕ) : ℕ → ZMod p → ℝ
  | 0 => intervalWeight p q
  | k+1 => intervalAverage p q (smoothInterval p q k)

theorem intervalAverage_support (p q r : ℕ) [NeZero p] (f : ZMod p → ℝ)
    (hf : ∀ x, x ∉ fieldInterval p r → f x = 0)
    (x : ZMod p) (hx : x ∉ fieldInterval p (q+r)) : intervalAverage p q f x = 0 := by
  unfold intervalAverage
  have hs : ∑ y ∈ fieldInterval p q, f (x-y) = 0 := by
    apply Finset.sum_eq_zero
    intro y hy
    apply hf
    intro hz
    obtain ⟨a,ha,hae⟩ := Finset.mem_image.mp hy
    obtain ⟨b,hb,hbe⟩ := Finset.mem_image.mp hz
    apply hx
    apply Finset.mem_image.mpr
    refine ⟨a+b,Finset.mem_range.mpr (by have := Finset.mem_range.mp ha; have := Finset.mem_range.mp hb; omega),?_⟩
    rw [Nat.cast_add,hae,hbe]
    ring
  rw [hs,mul_zero]

theorem smoothInterval_bounds (p q : ℕ) [NeZero p] (hq0 : 0 < q) (hq : q ≤ p) :
    ∀ k x, 0 ≤ smoothInterval p q k x ∧ smoothInterval p q k x ≤ 1 := by
  intro k
  induction k with
  | zero => intro x; simp only [smoothInterval,intervalWeight]; split_ifs <;> norm_num
  | succ k ih => exact intervalAverage_bounds p q hq0 hq _ ih

theorem smoothInterval_sum (p q : ℕ) [NeZero p] (hq0 : 0 < q) (hq : q ≤ p) :
    ∀ k, ∑ x, smoothInterval p q k x = (q:ℝ) := by
  intro k
  induction k with
  | zero => simp [smoothInterval,intervalWeight,fieldInterval_card p q hq]
  | succ k ih => rw [smoothInterval,intervalAverage_sum p q hq0 hq,ih]

theorem smoothInterval_support (p q : ℕ) [NeZero p] :
    ∀ k x, x ∉ fieldInterval p ((k+1)*q) → smoothInterval p q k x = 0 := by
  intro k
  induction k with
  | zero => intro x hx; simpa [smoothInterval,intervalWeight] using hx
  | succ k ih =>
      intro x hx
      apply intervalAverage_support p q ((k+1)*q) _ ih x
      simpa only [show q+(k+1)*q = (k+1+1)*q by ring] using hx

/-- Repeated averaging amplifies any one-factor Fourier ratio bound. -/
theorem smoothInterval_fourier_bound (p q : ℕ) [NeZero p] (hq0 : 0 < q)
    (k : ZMod p) (B : ℝ) (hB : 0 ≤ B)
    (hbase : ‖normalizedFourier p (fun x => (intervalWeight p q x:ℂ)) k‖ ≤ (q:ℝ)/(p:ℝ)*B) :
    ∀ d, ‖normalizedFourier p (fun x => (smoothInterval p q d x:ℂ)) k‖ ≤
      (q:ℝ)/(p:ℝ)*B^(d+1) := by
  have hp : 0 < (p:ℝ) := by exact_mod_cast NeZero.pos p
  have hq : 0 < (q:ℝ) := by exact_mod_cast hq0
  intro d
  induction d with
  | zero => simpa only [smoothInterval,zero_add,pow_one] using hbase
  | succ d ih =>
      simp only [smoothInterval,intervalAverage_fourier,norm_mul,norm_div,Complex.norm_natCast]
      have h := mul_le_mul
        (mul_le_mul_of_nonneg_left hbase (by positivity : 0 ≤ (p:ℝ)/(q:ℝ)))
        ih (norm_nonneg _) (by positivity : 0 ≤ (p:ℝ)/(q:ℝ)*((q:ℝ)/(p:ℝ)*B))
      refine h.trans_eq ?_
      simp only [pow_succ]
      field_simp

end KakeyaTwoScale
#print axioms KakeyaTwoScale.intervalAverage_support
#print axioms KakeyaTwoScale.smoothInterval_bounds
#print axioms KakeyaTwoScale.smoothInterval_sum
#print axioms KakeyaTwoScale.smoothInterval_support
#print axioms KakeyaTwoScale.smoothInterval_fourier_bound
