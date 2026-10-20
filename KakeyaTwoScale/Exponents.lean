module
public import Mathlib.Tactic

@[expose] public section

/-! Exact numerical endpoint of Lewko's September 10 two-scale argument.
No assertion here supplies the geometric or asymptotic hypotheses. -/
noncomputable section
namespace KakeyaTwoScale

 def a : ℝ := 373 / 625
 def theta : ℝ := 252 / 625
 def denominator : ℝ := 22 + a / theta
 def omega (n : ℝ) : ℝ := (n - 1) * theta
 def gamma (n k : ℝ) : ℝ := (n - 1) + (k - 1) * theta

 theorem theta_eq : theta = 1 - a := by norm_num [theta, a]
 theorem denominator_value : denominator = 5917 / 252 := by
  norm_num [denominator, a, theta]

 /-- Algebraic rearrangement of the exponent comparison, before any floor bound. -/
 theorem gain_iff (n k D : ℝ) :
    denominator * (n - D) ≤ 20 * omega n + gamma n k + (2*a-1)*(n-1) ↔
    1 + a*(n-1) + (3*omega n-gamma n k)/denominator ≤ D := by
  norm_num [denominator, omega, gamma, a, theta]
  constructor <;> intro h <;> linarith

 /-- The narrow branch gives a strict 0.597 n bound, conditional on the
 exponent inequality derived from the two-scale volume estimate. -/
 theorem narrow_endpoint (n k D : ℝ) (hn : 0 ≤ n) (hk : k ≤ n/2)
    (h : denominator * (n-D) ≤
      20*omega n + gamma n k + (2*a-1)*(n-1)) :
    (597/1000 : ℝ)*n < D := by
  norm_num [denominator, omega, gamma, a, theta] at h
  linarith

 /-- Isolates the arithmetic in Zahl's broad branch. The hypothesis on k
 is satisfied by floor(n/2), and is essential for the estimate for B. -/
 theorem broad_exponent (n k : ℝ) (hn : 0 < n)
    (hklo : (n-1)/2 ≤ k) (hkhi : k ≤ n/2) :
    (3/5 : ℝ)*n ≤ (n^2+k^2+n-k)/(2*n) - (k-1)/20 := by
  have hs := sq_nonneg (k - n/2)
  have hB : (5/8 : ℝ)*n ≤ (n^2+k^2+n-k)/(2*n) := by
    apply (le_div_iff₀ (by positivity)).2
    nlinarith
  linarith

 theorem endpoint_of_branches (n k D : ℝ) (hn : 0 ≤ n) (hk : k ≤ n/2)
    (h : (3/5 : ℝ)*n ≤ D ∨
      denominator*(n-D) ≤ 20*omega n+gamma n k+(2*a-1)*(n-1)) :
    (597/1000 : ℝ)*n ≤ D := by
  rcases h with h | h
  · linarith
  · exact le_of_lt (narrow_endpoint n k D hn hk h)

end KakeyaTwoScale

#print axioms KakeyaTwoScale.gain_iff
#print axioms KakeyaTwoScale.narrow_endpoint
#print axioms KakeyaTwoScale.broad_exponent
#print axioms KakeyaTwoScale.endpoint_of_branches
