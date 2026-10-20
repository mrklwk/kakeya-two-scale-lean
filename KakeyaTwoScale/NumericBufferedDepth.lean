module
public import KakeyaTwoScale.ActualGrainStatistics

@[expose] public section

noncomputable section
namespace KakeyaTwoScale

/-- One fixed depth B+1 suffices whenever the original tuple count is at most
2^B. The proof includes the empty-mass case and every s≥2. -/
theorem buffered_log_depth_bound (B s : ℕ) (H : ℝ) (hs : 2≤s)
    (hH : 0≤H) (hbound : H≤(2:ℝ)^B) :
    Real.log H / (-Real.log ((2:ℝ)/2^s)) < (B+1:ℕ) := by
  have hlog : 0<Real.log 2 := Real.log_pos (by norm_num)
  have he : -Real.log ((2:ℝ)/2^s)=((s:ℝ)-1)*Real.log 2 := by
    rw [Real.log_div (by norm_num) (by positivity),Real.log_pow]
    ring
  have hs' : (2:ℝ)≤s := by exact_mod_cast hs
  have hd : 0< -Real.log ((2:ℝ)/2^s) := by rw [he]; exact mul_pos (by linarith) hlog
  have hden : Real.log 2≤ -Real.log ((2:ℝ)/2^s) := by rw [he]; nlinarith
  have hl : Real.log H≤(B:ℝ)*Real.log 2 := by
    rcases eq_or_lt_of_le hH with hzero | hpos
    · rw [←hzero,Real.log_zero]; positivity
    · have h := Real.log_le_log hpos hbound
      rwa [Real.log_pow] at h
  have hb : Real.log H / (-Real.log ((2:ℝ)/2^s)) ≤ (B:ℝ) :=
    (div_le_iff₀ hd).mpr (hl.trans (mul_le_mul_of_nonneg_left hden (Nat.cast_nonneg B)))
  exact hb.trans_lt (by exact_mod_cast Nat.lt_succ_self B)


/-- The contraction rate saves a factor s-1 in the stopping depth. This is
needed to keep orientation losses small as the partition scale grows. -/
theorem buffered_log_depth_sharp (B s : ℕ) (H : ℝ) (hs : 2≤s)
    (hH : 0≤H) (hbound : H≤(2:ℝ)^B) :
    Real.log H / (-Real.log ((2:ℝ)/2^s)) < (B/(s-1)+1:ℕ) := by
  have hlog : 0<Real.log 2 := Real.log_pos (by norm_num)
  have he : -Real.log ((2:ℝ)/2^s)=((s:ℝ)-1)*Real.log 2 := by
    rw [Real.log_div (by norm_num) (by positivity),Real.log_pow]
    ring
  have hs' : (2:ℝ)≤s := by exact_mod_cast hs
  have hd : 0< -Real.log ((2:ℝ)/2^s) := by
    rw [he]; exact mul_pos (by linarith) hlog
  have hl : Real.log H≤(B:ℝ)*Real.log 2 := by
    rcases eq_or_lt_of_le hH with hzero | hpos
    · rw [←hzero,Real.log_zero]; positivity
    · have h := Real.log_le_log hpos hbound
      rwa [Real.log_pow] at h
  have hn : B<(s-1)*(B/(s-1)+1) := Nat.lt_mul_div_succ B (by omega)
  have hn' : (B:ℝ)<((s:ℝ)-1)*(B/(s-1)+1:ℕ) := by
    have hh : (B:ℝ)<((s-1:ℕ):ℝ)*(B/(s-1)+1:ℕ) := by exact_mod_cast hn
    simpa only [Nat.cast_sub (by omega : 1≤s),Nat.cast_one] using hh
  apply (div_lt_iff₀ hd).mpr
  rw [he]
  nlinarith [mul_lt_mul_of_pos_right hn' hlog]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.buffered_log_depth_bound

#print axioms KakeyaTwoScale.buffered_log_depth_sharp
