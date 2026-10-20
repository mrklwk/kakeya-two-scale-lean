module
public import KakeyaTwoScale.ProgressionCounting

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical

def modelProgressionLength (p F : ℕ) : ℕ := Nat.ceil ((p:ℝ)/(F:ℝ))

theorem modelProgressionLength_bounds (p F : ℕ) (hp : 3 ≤ p) (hF : 2 ≤ F) (hFp : F ≤ p) :
    0 < modelProgressionLength p F ∧ modelProgressionLength p F < p ∧
    (p:ℝ)/(modelProgressionLength p F:ℝ) ≤ F ∧
    (p:ℝ)/(F:ℝ) ≤ modelProgressionLength p F ∧
    (modelProgressionLength p F:ℝ) ≤ 2*((p:ℝ)/(F:ℝ)) := by
  have hpr : 0 < (p:ℝ) := by exact_mod_cast (show 0 < p by omega)
  have hFr : 0 < (F:ℝ) := by exact_mod_cast (show 0 < F by omega)
  have hx : 1 ≤ (p:ℝ)/(F:ℝ) := (le_div_iff₀ hFr).mpr (by simpa using (show (F:ℝ) ≤ p by exact_mod_cast hFp))
  have hlo : (p:ℝ)/(F:ℝ) ≤ (modelProgressionLength p F:ℝ) := Nat.le_ceil _
  have hhi : (modelProgressionLength p F:ℝ) < (p:ℝ)/(F:ℝ)+1 := Nat.ceil_lt_add_one (by positivity)
  have hm : 0 < (modelProgressionLength p F:ℝ) := lt_of_lt_of_le (div_pos hpr hFr) hlo
  refine ⟨by exact_mod_cast hm,?_,?_,hlo,by linarith⟩
  · have htwo : (2:ℝ) ≤ F := by exact_mod_cast hF
    have hhalf : (p:ℝ)/(F:ℝ) ≤ (p:ℝ)/2 := div_le_div_of_nonneg_left hpr.le (by norm_num) htwo
    have hp3 : (3:ℝ) ≤ p := by exact_mod_cast hp
    have hlt : (modelProgressionLength p F:ℝ) < p := by linarith
    exact_mod_cast hlt
  · apply (div_le_iff₀ hm).mpr
    have h := (div_le_iff₀ hFr).mp hlo
    nlinarith

theorem modelProgressionLength_log_bounds (p F : ℕ) (hp : 3 ≤ p) (hF : 2 ≤ F) (hFp : F ≤ p) :
    Real.log (p:ℝ)-Real.log (F:ℝ) ≤ Real.log (modelProgressionLength p F:ℝ) ∧
    Real.log (modelProgressionLength p F:ℝ) ≤ Real.log (p:ℝ)-Real.log (F:ℝ)+Real.log 2 := by
  have h := modelProgressionLength_bounds p F hp hF hFp
  have hpr : 0 < (p:ℝ) := by exact_mod_cast (show 0 < p by omega)
  have hFr : 0 < (F:ℝ) := by exact_mod_cast (show 0 < F by omega)
  have hmr : 0 < (modelProgressionLength p F:ℝ) := by exact_mod_cast h.1
  constructor
  · have hh := Real.log_le_log (div_pos hpr hFr) h.2.2.2.1
    rwa [Real.log_div (ne_of_gt hpr) (ne_of_gt hFr)] at hh
  · have hh := Real.log_le_log hmr h.2.2.2.2
    rw [Real.log_mul (by norm_num) (ne_of_gt (div_pos hpr hFr)),
      Real.log_div (ne_of_gt hpr) (ne_of_gt hFr)] at hh
    linarith

theorem floor_ge_half (x : ℝ) (hx : 2 ≤ x) : x/2 ≤ (Nat.floor x:ℝ) := by
  have h := Nat.lt_floor_add_one x
  linarith

end KakeyaTwoScale
#print axioms KakeyaTwoScale.modelProgressionLength_bounds
#print axioms KakeyaTwoScale.modelProgressionLength_log_bounds
#print axioms KakeyaTwoScale.floor_ge_half
