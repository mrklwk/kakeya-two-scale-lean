module
public import KakeyaTwoScale.FourierTranslation
public import KakeyaTwoScale.SmoothInterval

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical
open scoped BigOperators

def positiveFieldInterval (p m : ℕ) : Finset (ZMod p) :=
  (Finset.Icc 1 m).image (fun i : ℕ => (i:ZMod p))

theorem translate_interval_support (p r m : ℕ) [NeZero p] (hrm : r ≤ m)
    (f : ZMod p → ℝ) (hf : ∀ x, x ∉ fieldInterval p r → f x = 0)
    (x : ZMod p) (hx : x ∉ positiveFieldInterval p m) : f (x-1) = 0 := by
  apply hf
  intro h
  obtain ⟨a,ha,he⟩ := Finset.mem_image.mp h
  apply hx
  apply Finset.mem_image.mpr
  refine ⟨a+1,Finset.mem_Icc.mpr ⟨by omega,by have := Finset.mem_range.mp ha; omega⟩,?_⟩
  rw [Nat.cast_add,Nat.cast_one,he]
  ring

theorem floor_cutoff_parameters (m d : ℕ) (hm : 2*(d+1) ≤ m) :
    0 < m/(d+1) ∧ m/(d+1) ≤ m ∧ (d+1)*(m/(d+1)) ≤ m ∧ m ≤ 2*(d+1)*(m/(d+1)) := by
  have hd : 0 < d+1 := by omega
  have hdiv : 0 < m/(d+1) := Nat.div_pos (by omega) hd
  have hmul := Nat.div_mul_le_self m (d+1)
  have hrem := Nat.mod_lt m hd
  have he := Nat.mod_add_div m (d+1)
  refine ⟨hdiv,Nat.div_le_self _ _,by nlinarith,?_⟩
  nlinarith

end KakeyaTwoScale
#print axioms KakeyaTwoScale.translate_interval_support
#print axioms KakeyaTwoScale.floor_cutoff_parameters
