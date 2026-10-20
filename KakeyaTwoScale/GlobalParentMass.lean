module
public import KakeyaTwoScale.ParentLevel
public import KakeyaTwoScale.UniformTransfer

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
namespace ParentLevel
variable {Child Parent : Type*} [DecidableEq Child] [DecidableEq Parent]

/-- Exponential cardinal growth and a scale-uniform original mass produce an
actual original-capacity level with a single reciprocal-linear mass constant. -/
theorem exists_fixed_level_uniform_mass (S : Finset Child) (assign : Child → Parent)
    (fine coarse c₀ : ℝ) (hf : 0<fine) (hc : 0<coarse) (hc₀ : 0<c₀)
    (A B q : ℕ) (hcard : S.card ≤ 2^(A*q+B)) (hmass : c₀ ≤ fine*(S.card:ℝ)) :
    ∃ j ≤ A*q+B,
      c₀/(A+B+1:ℕ)/((q:ℝ)+1) ≤
        fine*((fixed S assign j fine coarse hf hc).children.card:ℝ) ∧
      (fixed S assign j fine coarse hf hc).children.Nonempty := by
  obtain ⟨j,hj,hm⟩ := exists_fixed_level_of_card_bound S assign fine coarse hf hc
    (A*q+B) hcard
  have hden : (0:ℝ)<(A*q+B+1:ℕ) := by positivity
  have hden' : (0:ℝ)<(A+B+1:ℕ)*((q:ℝ)+1) := by positivity
  have hle : ((A*q+B+1:ℕ):ℝ) ≤ (A+B+1:ℕ)*((q:ℝ)+1) := by
    push_cast
    nlinarith [show (0:ℝ) ≤ A by positivity,show (0:ℝ) ≤ B by positivity,
      show (0:ℝ) ≤ q by positivity]
  have hret : c₀/(A+B+1:ℕ)/((q:ℝ)+1) ≤
      fine*((fixed S assign j fine coarse hf hc).children.card:ℝ) := by
    rw [div_div]
    exact (div_le_div_of_nonneg_left hc₀.le hden hle).trans
      ((div_le_div_of_nonneg_right hmass hden.le).trans hm)
  refine ⟨j,hj,hret,?_⟩
  apply Finset.card_pos.mp
  have hpos : (0:ℝ)<fine*((fixed S assign j fine coarse hf hc).children.card:ℝ) :=
    (by positivity : 0<c₀/(A+B+1:ℕ)/((q:ℝ)+1)).trans_le hret
  have : (0:ℝ)<(fixed S assign j fine coarse hf hc).children.card :=
    (mul_pos_iff_of_pos_left hf).mp hpos
  exact_mod_cast this

end ParentLevel

/-- The parent-level denominator q+1 is a polynomial loss with a uniform
constant; no choice of constants depending on q is made. -/
theorem reciprocal_succ_mass {c U : ℝ} {q : ℕ} (hc : 0≤c) (hq : 1≤q)
    (hU : c/((q:ℝ)+1)≤U) : (c/2)/(q:ℝ)≤U := by
  have hq' : (1:ℝ)≤q := by exact_mod_cast hq
  rw [div_div]
  exact (div_le_div_of_nonneg_left hc (by positivity) (by linarith)).trans hU

end KakeyaTwoScale
#print axioms KakeyaTwoScale.ParentLevel.exists_fixed_level_uniform_mass
#print axioms KakeyaTwoScale.reciprocal_succ_mass
