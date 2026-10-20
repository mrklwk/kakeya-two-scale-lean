module
public import KakeyaTwoScale.ConcreteRootGeometry
public import KakeyaTwoScale.GridIntegerBank

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- A finite grid bank for arbitrary translated unit cylinders. Its size may
depend on positions; no bound on that size is used in the analytic estimate. -/
theorem exists_finite_cylinder_grid_bank {d N : ℕ} (delta : ℝ) (hd : 0<delta)
    (b u : Fin N→EuclideanSpace ℝ (Fin d)) (hu : ∀o, ‖u o‖=1) :
    ∃ cubes : Finset (Fin d→ℤ), ∀o x, x∈flatCylinder (b o) (u o) 1 delta →
      gridIndex delta (WithLp.ofLp x)∈cubes := by
  classical
  let R := (∑o, ‖b o‖)+1+delta
  let M := ⌈R/delta⌉₊+2
  refine ⟨gridIndexBank d M,?_⟩
  intro o x hx
  obtain ⟨t,ht0,ht1,_,hx⟩ := hx
  have hb : ‖b o‖≤∑o, ‖b o‖ := Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ o)
  have hnorm : ‖x‖≤R := by
    have h1 := norm_le_norm_sub_add x (b o+t • u o)
    have h2 := norm_add_le (b o) (t • u o)
    rw [norm_smul,hu o,Real.norm_eq_abs,abs_of_pos ht0,mul_one] at h2
    dsimp [R]
    linarith
  apply (mem_gridIndexBank _).mpr
  intro j
  have hcoord : |x j|≤R := (PiLp.norm_apply_le x j).trans hnorm
  have hdiv : -(R/delta)≤x j/delta ∧ x j/delta≤R/delta := by
    constructor
    · rw [←neg_div]
      exact div_le_div_of_nonneg_right (abs_le.mp hcoord).1 hd.le
    · exact div_le_div_of_nonneg_right (abs_le.mp hcoord).2 hd.le
  have hceil := Nat.le_ceil (R/delta)
  have hlo := Int.floor_le (x j/delta)
  have hhi := Int.lt_floor_add_one (x j/delta)
  change -(M:ℤ)≤⌊x j/delta⌋ ∧ ⌊x j/delta⌋≤(M:ℤ)
  constructor
  · have hh : -(M:ℝ)≤(⌊x j/delta⌋:ℝ) := by dsimp [M]; push_cast; linarith
    exact_mod_cast hh
  · have hh : (⌊x j/delta⌋:ℝ)≤(M:ℝ) := by dsimp [M]; push_cast; linarith
    exact_mod_cast hh

end KakeyaTwoScale
#print axioms KakeyaTwoScale.exists_finite_cylinder_grid_bank
