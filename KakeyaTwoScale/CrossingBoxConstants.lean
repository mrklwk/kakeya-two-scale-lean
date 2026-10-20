module
public import KakeyaTwoScale.BoxCrossingAreaBound
public import Mathlib.Order.Interval.Finset.Fin

@[expose] public section

open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

theorem intervalVolume_univ (c : ℝ) : intervalVolume c univ = ENNReal.ofReal (2*c) := by
  simp [intervalVolume,Real.volume_Ioo,sub_neg_eq_add,two_mul]

/-- The exact unused-coordinate factor in the reviewed bisection argument. -/
theorem crossing_box_factor {n : ℕ} (α b : ℝ) (j : Fin (n+1)) :
    (Measure.pi (fun i : Fin (n+1) => if i.val < j.val then intervalVolume α else intervalVolume b)) univ * intervalVolume α univ =
      (ENNReal.ofReal (2*α))^(j.val+1) * (ENNReal.ofReal (2*b))^(n+1-j.val) := by
  have (i : Fin (n+1)) : IsFiniteMeasure (if i.val < j.val then intervalVolume α else intervalVolume b) := by
    split_ifs <;> infer_instance
  rw [Measure.pi_univ]
  have he (i : Fin (n+1)) : (if i.val < j.val then intervalVolume α else intervalVolume b) univ =
      if i.val < j.val then ENNReal.ofReal (2*α) else ENNReal.ofReal (2*b) := by
    split_ifs <;> exact intervalVolume_univ _
  simp_rw [he,intervalVolume_univ]
  rw [Finset.prod_ite]
  have hlt : (Finset.univ.filter (fun i : Fin (n+1) => i.val < j.val)) = Finset.Iio j := by ext i; simp
  have hge : (Finset.univ.filter (fun i : Fin (n+1) => ¬i.val < j.val)) = Finset.Ici j := by ext i; simp
  rw [hlt,hge]
  simp only [Finset.prod_const,Fin.card_Iio,Fin.card_Ici,pow_succ]
  ring

end KakeyaTwoScale
#print axioms KakeyaTwoScale.intervalVolume_univ
#print axioms KakeyaTwoScale.crossing_box_factor
