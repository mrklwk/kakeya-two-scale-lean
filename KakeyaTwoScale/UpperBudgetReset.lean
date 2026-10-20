module
public import KakeyaTwoScale.NonlinearTupleSelection

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- Count actual piece occurrences through their new grains and old origins.
An old-origin fiber bound costs at most the number of NEW grains, since each
new grain has one origin. No nonlinear-mass retention premise is used. -/
theorem piece_count_from_origin_fibers {T G O : Type*}
    [DecidableEq T] [DecidableEq G] [DecidableEq O]
    (S : Finset T) (grain : T → G) (origin : G → O) {K : ℝ} (hK : 0 ≤ K)
    (hfiber : ∀ o ∈ S.image (origin ∘ grain),
      ((S.filter fun t => origin (grain t)=o).card:ℝ) ≤ K) :
    (S.card:ℝ) ≤ K*((S.image grain).card:ℝ) := by
  classical
  have he := Finset.card_eq_sum_card_fiberwise
    (s:=S) (t:=S.image (origin ∘ grain)) (f:=origin ∘ grain)
    (fun t ht => Finset.mem_image_of_mem (origin ∘ grain) ht)
  have he' : (S.card:ℝ) = ∑ o ∈ S.image (origin ∘ grain),
      ((S.filter fun t => origin (grain t)=o).card:ℝ) := by exact_mod_cast he
  have hi : (S.image (origin ∘ grain)).card ≤ (S.image grain).card := by
    rw [← Finset.image_image]
    exact Finset.card_image_le
  calc
    (S.card:ℝ) = _ := he'
    _ ≤ ∑ _o ∈ S.image (origin ∘ grain), K := Finset.sum_le_sum hfiber
    _ = K*((S.image (origin ∘ grain)).card:ℝ) := by simp [mul_comm]
    _ ≤ K*((S.image grain).card:ℝ) := mul_le_mul_of_nonneg_left (by exact_mod_cast hi) hK

/-- Combine global and old-origin counting bounds without paying a new small
power of delta when the number of grains changes. For q=1/d, d>=1, this is
the upper-budget reset algebra. Occurrence nonduplication and the per-origin
cut budget must be established geometrically before applying this theorem. -/
theorem upper_budget_reset {T G O : Type*}
    [DecidableEq T] [DecidableEq G] [DecidableEq O]
    (S : Finset T) (grain : T → G) (origin : G → O)
    {A X C h q : ℝ} (hA : 1 ≤ A) (hX : 0 ≤ X) (hC : 0 ≤ C) (hh : 0 < h)
    (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hglobal : (S.card:ℝ) ≤ X*C)
    (hfiber : ∀ o ∈ S.image (origin ∘ grain),
      ((S.filter fun t => origin (grain t)=o).card:ℝ) ≤ A*X*C/h) :
    (S.card:ℝ) ≤ A*X*C*(((S.image grain).card:ℝ)/h)^q := by
  have hAXC : 0 ≤ A*X*C := by positivity
  have hlocal := piece_count_from_origin_fibers S grain origin (div_nonneg hAXC hh.le) hfiber
  let r : ℝ := ((S.image grain).card:ℝ)/h
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hlocal' : (S.card:ℝ) ≤ A*X*C*r := by
    dsimp [r]
    convert hlocal using 1; ring
  change (S.card:ℝ) ≤ A*X*C*r^q
  by_cases hr1 : r ≤ 1
  · exact hlocal'.trans (mul_le_mul_of_nonneg_left (Real.self_le_rpow_of_le_one hr hr1 hq1) hAXC)
  · have hp := Real.one_le_rpow (le_of_not_ge hr1) hq
    have hg : X*C ≤ A*X*C := by nlinarith [mul_nonneg hX hC]
    exact hglobal.trans (hg.trans (by nlinarith))

end KakeyaTwoScale
#print axioms KakeyaTwoScale.piece_count_from_origin_fibers
#print axioms KakeyaTwoScale.upper_budget_reset
