module
public import KakeyaTwoScale.RoundedParentCaps
public import KakeyaTwoScale.CoarseArithmeticWeight

@[expose] public section

open MeasureTheory
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
open Classical

/-- The coarse arithmetic weight inequality for the actual rounded parent
level. No parent count, fiber cap, chart realization, capacity comparison,
or arithmetic volume premise is supplied. The comparison volume is the
actual occupied coarse-grid union of the constructed parent axes. -/
theorem rounded_coarse_arithmetic_weight (n : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ c : ℝ, 0 < c ∧ ∀ {J : Type*} (S : Finset J) (b v : J → Fin n → ℝ)
      (level : ℕ) (d r : ℝ) (hd : 0 < d) (hdr : d ≤ r), r ≤ 1 →
      (∀ j ∈ S, ‖v j‖ ≤ R) →
      (∀ j ∈ S, ∀ l ∈ S, j ≠ l → d ≤ dist (v j) (v l)) →
      let F := RoundedParentLevel.fixed S b v level (d^n) r (pow_pos hd n) (hd.trans_le hdr)
      c*(r^n)^theta*(d^n*(F.children.card:ℝ))^a ≤
        volume.real (occupiedGridRegion F.parents
          (RoundedParentLevel.parentBase r) (RoundedParentLevel.parentSlope r) r
          (fun _ => Set.Icc (0:ℝ) 1))*F.weight^theta := by
  obtain ⟨c,hc,hvol⟩ := coarse_arithmetic_weight n (roundedParentCapConstant n R)
    (roundedParentCapConstant_pos n R hR)
  refine ⟨c,hc,?_⟩
  intro J S b v level d r hd hdr hrone hv hsep
  let F := RoundedParentLevel.fixed S b v level (d^n) r (pow_pos hd n) (hd.trans_le hdr)
  change c*(r^n)^theta*(d^n*(F.children.card:ℝ))^a ≤
    volume.real (occupiedGridRegion F.parents
      (RoundedParentLevel.parentBase r) (RoundedParentLevel.parentSlope r) r
      (fun _ => Set.Icc (0:ℝ) 1))*F.weight^theta
  by_cases hne : F.parents.Nonempty
  · have hcap : ∀ y ∈ F.parents.image Prod.snd,
        ((F.parents.filter (fun p => p.2=y)).card:ℝ) ≤ roundedParentCapConstant n R/F.weight := by
      intro y _
      exact rounded_parent_slope_fiber_cap S b v level d r R hd hdr hrone hR hv hsep y
    have hm := F.covered_cell_mass (selected:=F.children) (Finset.Subset.refl _)
      F.parents (Finset.Subset.refl _) F.assigned
    have hmass : d^n*(F.children.card:ℝ) ≤ 2*F.weight*r^n*(F.parents.card:ℝ) := by
      have hm' : d^n*(F.children.card:ℝ) ≤ 2*r^n*(F.weight*(F.parents.card:ℝ)) := hm
      convert hm' using 1; ring
    have hh := hvol r F.weight (d^n*(F.children.card:ℝ)) (hd.trans_le hdr) F.weight_pos
      (by positivity) F.parents hne hcap hmass 0 0
    simp only [add_zero] at hh
    exact hh
  · have hp : F.parents=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    have hs : F.children=∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      rintro ⟨j,hj⟩
      have hh := F.assigned j hj
      simp [hp] at hh
    simp only [hs,Finset.card_empty,Nat.cast_zero,mul_zero,
      Real.zero_rpow (show a ≠ 0 by norm_num [a])]
    exact mul_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg F.weight_pos.le _)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.rounded_coarse_arithmetic_weight
