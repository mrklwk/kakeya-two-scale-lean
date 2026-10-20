module
public import KakeyaTwoScale.RoundedParentLevel
public import KakeyaTwoScale.SharpBallPacking
public import KakeyaTwoScale.GraphDirectionRealization

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
open Classical

/-- A fixed dimension/slope-bound constant for the source angular caps. -/
def roundedParentCapConstant (n : ℕ) (R : ℝ) : ℝ :=
  let h := 1/((n+2:ℝ)*(R+2))
  (3*(1+2*(1/h+1/(h*h)))+1)^n

theorem roundedParentCapConstant_pos (n : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    0 < roundedParentCapConstant n R := by unfold roundedParentCapConstant; positivity

/-- Angular counting for the actual dyadically selected, rounded parents.
All unit-direction, height-coordinate, assignment-capacity and chart-rounding
premises of the generic cap theorem are discharged here. -/
theorem rounded_parent_angular_cap {n : ℕ} {J : Type*} [DecidableEq J]
    (S : Finset J) (b v : J → Fin n → ℝ) (level : ℕ)
    (d r R : ℝ) (hd : 0 < d) (hdr : d ≤ r) (hrone : r ≤ 1)
    (hR : 0 ≤ R) (hv : ∀ j ∈ S, ‖v j‖ ≤ R)
    (hsep : ∀ j ∈ S, ∀ k ∈ S, j ≠ k → d ≤ dist (v j) (v k))
    (i : Fin (n+1)) (e : EuclideanSpace ℝ (Fin (n+1))) (he : ‖e‖=1) :
    let F := RoundedParentLevel.fixed S b v level (d^n) r (pow_pos hd n) (hd.trans_le hdr)
    (∑ _p ∈ F.parents.filter (fun p => Real.arccos |inner ℝ
      (graphUnitDirection i (RoundedParentLevel.parentSlope r p)) e| ≤ r), F.weight) ≤
      roundedParentCapConstant n R := by
  dsimp only
  let F := RoundedParentLevel.fixed S b v level (d^n) r (pow_pos hd n) (hd.trans_le hdr)
  let u := fun p => graphUnitDirection i (RoundedParentLevel.parentSlope r p)
  let h := 1/((n+2:ℝ)*(R+2))
  have hr : 0 < r := hd.trans_le hdr
  have hh : 0 < h := by dsimp [h]; positivity
  have hsub : F.children ⊆ S := ParentLevel.selected_subset S (RoundedParentLevel.assign r b v) level
  have hparent (p) (hp : p ∈ F.parents) : ∃ j ∈ F.children, F.assign j=p := by
    exact Finset.mem_image.mp hp
  have hheight (p) (hp : p ∈ F.parents) : h ≤ |u p i| := by
    obtain ⟨j,hj,rfl⟩ := hparent p hp
    exact (rounded_graphUnitDirection i (v j) R r hR (hv j (hsub hj)) hr hrone).2.1
  have hnear (j) (hj : j ∈ F.children) : dist (v j) (chartSlope i (u (F.assign j))) ≤ r := by
    exact (rounded_graphUnitDirection i (v j) R r hR (hv j (hsub hj)) hr hrone).2.2
  have hcap := assigned_coarse_angular_cap F.children F.parents F.assign v u i d r h hd hdr hh
    (fun p _ => graphUnitDirection_norm i _) hheight hnear
    (fun j hj k hk hjk => hsep j (hsub hj) k (hsub hk) hjk) e he
  have hweight (p) (hp : p ∈ F.parents) :
      F.weight ≤ ((F.children.filter (fun j => F.assign j=p)).card:ℝ)*(d/r)^n := by
    have heq := ParentLevel.fixed_capacity_original S (RoundedParentLevel.assign r b v)
      level (d^n) (r^n) (pow_pos hd n) (pow_pos hr n) hp
    have hb := (ParentLevel.normalized_capacity_band S (RoundedParentLevel.assign r b v)
      level (pow_pos hd n) (pow_pos hr n) hp).1
    change F.weight ≤ d^n*(ParentLevel.capacity S (RoundedParentLevel.assign r b v) p:ℝ)/r^n at hb
    change F.capacity p = ParentLevel.capacity S (RoundedParentLevel.assign r b v) p at heq
    rw [← heq] at hb
    change F.weight ≤ (F.capacity p:ℝ)*(d/r)^n
    convert hb using 1
    rw [div_pow]
    ring
  apply le_trans (Finset.sum_le_sum (fun p hp => hweight p (Finset.mem_filter.mp hp).1))
  convert hcap using 1
  · apply Finset.sum_congr rfl
    intro p _
    congr 3
    ext j
    simp only [Finset.mem_filter]
  · rfl

/-- Actual repeated rounded slopes inherit the common-weight angular cap.
This is the fiber hypothesis needed by coarse_arithmetic_weight, now proved. -/
theorem rounded_parent_slope_fiber_cap {n : ℕ} {J : Type*} [DecidableEq J]
    (S : Finset J) (b v : J → Fin n → ℝ) (level : ℕ)
    (d r R : ℝ) (hd : 0 < d) (hdr : d ≤ r) (hrone : r ≤ 1)
    (hR : 0 ≤ R) (hv : ∀ j ∈ S, ‖v j‖ ≤ R)
    (hsep : ∀ j ∈ S, ∀ k ∈ S, j ≠ k → d ≤ dist (v j) (v k))
    (y : Fin n → ℤ) :
    let F := RoundedParentLevel.fixed S b v level (d^n) r (pow_pos hd n) (hd.trans_le hdr)
    ((F.parents.filter (fun p => p.2=y)).card:ℝ) ≤ roundedParentCapConstant n R/F.weight := by
  dsimp only
  let F := RoundedParentLevel.fixed S b v level (d^n) r (pow_pos hd n) (hd.trans_le hdr)
  let i : Fin (n+1) := 0
  let e := graphUnitDirection i (latticePoint r y)
  have he : ‖e‖=1 := graphUnitDirection_norm i _
  have hc := rounded_parent_angular_cap S b v level d r R hd hdr hrone hR hv hsep i e he
  change (∑ _p ∈ F.parents.filter (fun p => Real.arccos |inner ℝ
    (graphUnitDirection i (RoundedParentLevel.parentSlope r p)) e| ≤ r), F.weight) ≤
    roundedParentCapConstant n R at hc
  have hsub : F.parents.filter (fun p => p.2=y) ⊆
      F.parents.filter (fun p => Real.arccos |inner ℝ
        (graphUnitDirection i (RoundedParentLevel.parentSlope r p)) e| ≤ r) := by
    intro p hp
    obtain ⟨hp,hy⟩ := Finset.mem_filter.mp hp
    apply Finset.mem_filter.mpr
    refine ⟨hp,?_⟩
    have heq : graphUnitDirection i (RoundedParentLevel.parentSlope r p)=e := by
      dsimp [e,RoundedParentLevel.parentSlope]
      rw [hy]
    rw [heq,real_inner_self_eq_norm_sq,he]
    simpa using (hd.trans_le hdr).le
  have hs := Finset.sum_le_sum_of_subset_of_nonneg (f:=fun _ => F.weight) hsub
    (fun _ _ _ => F.weight_pos.le)
  have hm := hs.trans hc
  simp only [Finset.sum_const,nsmul_eq_mul] at hm
  exact (le_div_iff₀ F.weight_pos).mpr hm

end KakeyaTwoScale
#print axioms KakeyaTwoScale.roundedParentCapConstant_pos
#print axioms KakeyaTwoScale.rounded_parent_angular_cap
#print axioms KakeyaTwoScale.rounded_parent_slope_fiber_cap
