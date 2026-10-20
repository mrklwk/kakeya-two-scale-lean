module
public import KakeyaTwoScale.RoundedParentCaps

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
open Classical

/-- Angular counting for the actual dyadically selected, rounded parents.
All unit-direction, height-coordinate, assignment-capacity and chart-rounding
premises of the generic cap theorem are discharged here. -/
theorem rounded_parent_enlarged_angular_cap {n : ℕ} {J : Type*} [DecidableEq J]
    (S : Finset J) (b v : J → Fin n → ℝ) (level : ℕ)
    (d r R D : ℝ) (hD : 1 ≤ D) (hd : 0 < d) (hdr : d ≤ r) (hrone : r ≤ 1)
    (hR : 0 ≤ R) (hv : ∀ j ∈ S, ‖v j‖ ≤ R)
    (hsep : ∀ j ∈ S, ∀ k ∈ S, j ≠ k → d ≤ dist (v j) (v k))
    (i : Fin (n+1)) (e : EuclideanSpace ℝ (Fin (n+1))) (he : ‖e‖=1) :
    let F := RoundedParentLevel.fixed S b v level (d^n) r (pow_pos hd n) (hd.trans_le hdr)
    (∑ _p ∈ F.parents.filter (fun p => Real.arccos |inner ℝ
      (graphUnitDirection i (RoundedParentLevel.parentSlope r p)) e| ≤ D*r), F.weight) ≤
      D^n*roundedParentCapConstant n R := by
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
  have hDr : r ≤ D*r := by nlinarith
  have hDpos : 0 < D := by linarith
  have hcap := assigned_coarse_angular_cap F.children F.parents F.assign v u i d (D*r) h hd (hdr.trans hDr) hh
    (fun p _ => graphUnitDirection_norm i _) hheight (fun j hj => (hnear j hj).trans hDr)
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
  have hscaled := mul_le_mul_of_nonneg_left hcap (pow_nonneg hDpos.le n)
  rw [Finset.mul_sum] at hscaled
  convert hscaled using 1
  · apply Finset.sum_congr rfl
    intro p _
    have hdscale : (d/r)^n = D^n*(d/(D*r))^n := by
      rw [← mul_pow]
      congr 1
      field_simp
    rw [hdscale, mul_left_comm]
    congr 2
    congr 1
    congr 1
    ext j
    simp only [Finset.mem_filter]
  · rfl


end KakeyaTwoScale
#print axioms KakeyaTwoScale.rounded_parent_enlarged_angular_cap
