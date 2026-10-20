module
public import KakeyaTwoScale.GlobalNeighborhoodBounds
public import KakeyaTwoScale.EnlargedCover

@[expose] public section

open MeasureTheory Metric
noncomputable section
namespace KakeyaTwoScale

/-- A single dimensional radius and the common inverse-height Jacobian control
all four actual regions of every rounded capacity level. Original segment
inclusion and the exact fine intercept rounding are the only source geometry. -/
theorem uniform_four_region_bounds (n : ℕ) (D : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (i : Fin (n+1)) (s L : ℝ), 0 < L → L ≤ 1 →
    ∀ (K : Set (EuclideanSpace ℝ (Fin (n+1)))), Bornology.IsBounded K →
    ∀ {J : Type*} [DecidableEq J] (G : Finset J) (b₀ b v : J → Fin n → ℝ),
    ∀ (d r : ℝ) (hd : 0 < d) (hdr : d ≤ r) (level : ℕ),
    (∀ j ∈ G, b j=gridRound d (b₀ j)) →
    (∀ j ∈ G, ∀ t ∈ Set.Icc (0:ℝ) 1,
      chartPhysical i s L (t,segmentPoint (b₀ j) (v j) t) ∈ K) →
    let F := RoundedParentLevel.fixed G b v level (d^n) r (pow_pos hd n) (hd.trans_le hdr)
    volume.real (occupiedGridRegion F.children b v d (fun _ => Set.Icc (0:ℝ) 1)) ≤
        L⁻¹*volume.real (thickening (C*d) K) ∧
    volume.real (occupiedGridRegion F.children b v r (fun _ => Set.Icc (0:ℝ) 1)) ≤
        L⁻¹*volume.real (thickening (C*r) K) ∧
    volume.real (occupiedGridRegion F.parents (RoundedParentLevel.parentBase r)
      (RoundedParentLevel.parentSlope r) r (fun _ => Set.Icc (0:ℝ) 1)) ≤
        L⁻¹*volume.real (thickening (C*r) K) ∧
    volume.real (⋃ p ∈ F.parents, euclideanTube
      (euclideanUnsplit i (0,RoundedParentLevel.parentBase r p))
      (euclideanUnsplit i (1,RoundedParentLevel.parentSlope r p)) (D*r)) ≤
        L⁻¹*volume.real (thickening (C*r) K) := by
  classical
  let C : ℝ := (n+2:ℝ)*(2*|D|+6)
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro i s L hL hLone K hK J _ G b₀ b v d r hd hdr level hbase haxis
  dsimp only
  let F := RoundedParentLevel.fixed G b v level (d^n) r (pow_pos hd n) (hd.trans_le hdr)
  have hr : 0 < r := hd.trans_le hdr
  have hn : (0:ℝ) < n+2 := by positivity
  have h6 : 6*(n+2:ℝ) ≤ C := by dsimp [C]; nlinarith [abs_nonneg D]
  have h4 : 4*(n+2:ℝ) ≤ C := by linarith only [h6,hn]
  have hfull : ((n+2:ℝ)*(|L|+1))*D+5*(n+2:ℝ) ≤ C := by
    rw [abs_of_pos hL]
    have hm0 : 0 ≤ (n+2:ℝ)*(L+1) := by positivity
    have hm : (n+2:ℝ)*(L+1) ≤ 2*(n+2:ℝ) := by nlinarith only [hLone,hn]
    have hprod := mul_le_mul (le_abs_self D) hm hm0 (abs_nonneg D)
    dsimp [C]
    nlinarith only [hprod,hn]
  have hsub : F.children ⊆ G := ParentLevel.selected_subset G (RoundedParentLevel.assign r b v) level
  have haxis' : ∀ j ∈ F.children, ∀ t ∈ Set.Icc (0:ℝ) 1,
      chartPhysical i s L (t,segmentPoint (b₀ j) (v j) t) ∈ K :=
    fun j hj => haxis j (hsub hj)
  have hchild (e : ℝ) (hde : d ≤ e) :
      occupiedGridRegion F.children b v e (fun _ => Set.Icc (0:ℝ) 1) ⊆
        chartPhysical i s L ⁻¹' thickening (C*e) K := by
    have he := hd.trans_le hde
    have hnear : occupiedGridRegion F.children b v e (fun _ => Set.Icc (0:ℝ) 1) ⊆
        chartPhysical i s L ⁻¹' thickening ((4*(n+2:ℝ))*e) K := by
      rw [show (4:ℝ)*(n+2)=(n+2)*(2+2) by ring]
      apply occupied_grid_near_physical_axes i s L F.children b₀ v b v _ K he (by norm_num) (fun _ _ => Set.Subset.rfl) haxis'
      intro j hj t ht
      rw [hbase j (hsub hj)]
      apply segmentPoint_dist_le _ _ _ _ e t ht
      · simpa only [dist_comm] using (dist_gridRound_le hd (b₀ j)).trans hde
      · simpa using he.le
    exact hnear.trans (Set.preimage_mono (thickening_mono (mul_le_mul_of_nonneg_right h4 he.le) K))
  have hparent (p) (hp : p ∈ F.parents) : ∃ j ∈ F.children, F.assign j=p := by
    exact Finset.mem_image.mp hp
  have hpgrid : occupiedGridRegion F.parents (RoundedParentLevel.parentBase r)
      (RoundedParentLevel.parentSlope r) r (fun _ => Set.Icc (0:ℝ) 1) ⊆
        chartPhysical i s L ⁻¹' thickening (C*r) K := by
    intro x hx
    obtain ⟨p,hp,ht,hcell⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨j,hj,rfl⟩ := hparent p hp
    have hb : RoundedParentLevel.parentBase r (F.assign j)=gridRound r (gridRound d (b₀ j)) := by
      change gridRound r (b j)=_
      rw [hbase j (hsub hj)]
    have hv : RoundedParentLevel.parentSlope r (F.assign j)=gridRound r (v j) := rfl
    rw [hb,hv] at hcell
    have hnear := rounded_parent_region_near_K i s L {j} b₀ v
      (fun _ => Set.Icc (0:ℝ) 1) K hd hdr (fun _ _ => Set.Subset.rfl)
      (by intro k hk; have : k=j := Finset.mem_singleton.mp hk; subst k; exact haxis' j hj)
    have hxnear := hnear (Set.mem_iUnion₂.mpr ⟨j,Finset.mem_singleton_self j,ht,hcell⟩)
    exact thickening_mono (mul_le_mul_of_nonneg_right h6 hr.le) K hxnear
  have hcaps : (⋃ p ∈ F.parents, euclideanTube
      (euclideanUnsplit i (0,RoundedParentLevel.parentBase r p))
      (euclideanUnsplit i (1,RoundedParentLevel.parentSlope r p)) (D*r)) ⊆
        euclideanChartAffine i s L ⁻¹' thickening (C*r) K := by
    intro x hx
    obtain ⟨p,hp,hx⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨j,hj,rfl⟩ := hparent p hp
    have hb : RoundedParentLevel.parentBase r (F.assign j)=gridRound r (gridRound d (b₀ j)) := by
      change gridRound r (b j)=_
      rw [hbase j (hsub hj)]
    have hv : RoundedParentLevel.parentSlope r (F.assign j)=gridRound r (v j) := rfl
    rw [hb,hv] at hx
    have hh := rounded_parent_full_capsule_near_K i s L (b₀ j) (v j) K D hd hdr (haxis' j hj) hx
    exact thickening_mono (mul_le_mul_of_nonneg_right hfull hr.le) K hh
  exact ⟨chart_region_volume_le_neighborhood i s hL K (C*d) _ (hchild d le_rfl) (bounded_neighborhood_finite hK _),
    chart_region_volume_le_neighborhood i s hL K (C*r) _ (hchild r hdr) (bounded_neighborhood_finite hK _),
    chart_region_volume_le_neighborhood i s hL K (C*r) _ hpgrid (bounded_neighborhood_finite hK _),
    euclidean_region_volume_le_neighborhood i s hL K (C*r) _ hcaps (bounded_neighborhood_finite hK _)⟩

end KakeyaTwoScale
#print axioms KakeyaTwoScale.uniform_four_region_bounds
