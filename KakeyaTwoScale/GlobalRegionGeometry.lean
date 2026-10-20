module
public import KakeyaTwoScale.GraphParentCapsule
public import KakeyaTwoScale.GridRegion
public import KakeyaTwoScale.RoundedParentLevel

@[expose] public section

open Metric
noncomputable section
namespace KakeyaTwoScale

def chartPhysical {n : ℕ} (i : Fin (n+1)) (s L : ℝ) (p : ℝ × (Fin n → ℝ)) :
    EuclideanSpace ℝ (Fin (n+1)) := euclideanUnsplit i (heightAffine s L p)

def euclideanChartAffine {n : ℕ} (i : Fin (n+1)) (s L : ℝ)
    (x : EuclideanSpace ℝ (Fin (n+1))) := chartPhysical i s L (euclideanSplit i x)

 theorem chartPhysical_same_height_dist {n : ℕ} (i : Fin (n+1)) (s L t : ℝ)
    (x y : Fin n → ℝ) :
    dist (chartPhysical i s L (t,x)) (chartPhysical i s L (t,y)) ≤ (n+2:ℝ)*dist x y :=
  unsplit_same_height_dist i x y (s+L*t)

 theorem euclideanChartAffine_dist_le {n : ℕ} (i : Fin (n+1)) (s L : ℝ)
    (x y : EuclideanSpace ℝ (Fin (n+1))) :
    dist (euclideanChartAffine i s L x) (euclideanChartAffine i s L y) ≤
      ((n+2:ℝ)*(|L|+1))*dist x y := by
  rw [dist_eq_norm]
  have hcoord : ∀ j, |(euclideanChartAffine i s L x-euclideanChartAffine i s L y) j| ≤
      (|L|+1)*dist x y := by
    apply (Fin.forall_iff_succAbove i (P := fun j =>
      |(euclideanChartAffine i s L x-euclideanChartAffine i s L y) j| ≤ (|L|+1)*dist x y)).mpr
    constructor
    · have hi : |x i-y i| ≤ dist x y := by
        simpa [dist_eq_norm,PiLp.sub_apply,Real.norm_eq_abs] using PiLp.norm_apply_le (x-y) i
      simp only [euclideanChartAffine,chartPhysical,heightAffine,euclideanSplit,
        PiLp.sub_apply,unsplit_height]
      have he : s+L*x i-(s+L*y i)=L*(x i-y i) := by ring
      rw [he,abs_mul]
      nlinarith [mul_le_mul_of_nonneg_left hi (abs_nonneg L), dist_nonneg (x:=x) (y:=y)]
    · intro j
      have hi : |x (i.succAbove j)-y (i.succAbove j)| ≤ dist x y := by
        simpa [dist_eq_norm,PiLp.sub_apply,Real.norm_eq_abs] using PiLp.norm_apply_le (x-y) (i.succAbove j)
      simp only [euclideanChartAffine,chartPhysical,heightAffine,euclideanSplit,
        PiLp.sub_apply,unsplit_horizontal]
      nlinarith [mul_nonneg (abs_nonneg L) (dist_nonneg (x:=x) (y:=y))]
  have h := euclidean_norm_of_coordinate_bound _ _ (by positivity) hcoord
  simpa only [mul_assoc] using h

/-- Any occupied cell around a perturbed graph is physically near the original
axis. The perturbation estimates are discharged below for actual rounding. -/
theorem occupied_grid_near_physical_axes {n : ℕ} {J : Type*}
    (i : Fin (n+1)) (s L : ℝ) (S : Finset J)
    (b₀ v₀ b v : J → Fin n → ℝ) (I : J → Set ℝ)
    (K : Set (EuclideanSpace ℝ (Fin (n+1)))) {r A : ℝ}
    (hr : 0 < r) (_hA : 0 ≤ A)
    (hI : ∀ j ∈ S, I j ⊆ Set.Icc (0:ℝ) 1)
    (haxis : ∀ j ∈ S, ∀ t ∈ Set.Icc (0:ℝ) 1,
      chartPhysical i s L (t,segmentPoint (b₀ j) (v₀ j) t) ∈ K)
    (hperturb : ∀ j ∈ S, ∀ t ∈ Set.Icc (0:ℝ) 1,
      dist (segmentPoint (b j) (v j) t) (segmentPoint (b₀ j) (v₀ j) t) ≤ A*r) :
    occupiedGridRegion S b v r I ⊆ chartPhysical i s L ⁻¹'
      thickening (((n+2:ℝ)*(A+2))*r) K := by
  intro p hp
  obtain ⟨j,hj,ht,hcell⟩ := Set.mem_iUnion₂.mp hp
  have ht' := hI j hj ht
  have hnear : dist p.2 (segmentPoint (b j) (v j) p.1) ≤ r :=
    gridCell_dist_le hr.le ((mem_gridCell_iff hr _ _).mpr hcell) (mem_own_gridCell hr _)
  have hd := (dist_triangle p.2 (segmentPoint (b j) (v j) p.1)
    (segmentPoint (b₀ j) (v₀ j) p.1)).trans (add_le_add hnear (hperturb j hj p.1 ht'))
  apply mem_thickening_iff.mpr
  refine ⟨_,haxis j hj p.1 ht',?_⟩
  have hh := chartPhysical_same_height_dist i s L p.1 p.2 (segmentPoint (b₀ j) (v₀ j) p.1)
  have hh' := mul_le_mul_of_nonneg_left hd (show (0:ℝ) ≤ n+2 by positivity)
  change dist (chartPhysical i s L (p.1,p.2)) _ < _
  nlinarith

/-- Fine child cells and coarse child cells use the same fine-rounded intercept.
The scale r may equal d (fine region) or exceed it (coarse region). -/
theorem rounded_child_region_near_K {n : ℕ} {J : Type*}
    (i : Fin (n+1)) (s L : ℝ) (S : Finset J) (b₀ v : J → Fin n → ℝ)
    (I : J → Set ℝ) (K : Set (EuclideanSpace ℝ (Fin (n+1)))) {d r : ℝ}
    (hd : 0 < d) (hdr : d ≤ r)
    (hI : ∀ j ∈ S, I j ⊆ Set.Icc (0:ℝ) 1)
    (haxis : ∀ j ∈ S, ∀ t ∈ Set.Icc (0:ℝ) 1,
      chartPhysical i s L (t,segmentPoint (b₀ j) (v j) t) ∈ K) :
    occupiedGridRegion S (fun j => gridRound d (b₀ j)) v r I ⊆
      chartPhysical i s L ⁻¹' thickening ((4*(n+2:ℝ))*r) K := by
  rw [show (4:ℝ)*(n+2) = (n+2)*(2+2) by ring]
  apply occupied_grid_near_physical_axes i s L S b₀ v _ v I K (hd.trans_le hdr) (by norm_num : (0:ℝ)≤2) hI haxis
  intro j _ t ht
  apply segmentPoint_dist_le _ _ _ _ r t ht
  · simpa only [dist_comm] using (dist_gridRound_le hd (b₀ j)).trans hdr
  · simpa using (hd.trans_le hdr).le

 theorem double_round_segment_near {n : ℕ} (b v : Fin n → ℝ) {d r : ℝ}
    (hd : 0 < d) (hdr : d ≤ r) (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    dist (segmentPoint (gridRound r (gridRound d b)) (gridRound r v) t)
      (segmentPoint b v t) ≤ 4*r := by
  have hr := hd.trans_le hdr
  have hb : dist (gridRound r (gridRound d b)) b ≤ 2*r := by
    have h := dist_triangle b (gridRound d b) (gridRound r (gridRound d b))
    have hd' := dist_gridRound_le hd b
    have hr' := dist_gridRound_le hr (gridRound d b)
    rw [dist_comm]
    linarith
  have hv : dist (gridRound r v) v ≤ 2*r := by
    have h := dist_gridRound_le hr v
    rw [dist_comm]
    linarith
  convert
    segmentPoint_dist_le _ _ _ _ (2*r) t ht hb hv using 1
  ring

/-- Coarse parent cells, indexed by their actual children; passing to an image
of the assignment or deleting parents only reduces this union. -/
theorem rounded_parent_region_near_K {n : ℕ} {J : Type*}
    (i : Fin (n+1)) (s L : ℝ) (S : Finset J) (b₀ v : J → Fin n → ℝ)
    (I : J → Set ℝ) (K : Set (EuclideanSpace ℝ (Fin (n+1)))) {d r : ℝ}
    (hd : 0 < d) (hdr : d ≤ r)
    (hI : ∀ j ∈ S, I j ⊆ Set.Icc (0:ℝ) 1)
    (haxis : ∀ j ∈ S, ∀ t ∈ Set.Icc (0:ℝ) 1,
      chartPhysical i s L (t,segmentPoint (b₀ j) (v j) t) ∈ K) :
    occupiedGridRegion S (fun j => gridRound r (gridRound d (b₀ j)))
      (fun j => gridRound r (v j)) r I ⊆
      chartPhysical i s L ⁻¹' thickening ((6*(n+2:ℝ))*r) K := by
  rw [show (6:ℝ)*(n+2) = (n+2)*(4+2) by ring]
  apply occupied_grid_near_physical_axes i s L S b₀ v _ _ I K (hd.trans_le hdr) (by norm_num : (0:ℝ)≤4) hI haxis
  intro j _ t ht
  exact double_round_segment_near (b₀ j) (v j) hd hdr t ht

set_option maxHeartbeats 400000 in
/-- Full rounded parent capsules, including caps and points at heights outside
[0,1], remain near K after the actual common affine height map. -/
theorem rounded_parent_full_capsule_near_K {n : ℕ}
    (i : Fin (n+1)) (s L : ℝ) (b₀ v : Fin n → ℝ)
    (K : Set (EuclideanSpace ℝ (Fin (n+1)))) {d r : ℝ}
    (D : ℝ) (hd : 0 < d) (hdr : d ≤ r)
    (haxis : ∀ t ∈ Set.Icc (0:ℝ) 1,
      chartPhysical i s L (t,segmentPoint b₀ v t) ∈ K) :
    euclideanTube (euclideanUnsplit i (0,gridRound r (gridRound d b₀)))
      (euclideanUnsplit i (1,gridRound r v)) (D*r) ⊆
      euclideanChartAffine i s L ⁻¹'
        thickening ((((n+2:ℝ)*(|L|+1))*D+5*(n+2:ℝ))*r) K := by
  intro x hx
  obtain ⟨t,ht,hxt⟩ := hx
  rw [← unsplit_graph_point i (gridRound r (gridRound d b₀)) (gridRound r v) t] at hxt
  let y := euclideanUnsplit i (t,segmentPoint (gridRound r (gridRound d b₀)) (gridRound r v) t)
  have hmap := euclideanChartAffine_dist_le i s L x y
  have hM : 0 < (n+2:ℝ)*(|L|+1) := by positivity
  have hnear : dist (euclideanChartAffine i s L x) (euclideanChartAffine i s L y) <
      ((n+2:ℝ)*(|L|+1))*(D*r) := hmap.trans_lt (mul_lt_mul_of_pos_left hxt hM)
  have hy : euclideanChartAffine i s L y = chartPhysical i s L
      (t,segmentPoint (gridRound r (gridRound d b₀)) (gridRound r v) t) := by
    simp only [euclideanChartAffine,y,euclideanSplit_unsplit]
  rw [hy] at hnear
  have hround := (chartPhysical_same_height_dist i s L t
    (segmentPoint (gridRound r (gridRound d b₀)) (gridRound r v) t) (segmentPoint b₀ v t)).trans
    (mul_le_mul_of_nonneg_left (double_round_segment_near b₀ v hd hdr t ht)
      (show (0:ℝ) ≤ n+2 by positivity))
  have hdist : dist (euclideanChartAffine i s L x)
      (chartPhysical i s L (t,segmentPoint b₀ v t)) <
      (((n+2:ℝ)*(|L|+1))*D+5*(n+2:ℝ))*r := by
    calc
      _ ≤ dist (euclideanChartAffine i s L x)
          (chartPhysical i s L (t,segmentPoint (gridRound r (gridRound d b₀)) (gridRound r v) t)) +
          dist (chartPhysical i s L (t,segmentPoint (gridRound r (gridRound d b₀)) (gridRound r v) t))
            (chartPhysical i s L (t,segmentPoint b₀ v t)) := dist_triangle _ _ _
      _ < ((n+2:ℝ)*(|L|+1))*(D*r)+(n+2:ℝ)*(4*r) := add_lt_add_of_lt_of_le hnear hround
      _ = (((n+2:ℝ)*(|L|+1))*D+4*(n+2:ℝ))*r := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by
        have hn : (0:ℝ) ≤ n+2 := by positivity
        linarith only [hn]) (hd.trans_le hdr).le
  change euclideanChartAffine i s L x ∈
    thickening ((((n+2:ℝ)*(|L|+1))*D+5*(n+2:ℝ))*r) K
  exact (mem_thickening_iff (E := K) (x := euclideanChartAffine i s L x)).mpr
    ⟨chartPhysical i s L (t,segmentPoint b₀ v t),haxis t ht,hdist⟩

end KakeyaTwoScale
#print axioms KakeyaTwoScale.euclideanChartAffine_dist_le
#print axioms KakeyaTwoScale.rounded_child_region_near_K
#print axioms KakeyaTwoScale.rounded_parent_region_near_K
#print axioms KakeyaTwoScale.rounded_parent_full_capsule_near_K
