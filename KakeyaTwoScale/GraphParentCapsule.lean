module
public import KakeyaTwoScale.GraphDirectionRealization
public import KakeyaTwoScale.BrushCaptureGeometry
public import KakeyaTwoScale.VariableTubeVolume
public import KakeyaTwoScale.WeightedTubeVolume

@[expose] public section

open MeasureTheory
noncomputable section
namespace KakeyaTwoScale

 theorem unsplit_height {n : ℕ} (i : Fin (n+1)) (p : ℝ × (Fin n → ℝ)) :
    euclideanUnsplit i p i = p.1 := congrArg Prod.fst (euclideanSplit_unsplit i p)

 theorem unsplit_horizontal {n : ℕ} (i : Fin (n+1)) (p : ℝ × (Fin n → ℝ)) (j : Fin n) :
    euclideanUnsplit i p (i.succAbove j) = p.2 j :=
  congrFun (congrArg Prod.snd (euclideanSplit_unsplit i p)) j

/-- Exact graph segment identity. Its parameter remains in the original
unit height interval; the spatial segment is never extended. -/
theorem unsplit_graph_point {n : ℕ} (i : Fin (n+1)) (b v : Fin n → ℝ) (t : ℝ) :
    euclideanUnsplit i (t,segmentPoint b v t)=
      euclideanUnsplit i (0,b)+t • euclideanUnsplit i (1,v) := by
  apply WithLp.ofLp_injective 2
  apply funext
  apply (Fin.forall_iff_succAbove i (P:=fun j =>
    euclideanUnsplit i (t,segmentPoint b v t) j =
      (euclideanUnsplit i (0,b)+t • euclideanUnsplit i (1,v)) j)).mpr
  constructor
  · simp [unsplit_height]
  · intro j
    simp [unsplit_horizontal,segmentPoint]

/-- Sup-norm horizontal error converts to Euclidean error at the same height. -/
theorem unsplit_same_height_dist {n : ℕ} (i : Fin (n+1))
    (x y : Fin n → ℝ) (t : ℝ) :
    dist (euclideanUnsplit i (t,x)) (euclideanUnsplit i (t,y)) ≤ (n+2:ℝ)*dist x y := by
  rw [dist_eq_norm]
  apply euclidean_norm_of_coordinate_bound _ _ dist_nonneg
  apply (Fin.forall_iff_succAbove i (P:=fun j =>
    |(euclideanUnsplit i (t,x)-euclideanUnsplit i (t,y)) j| ≤ dist x y)).mpr
  constructor
  · simp [unsplit_height]
  · intro j
    simpa only [PiLp.sub_apply,unsplit_horizontal,Real.dist_eq] using dist_le_pi_dist x y j

/-- Exact axis length, its unit direction, and a uniform upper length bound. -/
theorem graph_axis_length {n : ℕ} (i : Fin (n+1)) (v : Fin n → ℝ)
    (R : ℝ) (hR : 0 ≤ R) (hv : ‖v‖ ≤ R) :
    1 ≤ ‖euclideanUnsplit i (1,v)‖ ∧
    ‖euclideanUnsplit i (1,v)‖ ≤ (n+2:ℝ)*(R+1) ∧
    euclideanUnsplit i (1,v)=‖euclideanUnsplit i (1,v)‖ • graphUnitDirection i v := by
  refine ⟨?_,?_,(NormedSpace.norm_smul_normalize _).symm⟩
  · simpa [Real.norm_eq_abs,graphVector_height] using PiLp.norm_apply_le (euclideanUnsplit i (1,v)) i
  · apply euclidean_norm_of_coordinate_bound _ _ (by positivity)
    apply (Fin.forall_iff_succAbove i (P:=fun j => |euclideanUnsplit i (1,v) j| ≤ R+1)).mpr
    constructor
    · rw [graphVector_height,abs_one]; linarith
    · intro j
      rw [graphVector_slope]
      have hj : |v j| ≤ ‖v‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm v j
      linarith

/-- The closed horizontal parent fits in an open Euclidean capsule around
its exact finite graph segment. The strict radius margin preserves caps. -/
theorem horizontal_parent_subset_capsule {n : ℕ} (i : Fin (n+1))
    (b v : Fin n → ℝ) (r : ℝ) (hr : 0 < r) :
    euclideanUnsplit i '' horizontalTube b v (4*r) ⊆
      euclideanTube (euclideanUnsplit i (0,b)) (euclideanUnsplit i (1,v))
        ((4*(n+2:ℝ)+1)*r) := by
  rintro x ⟨p,hp,rfl⟩
  refine ⟨p.1,hp.1,?_⟩
  rw [← unsplit_graph_point]
  have hh := unsplit_same_height_dist i p.2 (segmentPoint b v p.1) p.1
  have hm := mul_le_mul_of_nonneg_left hp.2 (show 0 ≤ (n+2:ℝ) by positivity)
  change dist (euclideanUnsplit i (p.1,p.2)) (euclideanUnsplit i (p.1,segmentPoint b v p.1)) < _
  nlinarith

/-- Domination of the original whole-family overlap after changing coordinates
and enlarging the same exact graph segments. No weights are recomputed. -/
theorem horizontal_parent_overlap_le {n : ℕ} {P : Type*} (i : Fin (n+1))
    (parents : Finset P) (b v : P → Fin n → ℝ) (w : P → ℝ)
    (hw : ∀ p ∈ parents, 0 ≤ w p) (r : ℝ) (hr : 0 < r) (x : ℝ × (Fin n → ℝ)) :
    weightedOverlap parents (fun p => horizontalTube (b p) (v p) (4*r)) w x ≤
      weightedOverlap parents (fun p => euclideanTube (euclideanUnsplit i (0,b p))
        (euclideanUnsplit i (1,v p)) ((4*(n+2:ℝ)+1)*r)) w (euclideanUnsplit i x) := by
  unfold weightedOverlap
  apply Finset.sum_le_sum
  intro p hp
  by_cases hx : x ∈ horizontalTube (b p) (v p) (4*r)
  · rw [Set.indicator_of_mem hx,Set.indicator_of_mem
      (horizontal_parent_subset_capsule i (b p) (v p) r hr ⟨x,hx,rfl⟩)]
  · rw [Set.indicator_of_notMem hx]
    exact Set.indicator_nonneg (fun _ _ => hw p hp) _

/-- Exact volume preservation for the coordinate realization, including all
measurable capture sets. -/
theorem volume_real_unsplit_image {n : ℕ} (i : Fin (n+1))
    (E : Set (ℝ × (Fin n → ℝ))) (hE : MeasurableSet E) :
    volume.real (euclideanUnsplit i '' E)=volume.real E := by
  have heq : euclideanUnsplit i '' E=euclideanSplit i ⁻¹' E := by
    ext x
    constructor
    · rintro ⟨p,hp,rfl⟩
      simpa [euclideanSplit_unsplit] using hp
    · intro hx
      exact ⟨euclideanSplit i x,hx,euclideanUnsplit_split i x⟩
  rw [Measure.real,heq,(euclideanSplit_measurePreserving i).measure_preimage hE.nullMeasurableSet]
  rfl

/-- Actual capture volume transfers to the enlarged capsules with the same
original finite parent family, original weights and original threshold. -/
theorem horizontal_parent_capture_volume_le {n : ℕ} {P : Type*} (i : Fin (n+1))
    (parents : Finset P) (b v : P → Fin n → ℝ) (w : P → ℝ)
    (hw : ∀ p ∈ parents, 0 ≤ w p) (r M : ℝ) (hr : 0 < r) (p : P) :
    volume.real (horizontalTube (b p) (v p) (4*r) ∩
      {x | M ≤ weightedOverlap parents (fun p => horizontalTube (b p) (v p) (4*r)) w x}) ≤
    volume.real (euclideanTube (euclideanUnsplit i (0,b p)) (euclideanUnsplit i (1,v p))
      ((4*(n+2:ℝ)+1)*r) ∩ {x | M ≤ weightedOverlap parents
        (fun p => euclideanTube (euclideanUnsplit i (0,b p)) (euclideanUnsplit i (1,v p))
          ((4*(n+2:ℝ)+1)*r)) w x}) := by
  let E := horizontalTube (b p) (v p) (4*r) ∩
    {x | M ≤ weightedOverlap parents (fun p => horizontalTube (b p) (v p) (4*r)) w x}
  have hE : MeasurableSet E := (measurableSet_horizontalTube _ _ _).inter
    (measurableSet_le measurable_const (measurable_weightedOverlap parents _ w
      (fun p _ => measurableSet_horizontalTube _ _ _)))
  rw [← volume_real_unsplit_image i E hE]
  apply measureReal_mono ?_ (measure_ne_top_of_subset Set.inter_subset_left
    (euclideanTube_finite _ _ _))
  rintro x ⟨y,hy,rfl⟩
  exact ⟨horizontal_parent_subset_capsule i (b p) (v p) r hr ⟨y,hy.1,rfl⟩,
    hy.2.trans (horizontal_parent_overlap_le i parents b v w hw r hr y)⟩

/-- A parent capsule stays near the original set whenever one represented
child's finite graph segment does. This uses only matching parameters in
[0,1], and never extends a graph axis past its original endpoints. -/
theorem graph_parent_capsule_near_set {n : ℕ} (i : Fin (n+1))
    (b v bP vP : Fin n → ℝ) (r width s : ℝ)
    (hb : dist b bP ≤ r) (hv : dist v vP ≤ r)
    (K : Set (EuclideanSpace ℝ (Fin (n+1))))
    (hK : ∀ t ∈ Set.Icc (0:ℝ) 1,
      euclideanUnsplit i (t,segmentPoint b v t) ∈ Metric.thickening s K) :
    euclideanTube (euclideanUnsplit i (0,bP)) (euclideanUnsplit i (1,vP)) width ⊆
      Metric.thickening (width+2*(n+2:ℝ)*r+s) K := by
  intro x hx
  obtain ⟨t,ht,hx⟩ := hx
  obtain ⟨y,hy,hxy⟩ := Metric.mem_thickening_iff.mp (hK t ht)
  apply Metric.mem_thickening_iff.mpr
  refine ⟨y,hy,?_⟩
  have hp := unsplit_same_height_dist i (segmentPoint b v t) (segmentPoint bP vP t) t
  have hround := mul_le_mul_of_nonneg_left (segmentPoint_dist_le b v bP vP r t ht hb hv)
    (show 0 ≤ (n+2:ℝ) by positivity)
  have haxis := hp.trans hround
  rw [dist_comm] at haxis
  rw [← unsplit_graph_point] at hx
  have hd1 := dist_triangle x (euclideanUnsplit i (t,segmentPoint bP vP t))
    (euclideanUnsplit i (t,segmentPoint b v t))
  have hd2 := dist_triangle x (euclideanUnsplit i (t,segmentPoint b v t)) y
  nlinarith

/-- Radius bookkeeping for the actual rounded parent at source scales.
The output is one fixed multiple of rho, including the original A delta error. -/
theorem rounded_parent_capsule_near_set {n : ℕ} (i : Fin (n+1))
    (b v : Fin n → ℝ) (d r A : ℝ) (hr : 0 < r) (hdr : d ≤ r) (hA : 0 ≤ A)
    (K : Set (EuclideanSpace ℝ (Fin (n+1))))
    (hK : ∀ t ∈ Set.Icc (0:ℝ) 1,
      euclideanUnsplit i (t,segmentPoint b v t) ∈ Metric.thickening (A*d) K) :
    euclideanTube (euclideanUnsplit i (0,gridRound r b))
      (euclideanUnsplit i (1,gridRound r v)) ((4*(n+2:ℝ)+1)*r) ⊆
      Metric.thickening ((6*(n+2:ℝ)+1+A)*r) K := by
  have hs := graph_parent_capsule_near_set i b v (gridRound r b) (gridRound r v)
    r ((4*(n+2:ℝ)+1)*r) (A*d) (dist_gridRound_le hr b) (dist_gridRound_le hr v) K hK
  intro x hx
  obtain ⟨y,hy,hd⟩ := Metric.mem_thickening_iff.mp (hs hx)
  apply Metric.mem_thickening_iff.mpr
  refine ⟨y,hy,?_⟩
  have hh := mul_le_mul_of_nonneg_left hdr hA
  nlinarith

theorem horizontal_parent_subset_capsule_width {n : ℕ} (i : Fin (n+1))
    (b v : Fin n → ℝ) (r D : ℝ) (hr : 0 < r) (hD : 4*(n+2:ℝ)+1 ≤ D) :
    euclideanUnsplit i '' horizontalTube b v (4*r) ⊆
      euclideanTube (euclideanUnsplit i (0,b)) (euclideanUnsplit i (1,v))
        (D*r) := by
  rintro x ⟨p,hp,rfl⟩
  refine ⟨p.1,hp.1,?_⟩
  rw [← unsplit_graph_point]
  have hh := unsplit_same_height_dist i p.2 (segmentPoint b v p.1) p.1
  have hm := mul_le_mul_of_nonneg_left hp.2 (show 0 ≤ (n+2:ℝ) by positivity)
  change dist (euclideanUnsplit i (p.1,p.2)) (euclideanUnsplit i (p.1,segmentPoint b v p.1)) < _
  nlinarith

/-- Domination of the original whole-family overlap after changing coordinates
and enlarging the same exact graph segments. No weights are recomputed. -/
theorem horizontal_parent_overlap_le_width {n : ℕ} {P : Type*} (i : Fin (n+1))
    (parents : Finset P) (b v : P → Fin n → ℝ) (w : P → ℝ)
    (hw : ∀ p ∈ parents, 0 ≤ w p) (r D : ℝ) (hr : 0 < r) (hD : 4*(n+2:ℝ)+1 ≤ D) (x : ℝ × (Fin n → ℝ)) :
    weightedOverlap parents (fun p => horizontalTube (b p) (v p) (4*r)) w x ≤
      weightedOverlap parents (fun p => euclideanTube (euclideanUnsplit i (0,b p))
        (euclideanUnsplit i (1,v p)) (D*r)) w (euclideanUnsplit i x) := by
  unfold weightedOverlap
  apply Finset.sum_le_sum
  intro p hp
  by_cases hx : x ∈ horizontalTube (b p) (v p) (4*r)
  · rw [Set.indicator_of_mem hx,Set.indicator_of_mem
      (horizontal_parent_subset_capsule_width i (b p) (v p) r D hr hD ⟨x,hx,rfl⟩)]
  · rw [Set.indicator_of_notMem hx]
    exact Set.indicator_nonneg (fun _ _ => hw p hp) _

theorem horizontal_parent_capture_volume_le_width {n : ℕ} {P : Type*} (i : Fin (n+1))
    (parents : Finset P) (b v : P → Fin n → ℝ) (w : P → ℝ)
    (hw : ∀ p ∈ parents, 0 ≤ w p) (r M D : ℝ) (hr : 0 < r) (hD : 4*(n+2:ℝ)+1 ≤ D) (p : P) :
    volume.real (horizontalTube (b p) (v p) (4*r) ∩
      {x | M ≤ weightedOverlap parents (fun p => horizontalTube (b p) (v p) (4*r)) w x}) ≤
    volume.real (euclideanTube (euclideanUnsplit i (0,b p)) (euclideanUnsplit i (1,v p))
      (D*r) ∩ {x | M ≤ weightedOverlap parents
        (fun p => euclideanTube (euclideanUnsplit i (0,b p)) (euclideanUnsplit i (1,v p))
          (D*r)) w x}) := by
  let E := horizontalTube (b p) (v p) (4*r) ∩
    {x | M ≤ weightedOverlap parents (fun p => horizontalTube (b p) (v p) (4*r)) w x}
  have hE : MeasurableSet E := (measurableSet_horizontalTube _ _ _).inter
    (measurableSet_le measurable_const (measurable_weightedOverlap parents _ w
      (fun p _ => measurableSet_horizontalTube _ _ _)))
  rw [← volume_real_unsplit_image i E hE]
  apply measureReal_mono ?_ (measure_ne_top_of_subset Set.inter_subset_left
    (euclideanTube_finite _ _ _))
  rintro x ⟨y,hy,rfl⟩
  exact ⟨horizontal_parent_subset_capsule_width i (b p) (v p) r D hr hD ⟨y,hy.1,rfl⟩,
    hy.2.trans (horizontal_parent_overlap_le_width i parents b v w hw r D hr hD y)⟩

/-- Absolute horizontal capture becomes a fixed positive fraction of the
actual variable-length Euclidean capsule. The full original family and its
high-overlap threshold are preserved; the volume upper bound is proved. -/
theorem graph_parent_relative_capture {n : ℕ} {P : Type*} (i : Fin (n+1))
    (parents : Finset P) (b v : P → Fin n → ℝ) (w : P → ℝ)
    (hw : ∀ p ∈ parents, 0 ≤ w p) (r M D L eta : ℝ)
    (hr : 0 < r) (hD : 4*(n+2:ℝ)+1 ≤ D) (hwidth : D*r ≤ 1/2)
    (hL : 1 ≤ L) (heta : 0 ≤ eta) (p : P)
    (hlength : ‖euclideanUnsplit i (1,v p)‖ ≤ L)
    (hcapture : eta*r^n ≤ volume.real (horizontalTube (b p) (v p) (4*r) ∩
      {x | M ≤ weightedOverlap parents (fun p => horizontalTube (b p) (v p) (4*r)) w x})) :
    let T := fun p => euclideanTube (euclideanUnsplit i (0,b p))
      (euclideanUnsplit i (1,v p)) (D*r)
    (eta/(3*L*(2*(n+3:ℝ))^n*D^n))*volume.real (T p) ≤
      volume.real (T p ∩ {x | M ≤ weightedOverlap parents T w x}) := by
  dsimp only
  have hDpos : 0 < D := by have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n; nlinarith
  have hLpos : 0 < L := by linarith
  have hell : 0 ≤ ‖euclideanUnsplit i (1,v p)‖ := norm_nonneg _
  have haxis : euclideanUnsplit i (1,v p)=
      ‖euclideanUnsplit i (1,v p)‖ • graphUnitDirection i (v p) :=
    (NormedSpace.norm_smul_normalize _).symm
  have hu := variable_tube_volume_upper (euclideanUnsplit i (0,b p))
    (graphUnitDirection i (v p)) ‖euclideanUnsplit i (1,v p)‖ L hell hL hlength
    (mul_pos hDpos hr) hwidth (graphUnitDirection_norm i (v p))
  rw [← haxis,mul_pow D r n] at hu
  have hh := mul_le_mul_of_nonneg_left hu
    (show 0 ≤ eta/(3*L*(2*(n+3:ℝ))^n*D^n) by positivity)
  have heq : (eta/(3*L*(2*(n+3:ℝ))^n*D^n))*(3*L*(2*(n+3:ℝ))^n*(D^n*r^n))=eta*r^n := by
    have hden : 3*L*(2*(n+3:ℝ))^n*D^n ≠ 0 := by positivity
    field_simp
  rw [heq] at hh
  exact hh.trans (hcapture.trans (horizontal_parent_capture_volume_le_width
    i parents b v w hw r M D hr hD p))

/-- Arbitrarily enlarged exact rounded-parent capsules remain in a fixed
rho-neighborhood of the original set. D may be a chosen power of two. -/
theorem rounded_parent_capsule_near_set_width {n : ℕ} (i : Fin (n+1))
    (b v : Fin n → ℝ) (d r A D : ℝ) (hr : 0 < r) (hdr : d ≤ r) (hA : 0 ≤ A)
    (K : Set (EuclideanSpace ℝ (Fin (n+1))))
    (hK : ∀ t ∈ Set.Icc (0:ℝ) 1,
      euclideanUnsplit i (t,segmentPoint b v t) ∈ Metric.thickening (A*d) K) :
    euclideanTube (euclideanUnsplit i (0,gridRound r b))
      (euclideanUnsplit i (1,gridRound r v)) (D*r) ⊆
      Metric.thickening ((D+2*(n+2:ℝ)+A)*r) K := by
  have hs := graph_parent_capsule_near_set i b v (gridRound r b) (gridRound r v)
    r (D*r) (A*d) (dist_gridRound_le hr b) (dist_gridRound_le hr v) K hK
  intro x hx
  obtain ⟨y,hy,hd⟩ := Metric.mem_thickening_iff.mp (hs hx)
  apply Metric.mem_thickening_iff.mpr
  refine ⟨y,hy,?_⟩
  have hh := mul_le_mul_of_nonneg_left hdr hA
  nlinarith

end KakeyaTwoScale

#print axioms KakeyaTwoScale.unsplit_graph_point
#print axioms KakeyaTwoScale.unsplit_same_height_dist
#print axioms KakeyaTwoScale.graph_axis_length
#print axioms KakeyaTwoScale.horizontal_parent_subset_capsule
#print axioms KakeyaTwoScale.horizontal_parent_overlap_le
#print axioms KakeyaTwoScale.volume_real_unsplit_image
#print axioms KakeyaTwoScale.horizontal_parent_capture_volume_le
#print axioms KakeyaTwoScale.graph_parent_capsule_near_set
#print axioms KakeyaTwoScale.rounded_parent_capsule_near_set

#print axioms KakeyaTwoScale.horizontal_parent_subset_capsule_width
#print axioms KakeyaTwoScale.horizontal_parent_overlap_le_width
#print axioms KakeyaTwoScale.horizontal_parent_capture_volume_le_width

#print axioms KakeyaTwoScale.graph_parent_relative_capture
#print axioms KakeyaTwoScale.rounded_parent_capsule_near_set_width
