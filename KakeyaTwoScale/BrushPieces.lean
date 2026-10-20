module
public import KakeyaTwoScale.PlaneAngle
public import KakeyaTwoScale.BrushSummation

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [ProperSpace X]

/-- Actual enlarged-plane neighborhoods with the common base-plane
neighborhood removed. The overlap constant precedes every plane and scale. -/
theorem uniform_plane_region_overlap (C : ℝ) (hC : 0 ≤ C) :
    ∃ B : ℕ, ∀ (H : Submodule ℝ X) [H.HasOrthogonalProjection]
      (p : X) {J : Type*} (family : Finset J) (a : J → X) (r s : ℝ),
      0 < r → 0 < s →
      (∀ j ∈ family, ‖a j‖ = 1 ∧ a j ∈ Hᗮ) →
      (∀ j ∈ family, ∀ k ∈ family, j ≠ k →
        r/s ≤ dist (a j) (a k) ∧ r/s ≤ dist (a j) (-a k)) →
      ∀ x, weightedOverlap family (fun j =>
        Metric.thickening (C*r) (extendedPlane H p (a j)) \
        Metric.thickening (s/16) (affinePlane H p)) (fun _ => (1:ℝ)) x ≤ B := by
  obtain ⟨B, hB⟩ := uniform_shortened_piece_overlap (X:=X) (16*C) (by positivity)
  refine ⟨B, ?_⟩
  intro H hH p J family a r s hr hs ha hsep
  apply hB (fun x => normalProjection H (x-p)) family a _ (r/s) (s/16)
    (div_pos hr hs) (by positivity) (fun j hj => (ha j hj).1) hsep
  intro j hj x hx
  refine ⟨?_, ?_⟩
  · exact le_of_not_gt (fun h => hx.2 ((mem_plane_thickening_iff H p x _).mpr h))
  · obtain ⟨t, ht⟩ := (mem_extendedPlane_thickening_iff H p (a j) x _ (ha j hj).2).mp hx.1
    refine ⟨t, ht.le.trans_eq ?_⟩
    field_simp

def assignedTubePieces {J : Type*} (family : Finset J) (assign : J → J)
    (b v : J → X) (I : J → Set ℝ) (r : ℝ) (k : J) : Set X :=
  ⋃ j ∈ family.filter (fun j => assign j = k),
    Metric.thickening r (segmentPoint (b j) (v j) '' I j)

/-- Construct shortened, assigned unions of actual tubes. The net, assignment,
quarter intervals and scale-uniform overlap are all outputs. -/
theorem construct_brush_pieces (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c) :
    ∃ B : ℕ, ∀ (H : Submodule ℝ X) [H.HasOrthogonalProjection]
      (p : X) {J : Type*} (family : Finset J) (b v : J → X) (r s : ℝ),
      family.Nonempty → 0 < r → 0 < s → r ≤ c*s/16 →
      (∀ j ∈ family, c*s ≤ ‖normalProjection H (v j)‖ ∧ ‖normalProjection H (v j)‖ ≤ 2*s) →
      (∀ j ∈ family, ∃ t ∈ Set.Icc (0:ℝ) 1,
        ‖normalProjection H (segmentPoint (b j) (v j) t-p)‖ ≤ C*r) →
      ∃ (net : Finset J) (assign : J → J) (I : J → Set ℝ),
        net ⊆ family ∧ (∀ j ∈ family, assign j ∈ net) ∧
        (∀ j ∈ family, I j = Set.Icc (0:ℝ) (1/4) ∨ I j = Set.Icc (3/4:ℝ) 1) ∧
        (∀ x, weightedOverlap net (assignedTubePieces family assign b v I r)
          (fun _ => (1:ℝ)) x ≤ B) := by
  obtain ⟨B, hB⟩ := uniform_shortened_piece_overlap (X:=X) (16*(C+4)/c) (by positivity)
  refine ⟨B, ?_⟩
  intro H hH p J family b v r s hne hr hs hrs hv hmeet
  obtain ⟨net, assign, hsub, hunit, hsep, hassign⟩ := normal_plane_net H family hne v
    (fun j hj => (mul_pos hc hs).trans_le (hv j hj).1) (r/s) (div_pos hr hs)
  have hex : ∀ j : J, ∃ I : Set ℝ, j ∈ family →
      (I = Set.Icc (0:ℝ) (1/4) ∨ I = Set.Icc (3/4:ℝ) 1) ∧
      ∀ t ∈ I, ∀ x, dist x (segmentPoint (b j) (v j) t) ≤ r →
        x ∉ Metric.thickening (c*s/16) (affinePlane H p) := by
    intro j
    by_cases hj : j ∈ family
    · obtain ⟨I, hI, hout⟩ := shortened_tube_outside_plane H (b j) (v j) p (c*s) r (mul_pos hc hs) (hv j hj).1 hrs
      exact ⟨I, fun _ => ⟨hI, hout⟩⟩
    · exact ⟨∅, fun h => (hj h).elim⟩
  choose I hI using hex
  refine ⟨net, assign, I, hsub, fun j hj => (hassign j hj).1,
    fun j hj => (hI j hj).1, ?_⟩
  apply hB (fun x => normalProjection H (x-p)) net (fun j => normalDirection H (v j))
    _ (r/s) (c*s/16) (div_pos hr hs) (by positivity) (fun j hj => (hunit j hj).1) hsep
  intro k hk x hx
  obtain ⟨j, hj, hx⟩ := Set.mem_iUnion₂.mp hx
  obtain ⟨hj, haj⟩ := Finset.mem_filter.mp hj
  obtain ⟨y, ⟨t, ht, rfl⟩, hxt⟩ := Metric.mem_thickening_iff.mp hx
  have ht01 : t ∈ Set.Icc (0:ℝ) 1 := by
    rcases (hI j hj).1 with h | h <;> rw [h] at ht <;> constructor <;> linarith [ht.1, ht.2]
  have hout := (hI j hj).2 t ht x hxt.le
  refine ⟨le_of_not_gt (fun h => hout ((mem_plane_thickening_iff H p x _).mpr h)), ?_⟩
  obtain ⟨t₀, ht₀, hbase⟩ := hmeet j hj
  have hclose := (hassign j hj).2
  rw [haj] at hclose
  have hnear := high_band_tube_containment H p (normalDirection H (v k)) (b j) (v j)
    x t t₀ r s (C*r) ((C+4)*r) (hunit k hk).2 ht01 ht₀ hs hr.le
    ((mul_pos hc hs).trans_le (hv j hj).1) (hv j hj).2 hbase (hclose.imp le_of_lt le_of_lt) hxt.le (by nlinarith)
  obtain ⟨c, hc⟩ := (mem_extendedPlane_thickening_iff H p _ x _ (hunit k hk).2).mp hnear
  refine ⟨c, hc.le.trans_eq ?_⟩
  field_simp

/-- The source angle band supplies the speed hypotheses with universal
Jordan constants; r<=s/(8*pi) guarantees the fixed quarter shortening. -/
theorem construct_angle_brush_pieces (C : ℝ) (hC : 0 ≤ C) :
    ∃ B : ℕ, ∀ (H : Submodule ℝ X) [H.HasOrthogonalProjection]
      (p : X) {J : Type*} (family : Finset J) (b v : J → X) (r s : ℝ),
      family.Nonempty → 0 < r → 0 < s → r ≤ s/(8*Real.pi) →
      (∀ j ∈ family, ‖v j‖ = 1 ∧ s ≤ planeAngle H (v j) ∧ planeAngle H (v j) ≤ 2*s) →
      (∀ j ∈ family, ∃ t ∈ Set.Icc (0:ℝ) 1,
        ‖normalProjection H (segmentPoint (b j) (v j) t-p)‖ ≤ C*r) →
      ∃ (net : Finset J) (assign : J → J) (I : J → Set ℝ),
        net ⊆ family ∧ (∀ j ∈ family, assign j ∈ net) ∧
        (∀ j ∈ family, I j = Set.Icc (0:ℝ) (1/4) ∨ I j = Set.Icc (3/4:ℝ) 1) ∧
        (∀ x, weightedOverlap net (assignedTubePieces family assign b v I r)
          (fun _ => (1:ℝ)) x ≤ B) := by
  obtain ⟨B, hB⟩ := construct_brush_pieces (X:=X) C (2/Real.pi) hC (by positivity)
  refine ⟨B, ?_⟩
  intro H hH p J family b v r s hne hr hs hrs hv hmeet
  apply hB H p family b v r s hne hr hs _ _ hmeet
  · convert hrs using 1; ring
  · intro j hj
    have hb := planeAngle_speed_bounds H (v j) (hv j hj).1
    exact ⟨(mul_le_mul_of_nonneg_left (hv j hj).2.1 (by positivity)).trans hb.1,
      hb.2.trans (hv j hj).2.2⟩

omit [ProperSpace X] in
/-- These assigned tube unions are open, with no measurability premise. -/
theorem assignedTubePieces_open {J : Type*} (family : Finset J) (assign : J → J)
    (b v : J → X) (I : J → Set ℝ) (r : ℝ) (k : J) :
    IsOpen (assignedTubePieces family assign b v I r k) :=
  isOpen_iUnion fun _ => isOpen_iUnion fun _ => Metric.isOpen_thickening

omit [ProperSpace X] in
/-- Assignment preserves the union of every chosen shortened tube. -/
theorem assignedTubePieces_union {J : Type*} (family net : Finset J) (assign : J → J)
    (b v : J → X) (I : J → Set ℝ) (r : ℝ)
    (hassign : ∀ j ∈ family, assign j ∈ net) :
    (⋃ k ∈ net, assignedTubePieces family assign b v I r k) =
      ⋃ j ∈ family, Metric.thickening r (segmentPoint (b j) (v j) '' I j) := by
  ext x
  constructor
  · intro hx
    obtain ⟨k, _, hx⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨j, hj, hx⟩ := Set.mem_iUnion₂.mp hx
    exact Set.mem_iUnion₂.mpr ⟨j, (Finset.mem_filter.mp hj).1, hx⟩
  · intro hx
    obtain ⟨j, hj, hx⟩ := Set.mem_iUnion₂.mp hx
    apply Set.mem_iUnion₂.mpr
    refine ⟨assign j, hassign j hj, ?_⟩
    exact Set.mem_iUnion₂.mpr ⟨j, Finset.mem_filter.mpr ⟨hj, rfl⟩, hx⟩

end KakeyaTwoScale
#print axioms KakeyaTwoScale.construct_brush_pieces

#print axioms KakeyaTwoScale.uniform_plane_region_overlap

#print axioms KakeyaTwoScale.construct_angle_brush_pieces
#print axioms KakeyaTwoScale.assignedTubePieces_open

#print axioms KakeyaTwoScale.assignedTubePieces_union
