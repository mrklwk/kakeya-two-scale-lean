module
public import KakeyaTwoScale.BrushPieces

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [ProperSpace X]

/-- The existing constructive brush proof, retaining the actual unit-normal
net and assignment witnesses needed for the sharp plane-weight estimate. -/
theorem construct_brush_pieces_with_net (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c) :
    ∃ B : ℕ, ∀ (H : Submodule ℝ X) [H.HasOrthogonalProjection]
      (p : X) {J : Type*} (family : Finset J) (b v : J → X) (r s : ℝ),
      family.Nonempty → 0 < r → 0 < s → r ≤ c*s/16 →
      (∀ j ∈ family, c*s ≤ ‖normalProjection H (v j)‖ ∧ ‖normalProjection H (v j)‖ ≤ 2*s) →
      (∀ j ∈ family, ∃ t ∈ Set.Icc (0:ℝ) 1,
        ‖normalProjection H (segmentPoint (b j) (v j) t-p)‖ ≤ C*r) →
      ∃ (net : Finset J) (assign : J → J) (I : J → Set ℝ),
        net ⊆ family ∧ (∀ j ∈ family, assign j ∈ net) ∧
        (∀ j ∈ net, ‖normalDirection H (v j)‖=1 ∧ normalDirection H (v j) ∈ Hᗮ) ∧
        (∀ j ∈ family, dist (normalDirection H (v j)) (normalDirection H (v (assign j))) ≤ r/s ∨
          dist (normalDirection H (v j)) (-normalDirection H (v (assign j))) ≤ r/s) ∧
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
  refine ⟨net, assign, I, hsub, (fun j hj => (hassign j hj).1), hunit,
    (fun j hj => (hassign j hj).2.imp le_of_lt le_of_lt),
    (fun j hj => (hI j hj).1), ?_⟩
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
theorem construct_angle_brush_pieces_with_net (C : ℝ) (hC : 0 ≤ C) :
    ∃ B : ℕ, ∀ (H : Submodule ℝ X) [H.HasOrthogonalProjection]
      (p : X) {J : Type*} (family : Finset J) (b v : J → X) (r s : ℝ),
      family.Nonempty → 0 < r → 0 < s → r ≤ s/(8*Real.pi) →
      (∀ j ∈ family, ‖v j‖ = 1 ∧ s ≤ planeAngle H (v j) ∧ planeAngle H (v j) ≤ 2*s) →
      (∀ j ∈ family, ∃ t ∈ Set.Icc (0:ℝ) 1,
        ‖normalProjection H (segmentPoint (b j) (v j) t-p)‖ ≤ C*r) →
      ∃ (net : Finset J) (assign : J → J) (I : J → Set ℝ),
        net ⊆ family ∧ (∀ j ∈ family, assign j ∈ net) ∧
        (∀ j ∈ net, ‖normalDirection H (v j)‖=1 ∧ normalDirection H (v j) ∈ Hᗮ) ∧
        (∀ j ∈ family, dist (normalDirection H (v j)) (normalDirection H (v (assign j))) ≤ r/s ∨
          dist (normalDirection H (v j)) (-normalDirection H (v (assign j))) ≤ r/s) ∧
        (∀ j ∈ family, I j = Set.Icc (0:ℝ) (1/4) ∨ I j = Set.Icc (3/4:ℝ) 1) ∧
        (∀ x, weightedOverlap net (assignedTubePieces family assign b v I r)
          (fun _ => (1:ℝ)) x ≤ B) := by
  obtain ⟨B, hB⟩ := construct_brush_pieces_with_net (X:=X) C (2/Real.pi) hC (by positivity)
  refine ⟨B, ?_⟩
  intro H hH p J family b v r s hne hr hs hrs hv hmeet
  apply hB H p family b v r s hne hr hs _ _ hmeet
  · convert hrs using 1; ring
  · intro j hj
    have hb := planeAngle_speed_bounds H (v j) (hv j hj).1
    exact ⟨(mul_le_mul_of_nonneg_left (hv j hj).2.1 (by positivity)).trans hb.1,
      hb.2.trans (hv j hj).2.2⟩

end KakeyaTwoScale
#print axioms KakeyaTwoScale.construct_brush_pieces_with_net
#print axioms KakeyaTwoScale.construct_angle_brush_pieces_with_net
