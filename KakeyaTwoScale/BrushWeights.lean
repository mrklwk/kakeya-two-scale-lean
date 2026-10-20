module
public import KakeyaTwoScale.BrushPieces

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
open Classical

/-- The weight of an actual assignment fiber, without rounded multiplicities. -/
def assignedWeight {J K : Type*} (family : Finset J) (assign : J → K)
    (w : J → ℝ) (k : K) : ℝ :=
  ∑ j ∈ family.filter (fun j => assign j = k), w j

/-- Every original weight occurs in exactly one assigned plane. -/
theorem assignedWeight_total {J K : Type*} (family : Finset J) (net : Finset K)
    (assign : J → K) (w : J → ℝ) (hassign : ∀ j ∈ family, assign j ∈ net) :
    ∑ k ∈ net, assignedWeight family assign w k = ∑ j ∈ family, w j :=
  Finset.sum_fiberwise_of_maps_to hassign w

/-- Weighted extraction constructs a subfamily; no separation certificate is
assumed. Ordinary balls around both signs cost exactly the factor two. -/
theorem weighted_projective_extraction {X J : Type*} [NormedAddCommGroup X]
    (family : Finset J) (a : J → X) (w : J → ℝ) (epsilon B : ℝ)
    (he : 0 < epsilon) (hw : ∀ j ∈ family, 0 ≤ w j)
    (hcap : ∀ k ∈ family,
      (∑ j ∈ family.filter (fun j => dist (a j) (a k) < epsilon), w j) ≤ B ∧
      (∑ j ∈ family.filter (fun j => dist (a j) (-a k) < epsilon), w j) ≤ B) :
    ∃ selected : Finset J, selected ⊆ family ∧
      (∀ j ∈ selected, ∀ k ∈ selected, j ≠ k →
        epsilon ≤ dist (a j) (a k) ∧ epsilon ≤ dist (a j) (-a k)) ∧
      (∑ j ∈ family, w j) ≤ 2*B*(selected.card : ℝ) := by
  by_cases hne : family.Nonempty
  · obtain ⟨net, assign, hsub, hsep, hassign⟩ :=
      finite_projective_net_assignment family hne a epsilon he
    refine ⟨net, hsub, hsep, ?_⟩
    rw [← assignedWeight_total family net assign w (fun j hj => (hassign j hj).1)]
    calc
      _ ≤ ∑ k ∈ net, (2*B) := by
        apply Finset.sum_le_sum
        intro k hk
        have hfiber : assignedWeight family assign w k ≤
            (∑ j ∈ family.filter (fun j => dist (a j) (a k) < epsilon), w j) +
            (∑ j ∈ family.filter (fun j => dist (a j) (-a k) < epsilon), w j) := by
          unfold assignedWeight
          rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
          apply Finset.sum_le_sum
          intro j hj
          by_cases ha : assign j = k
          · have hclose := (hassign j hj).2
            rw [ha] at hclose
            rcases hclose with hp | hn
            · simp only [ha, hp, ite_eq_left]
              split_ifs <;> linarith [hw j hj]
            · simp only [ha, hn, ite_eq_left]
              split_ifs <;> linarith [hw j hj]
          · simp only [ha, ite_false]
            split_ifs <;> linarith [hw j hj]
        linarith [(hcap k (hsub hk)).1, (hcap k (hsub hk)).2]
      _ = _ := by simp; ring
  · refine ⟨∅, Finset.empty_subset _, ?_, ?_⟩
    · simp
    · simp [Finset.not_nonempty_iff_eq_empty.mp hne]

/-- A local direction cap on the original family is inherited by every
concretely assigned plane, and yields a separated tube subcollection there. -/
theorem assigned_weight_separated_extraction {X J K : Type*} [NormedAddCommGroup X]
    (family : Finset J) (assign : J → K) (a : J → X) (w : J → ℝ)
    (epsilon B : ℝ) (he : 0 < epsilon) (hw : ∀ j ∈ family, 0 ≤ w j)
    (hunit : ∀ j ∈ family, ‖a j‖ = 1)
    (hcap : ∀ x : X, ‖x‖ = 1 →
      (∑ j ∈ family.filter (fun j => dist (a j) x < epsilon), w j) ≤ B)
    (k : K) :
    ∃ selected : Finset J, selected ⊆ family.filter (fun j => assign j = k) ∧
      (∀ j ∈ selected, ∀ l ∈ selected, j ≠ l →
        epsilon ≤ dist (a j) (a l) ∧ epsilon ≤ dist (a j) (-a l)) ∧
      assignedWeight family assign w k ≤ 2*B*(selected.card : ℝ) := by
  apply weighted_projective_extraction _ a w epsilon B he
    (fun j hj => hw j (Finset.mem_filter.mp hj).1)
  intro l hl
  have hlocal (x : X) (hx : ‖x‖ = 1) :
      (∑ j ∈ (family.filter (fun j => assign j = k)).filter
        (fun j => dist (a j) x < epsilon), w j) ≤ B := by
    apply le_trans _ (hcap x hx)
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro j hj
      obtain ⟨hj, hd⟩ := Finset.mem_filter.mp hj
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj).1, hd⟩
    · intro j hj _
      exact hw j (Finset.mem_filter.mp hj).1
  have hu := hunit l (Finset.mem_filter.mp hl).1
  exact ⟨hlocal (a l) hu, hlocal (-a l) (by simpa using hu)⟩

/-- For unit directions only unit-centered caps are needed, exactly as in
the source spherical weight hypothesis. Separation here uses chord distance. -/
theorem weighted_unit_direction_extraction {X J : Type*} [NormedAddCommGroup X]
    (family : Finset J) (a : J → X) (w : J → ℝ) (epsilon B : ℝ)
    (he : 0 < epsilon) (hw : ∀ j ∈ family, 0 ≤ w j)
    (hunit : ∀ j ∈ family, ‖a j‖ = 1)
    (hcap : ∀ x : X, ‖x‖ = 1 →
      (∑ j ∈ family.filter (fun j => dist (a j) x < epsilon), w j) ≤ B) :
    ∃ selected : Finset J, selected ⊆ family ∧
      (∀ j ∈ selected, ∀ k ∈ selected, j ≠ k →
        epsilon ≤ dist (a j) (a k) ∧ epsilon ≤ dist (a j) (-a k)) ∧
      (∑ j ∈ family, w j) ≤ 2*B*(selected.card : ℝ) := by
  apply weighted_projective_extraction family a w epsilon B he hw
  intro k hk
  exact ⟨hcap (a k) (hunit k hk), hcap (-a k) (by simpa using hunit k hk)⟩

/-- Every tube chosen from an assignment fiber is literally contained in its
assigned shortened union; extraction does not move axes or change intervals. -/
theorem selected_tube_union_subset_assigned {X J : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (family selected : Finset J) (assign : J → J) (b v : J → X)
    (I : J → Set ℝ) (r : ℝ) (k : J)
    (hsub : selected ⊆ family.filter (fun j => assign j = k)) :
    (⋃ j ∈ selected, Metric.thickening r (segmentPoint (b j) (v j) '' I j)) ⊆
      assignedTubePieces family assign b v I r k := by
  intro x hx
  obtain ⟨j, hj, hx⟩ := Set.mem_iUnion₂.mp hx
  exact Set.mem_iUnion₂.mpr ⟨j, hsub hj, hx⟩

/-- Exact conversion of the constructed extraction count into a weighted
power bound. This is algebra, not the arithmetic tube-volume theorem. -/
theorem extracted_weight_power (W B N a : ℝ) (hW : 0 ≤ W)
    (hB : 0 ≤ B) (hN : 0 ≤ N) (ha : 0 ≤ a) (hcount : W ≤ 2*B*N) :
    W^a ≤ (2*B)^a * N^a := by
  calc
    _ ≤ (2*B*N)^a := Real.rpow_le_rpow hW hcount ha
    _ = _ := Real.mul_rpow (by positivity) hN

end KakeyaTwoScale
#print axioms KakeyaTwoScale.assignedWeight_total
#print axioms KakeyaTwoScale.weighted_projective_extraction
#print axioms KakeyaTwoScale.assigned_weight_separated_extraction

#print axioms KakeyaTwoScale.selected_tube_union_subset_assigned
#print axioms KakeyaTwoScale.extracted_weight_power

#print axioms KakeyaTwoScale.weighted_unit_direction_extraction
