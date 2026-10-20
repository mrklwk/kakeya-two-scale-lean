module
public import KakeyaTwoScale.EuclideanTubeVolume

@[expose] public section

open MeasureTheory InnerProductGeometry
noncomputable section
namespace KakeyaTwoScale

theorem arccos_abs_eq_min (q : ℝ) :
    Real.arccos |q| = min (Real.arccos q) (Real.arccos (-q)) := by
  by_cases h : 0 ≤ q
  · rw [abs_of_nonneg h, min_eq_left (Real.arccos_le_arccos (by linarith))]
  · rw [abs_of_neg (lt_of_not_ge h), min_eq_right (Real.arccos_le_arccos (by linarith))]

theorem source_angle_separation_iff {d : ℕ}
    (u v : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖=1) (hv : ‖v‖=1) (r : ℝ) :
    r ≤ Real.arccos |inner ℝ u v| ↔ r ≤ angle u v ∧ r ≤ angle u (-v) := by
  rw [arccos_abs_eq_min, le_min_iff]
  simp [angle, hu, hv, inner_neg_right]

/-- Source-facing ordinary tube estimate, with literal unoriented angular separation. -/
theorem source_separated_euclidean_tubes_volume (n : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r →
      ∀ {J : Type*} (G : Finset J), G.Nonempty →
      ∀ b u : J → EuclideanSpace ℝ (Fin (n+1)),
      (∀ j ∈ G, ‖b j‖ ≤ R) → (∀ j ∈ G, ‖u j‖=1) →
      (∀ j ∈ G, ∀ k ∈ G, j ≠ k → r ≤ Real.arccos |inner ℝ (u j) (u k)|) →
      C*r^n*(G.card:ℝ)^a ≤ volume.real (⋃ j ∈ G, euclideanTube (b j) (u j) r) := by
  obtain ⟨C,hC,h⟩ := separated_euclidean_tubes_volume n R hR
  refine ⟨C,hC,?_⟩
  intro r hr J G hG b u hb hu hs
  apply h r hr G hG b u hb hu
  intro j hj k hk hjk
  exact (source_angle_separation_iff (u j) (u k) (hu j hj) (hu k hk) r).mp (hs j hj k hk hjk)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.arccos_abs_eq_min
#print axioms KakeyaTwoScale.source_angle_separation_iff
#print axioms KakeyaTwoScale.source_separated_euclidean_tubes_volume
