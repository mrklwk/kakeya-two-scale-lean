module
public import KakeyaTwoScale.EuclideanTubeSource

@[expose] public section

open InnerProductGeometry
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
open Classical

/-- Both encounters are within the radius of the axis; neither point is
assumed to lie on the axis. The scalar difference may vanish or be negative. -/
theorem tube_two_point_near_line {d : ℕ}
    (b u p x : EuclideanSpace ℝ (Fin d)) {r : ℝ}
    (hp : p ∈ euclideanTube b u r) (hx : x ∈ euclideanTube b u r) :
    ∃ t : ℝ, dist (x-p) (t • u) ≤ 2*r := by
  obtain ⟨s,hs,hp⟩ := hp
  obtain ⟨t,ht,hx⟩ := hx
  refine ⟨t-s,?_⟩
  have hh := dist_sub_sub_le x p (b+t • u) (b+s • u)
  have he : (b+t • u)-(b+s • u)=(t-s) • u := by rw [sub_smul]; abel
  rw [he] at hh
  linarith

/-- Exact source unoriented cap bounds imply the oriented open-cap bounds
used by the already proved separated extraction. No weight is changed. -/
theorem source_cap_to_oriented {d : ℕ} {J : Type*} (G : Finset J)
    (u : J → EuclideanSpace ℝ (Fin d)) (w : J → ℝ) (r B : ℝ)
    (hw : ∀ j ∈ G, 0 ≤ w j) (hu : ∀ j ∈ G, ‖u j‖=1)
    (hcap : ∀ v : EuclideanSpace ℝ (Fin d), ‖v‖=1 →
      (∑ j ∈ G.filter (fun j => Real.arccos |inner ℝ (u j) v| ≤ r), w j) ≤ B) :
    ∀ v : EuclideanSpace ℝ (Fin d), ‖v‖=1 →
      (∑ j ∈ G.filter (fun j => angle (u j) v < r), w j) ≤ B := by
  intro v hv
  apply le_trans _ (hcap v hv)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro j hj
    obtain ⟨hj,ha⟩ := Finset.mem_filter.mp hj
    have hh := ((source_angle_separation_iff (u j) v (hu j hj) hv
      (Real.arccos |inner ℝ (u j) v|)).mp le_rfl).1
    exact Finset.mem_filter.mpr ⟨hj,hh.trans ha.le⟩
  · intro j hj _
    exact hw j (Finset.mem_filter.mp hj).1

/-- The actual weighted overlap of tubes through p is uniformly bounded
outside its fixed-radius ball. The constant precedes all tube widths and
families, and the cap condition is exactly the source angular convention. -/
theorem euclidean_brush_overlap (d : ℕ) (h : ℝ) (hh : 0 < h) :
    ∃ N : ℕ, ∀ {J : Type*} (G : Finset J)
      (b u : J → EuclideanSpace ℝ (Fin d)) (w : J → ℝ) (r B : ℝ),
      0 < r → 0 ≤ B → (∀ j ∈ G, 0 ≤ w j) → (∀ j ∈ G, ‖u j‖=1) →
      (∀ v : EuclideanSpace ℝ (Fin d), ‖v‖=1 →
        (∑ j ∈ G.filter (fun j => Real.arccos |inner ℝ (u j) v| ≤ r), w j) ≤ B) →
      ∀ p x, (∀ j ∈ G, p ∈ euclideanTube (b j) (u j) r) → h ≤ dist x p →
      weightedOverlap G (fun j => euclideanTube (b j) (u j) r) w x ≤ 2*B*N := by
  obtain ⟨N,hN⟩ := uniform_separated_line_overlap
    (X:=EuclideanSpace ℝ (Fin d)) (Real.pi/h) (by positivity)
  refine ⟨N,?_⟩
  intro J G b u w r B hr hB hw hu hcap p x hp hx
  let A := G.filter (fun j => x ∈ euclideanTube (b j) (u j) r)
  have hAG : A ⊆ G := Finset.filter_subset _ _
  have hcapA : ∀ v : EuclideanSpace ℝ (Fin d), ‖v‖=1 →
      (∑ j ∈ A.filter (fun j => angle (u j) v < r), w j) ≤ B := by
    intro v hv
    apply le_trans _ (source_cap_to_oriented G u w r B hw hu hcap v hv)
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro j hj
      obtain ⟨hj,ha⟩ := Finset.mem_filter.mp hj
      exact Finset.mem_filter.mpr ⟨hAG hj,ha⟩
    · intro j hj _
      exact hw j (Finset.mem_filter.mp hj).1
  obtain ⟨S,hSA,hsep,hweight⟩ := angular_weight_separated_extraction A u w r B hr
    (fun j hj => hw j (hAG hj)) (fun j hj => hu j (hAG hj)) hcapA
  have hex : ∀ j ∈ S, ∃ t : ℝ, dist (x-p) (t • u j) ≤ 2*r := by
    intro j hj
    exact tube_two_point_near_line (b j) (u j) p x (hp j (hAG (hSA hj)))
      (Finset.mem_filter.mp (hSA hj)).2
  let t := fun j => if hj : j ∈ S then Classical.choose (hex j hj) else 0
  have ht : ∀ j ∈ S, dist (x-p) (t j • u j) ≤ (Real.pi/h)*(2*r/Real.pi)*h := by
    intro j hj
    have he : (Real.pi/h)*(2*r/Real.pi)*h=2*r := by field_simp
    rw [he]
    dsimp [t]; rw [dite_eq_left hj]
    exact Classical.choose_spec (hex j hj)
  have hcard := hN (2*r/Real.pi) h (by positivity) hh (x-p)
    (by simpa [dist_eq_norm] using hx) S u t
    (fun j hj => hu j (hAG (hSA hj))) ht
    (fun j hj k hk hne => ⟨(hsep j hj k hk hne).1,(hsep j hj k hk hne).2.1⟩)
  have hwcard : 2*B*(S.card:ℝ) ≤ 2*B*(N:ℝ) :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) (by positivity)
  have he : weightedOverlap G (fun j => euclideanTube (b j) (u j) r) w x = ∑ j ∈ A, w j := by
    simp [weightedOverlap,A,Finset.sum_filter,Set.indicator]
  rw [he]
  exact hweight.trans hwcard

end KakeyaTwoScale
#print axioms KakeyaTwoScale.tube_two_point_near_line
#print axioms KakeyaTwoScale.source_cap_to_oriented
#print axioms KakeyaTwoScale.euclidean_brush_overlap
