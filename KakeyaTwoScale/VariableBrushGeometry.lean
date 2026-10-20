module
public import KakeyaTwoScale.BrushCaptureGeometry

@[expose] public section

open InnerProductGeometry
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
open Classical

/-- Exact common-point overlap for variable axis lengths. No length bound is
needed for the two-point line localization; original directions and weights
are retained. -/
theorem variable_euclidean_brush_overlap (d : ℕ) (h : ℝ) (hh : 0 < h) :
    ∃ N : ℕ, ∀ {J : Type*} (G : Finset J)
      (b u : J → EuclideanSpace ℝ (Fin d)) (ell w : J → ℝ) (r B : ℝ),
      0 < r → 0 ≤ B → (∀ j ∈ G, 0 ≤ w j) → (∀ j ∈ G, ‖u j‖=1) →
      (∀ v : EuclideanSpace ℝ (Fin d), ‖v‖=1 →
        (∑ j ∈ G.filter (fun j => Real.arccos |inner ℝ (u j) v| ≤ r), w j) ≤ B) →
      ∀ p x, (∀ j ∈ G, p ∈ euclideanTube (b j) (ell j • u j) r) → h ≤ dist x p →
      weightedOverlap G (fun j => euclideanTube (b j) (ell j • u j) r) w x ≤ 2*B*N := by
  obtain ⟨N,hN⟩ := uniform_separated_line_overlap
    (X:=EuclideanSpace ℝ (Fin d)) (Real.pi/h) (by positivity)
  refine ⟨N,?_⟩
  intro J G b u ell w r B hr hB hw hu hcap p x hp hx
  let A := G.filter (fun j => x ∈ euclideanTube (b j) (ell j • u j) r)
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
    obtain ⟨t,ht⟩ := tube_two_point_near_line (b j) (ell j • u j) p x
      (hp j (hAG (hSA hj))) (Finset.mem_filter.mp (hSA hj)).2
    exact ⟨t*ell j,by simpa only [smul_smul] using ht⟩
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
  have he : weightedOverlap G (fun j => euclideanTube (b j) (ell j • u j) r) w x = ∑ j ∈ A, w j := by
    simp [weightedOverlap,A,Finset.sum_filter,Set.indicator]
  rw [he]
  exact hweight.trans hwcard


/-- A variable-length capsule through the actual point p lies near the plane.
The original axis is never extended or replaced by a captured subsegment. -/
theorem variable_euclideanTube_near_plane {d : ℕ}
    (H : Submodule ℝ (EuclideanSpace ℝ (Fin d))) [H.HasOrthogonalProjection]
    (b u p : EuclideanSpace ℝ (Fin d)) (ell L C r : ℝ)
    (hell : 0 ≤ ell) (hellL : ell ≤ L) (hr : 0 < r)
    (hu : ‖u‖=1) (hp : p ∈ euclideanTube b (ell • u) r)
    (ha : planeAngle H u ≤ C*r) :
    euclideanTube b (ell • u) r ⊆ Metric.thickening ((L*C+3)*r) (affinePlane H p) := by
  obtain ⟨s,hs,hp⟩ := hp
  intro x hx
  obtain ⟨t,ht,hx⟩ := hx
  have he : x-p=(x-(b+t • (ell • u)))+((t-s)*ell) • u+((b+s • (ell • u))-p) := by
    simp only [sub_smul,mul_smul]
    abel
  have hfirst : ‖normalProjection H (x-(b+t • (ell • u)))‖ ≤ r :=
    (Hᗮ.norm_starProjection_apply_le _).trans (by simpa [dist_eq_norm] using hx.le)
  have hlast : ‖normalProjection H ((b+s • (ell • u))-p)‖ ≤ r :=
    (Hᗮ.norm_starProjection_apply_le _).trans (by simpa [dist_eq_norm,norm_sub_rev] using hp.le)
  have hts : |t-s| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1,hs.2],by linarith [ht.2,hs.1]⟩
  have hscalar : |(t-s)*ell| ≤ L := by
    rw [abs_mul,abs_of_nonneg hell]
    exact (mul_le_of_le_one_left hell hts).trans hellL
  have hmiddle : ‖normalProjection H (((t-s)*ell) • u)‖ ≤ L*(C*r) := by
    rw [map_smul,norm_smul,Real.norm_eq_abs]
    exact mul_le_mul hscalar ((planeAngle_speed_bounds H u hu).2.trans ha)
      (norm_nonneg _) (hell.trans hellL)
  apply (mem_plane_thickening_iff H p x _).mpr
  rw [he,map_add,map_add]
  have htri := norm_add_le (normalProjection H (x-(b+t • (ell • u)))+
    normalProjection H (((t-s)*ell) • u)) (normalProjection H ((b+s • (ell • u))-p))
  have htri' := norm_add_le (normalProjection H (x-(b+t • (ell • u))))
    (normalProjection H (((t-s)*ell) • u))
  nlinarith

end KakeyaTwoScale
#print axioms KakeyaTwoScale.variable_euclidean_brush_overlap
#print axioms KakeyaTwoScale.variable_euclideanTube_near_plane
