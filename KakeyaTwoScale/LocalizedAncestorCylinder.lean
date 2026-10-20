module
public import KakeyaTwoScale.CapsuleCylinder
public import KakeyaTwoScale.NeighborhoodRadiusAudit

@[expose] public section

open Metric Set
noncomputable section
namespace KakeyaTwoScale

/-- A length-delta interval inside the parent, with the incidence parameter
strictly inside it even near either parent endpoint. -/
theorem exists_incident_subinterval {L δ t : ℝ} (hδ : 0 < δ)
    (hL : δ ≤ L) (ht0 : 0 < t) (htL : t < L) :
    ∃ s : ℝ, 0 ≤ s ∧ s+δ ≤ L ∧ s < t ∧ t < s+δ := by
  refine ⟨max 0 (min (t-δ/2) (L-δ)),?_⟩
  by_cases h : t-δ/2 ≤ L-δ
  · rw [min_eq_left h]
    by_cases h0 : 0 ≤ t-δ/2
    · rw [max_eq_right h0]
      constructor
      · exact h0
      · constructor <;> [skip; constructor] <;> linarith
    · rw [max_eq_left (le_of_not_ge h0)]
      constructor
      · exact le_rfl
      · constructor <;> [skip; constructor] <;> linarith
  · rw [min_eq_right (le_of_not_ge h),max_eq_right (by linarith : 0 ≤ L-δ)]
    constructor
    · linarith
    · constructor <;> [skip; constructor] <;> linarith

/-- Two points of the same flat cylinder are within length plus two widths.
The orthogonality condition is not needed for this upper bound. -/
theorem flatCylinder_pair_dist_lt {n : ℕ}
    (b u x y : EuclideanSpace ℝ (Fin n)) (L r : ℝ) (hu : ‖u‖=1)
    (hx : x ∈ flatCylinder b u L r) (hy : y ∈ flatCylinder b u L r) :
    dist x y < L+2*r := by
  obtain ⟨t,ht0,htL,_,hxt⟩ := hx
  obtain ⟨s,hs0,hsL,_,hys⟩ := hy
  have hd : dist (b+t • u) (b+s • u) < L := by
    rw [dist_eq_norm,show (b+t • u)-(b+s • u)=(t-s) • u by module,
      norm_smul,Real.norm_eq_abs,hu,mul_one]
    exact abs_lt.mpr ⟨by linarith,by linarith⟩
  have hx' : dist x (b+t • u) < r := hxt
  have hy' : dist (b+s • u) y < r := by simpa [dist_eq_norm,norm_sub_rev] using hys
  have h₁ := dist_triangle x (b+t • u) y
  have h₂ := dist_triangle (b+t • u) (b+s • u) y
  linarith

/-- Construct an actual full-width child, retaining the original incidence
point and staying in its parent. Only that point need be near the new variety.
The new variety need not lie in any old one. -/
theorem exists_incident_localized_cylinder {n : ℕ}
    (b u x : EuclideanSpace ℝ (Fin n)) (V : Set (EuclideanSpace ℝ (Fin n)))
    (L δ A : ℝ) (hu : ‖u‖=1) (hδ : 0 < δ) (hL : δ ≤ L)
    (hx : x ∈ flatCylinder b u L δ) (hV : x ∈ thickening (A*δ) V) :
    ∃ s : ℝ, 0 ≤ s ∧ s+δ ≤ L ∧
      x ∈ flatCylinder (b+s • u) u δ δ ∧
      flatCylinder (b+s • u) u δ δ ⊆
        flatCylinder b u L δ ∩ thickening ((A+3)*δ) V := by
  obtain ⟨t,ht0,htL,hi,hr⟩ := hx
  obtain ⟨s,hs0,hsL,hst,hts⟩ := exists_incident_subinterval hδ hL ht0 htL
  have hxchild : x ∈ flatCylinder (b+s • u) u δ δ := by
    have he : (b+s • u)+(t-s) • u=b+t • u := by module
    exact ⟨t-s,by linarith,by linarith,by simpa only [he] using hi,
      by simpa only [he] using hr⟩
  refine ⟨s,hs0,hsL,hxchild,?_⟩
  intro y hy
  constructor
  · obtain ⟨r,hr0,hrδ,hir,hrr⟩ := hy
    have he : b+(s+r) • u=(b+s • u)+r • u := by module
    exact ⟨s+r,by linarith,by linarith,by simpa only [he] using hir,
      by simpa only [he] using hrr⟩
  · have hh := whole_set_capture_radius (flatCylinder (b+s • u) u δ δ) V
      (A*δ) (3*δ) hV (fun z hz => by
        have hh := flatCylinder_pair_dist_lt (b+s • u) u z x δ δ hu hz hxchild
        linarith)
    have he : A*δ+3*δ=(A+3)*δ := by ring
    rw [← he]
    exact hh hy

end KakeyaTwoScale
#print axioms KakeyaTwoScale.exists_incident_subinterval
#print axioms KakeyaTwoScale.flatCylinder_pair_dist_lt
#print axioms KakeyaTwoScale.exists_incident_localized_cylinder
