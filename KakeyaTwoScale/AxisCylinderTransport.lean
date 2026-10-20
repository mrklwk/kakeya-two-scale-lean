module
public import KakeyaTwoScale.CellularCylinderSplit
public import KakeyaTwoScale.LocalizedAncestorCylinder

@[expose] public section

open Set Metric
noncomputable section
namespace KakeyaTwoScale

def axisCylinder {n : ℕ} (b u : EuclideanSpace ℝ (Fin n)) (a : ℝ × ℝ) (δ : ℝ) :=
  flatCylinder (b+a.1 • u) u (a.2-a.1) δ

theorem mem_axisCylinder_iff {n : ℕ} (b u x : EuclideanSpace ℝ (Fin n))
    (a : ℝ × ℝ) (δ : ℝ) :
    x ∈ axisCylinder b u a δ ↔ ∃ t ∈ Ioo a.1 a.2,
      inner ℝ u (x-(b+t • u))=0 ∧ ‖x-(b+t • u)‖ < δ := by
  constructor
  · rintro ⟨s,hs0,hsL,hi,hn⟩
    have he : b+(a.1+s) • u=(b+a.1 • u)+s • u := by module
    exact ⟨a.1+s,⟨by linarith,by linarith⟩,by simpa only [he] using hi,
      by simpa only [he] using hn⟩
  · rintro ⟨t,ht,hi,hn⟩
    have he : (b+a.1 • u)+(t-a.1) • u=b+t • u := by module
    exact ⟨t-a.1,by linarith [ht.1],by linarith [ht.2],
      by simpa only [he] using hi,by simpa only [he] using hn⟩

theorem axisCylinder_subset_parent {n : ℕ} (b u : EuclideanSpace ℝ (Fin n))
    {a : ℝ × ℝ} {L δ : ℝ} (ha : 0 ≤ a.1) (hb : a.2 ≤ L) :
    axisCylinder b u a δ ⊆ flatCylinder b u L δ := by
  intro x hx
  obtain ⟨t,ht,hi,hn⟩ := (mem_axisCylinder_iff b u x a δ).mp hx
  exact ⟨t,by linarith [ht.1],by linarith [ht.2],hi,hn⟩

theorem disjoint_axisCylinders {n : ℕ} (b u : EuclideanSpace ℝ (Fin n))
    (hu : ‖u‖=1) (δ : ℝ) {a c : ℝ × ℝ}
    (hd : Disjoint (Icc a.1 a.2) (Icc c.1 c.2)) :
    Disjoint (axisCylinder b u a δ) (axisCylinder b u c δ) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  obtain ⟨t,ht,hi,_⟩ := (mem_axisCylinder_iff b u x a δ).mp hx
  obtain ⟨s,hs,hj,_⟩ := (mem_axisCylinder_iff b u x c δ).mp hy
  have he := cylinder_parameter_unique b u x hu hi hj
  subst s
  exact Set.disjoint_left.mp hd ⟨ht.1.le,ht.2.le⟩ ⟨hs.1.le,hs.2.le⟩

/-- Full-width geometry from an actual near-source axis parameter; the strict
transverse inequality supplies the open output-neighborhood margin. -/
theorem axisCylinder_near_variety {n : ℕ} (b u : EuclideanSpace ℝ (Fin n))
    (V : Set (EuclideanSpace ℝ (Fin n))) (hu : ‖u‖=1)
    {a : ℝ × ℝ} {δ R : ℝ}
    (hnear : ∀ t ∈ Icc a.1 a.2, ∃ s z, z ∈ V ∧ |t-s| ≤ δ ∧
      dist (b+s • u) z ≤ (R+1)*δ) :
    axisCylinder b u a δ ⊆ thickening ((R+3)*δ) V := by
  intro x hx
  obtain ⟨t,ht,_,hn⟩ := (mem_axisCylinder_iff b u x a δ).mp hx
  obtain ⟨s,z,hz,hst,hsz⟩ := hnear t ⟨ht.1.le,ht.2.le⟩
  have hdist : dist (b+t • u) (b+s • u) ≤ δ := by
    rw [dist_eq_norm,show (b+t • u)-(b+s • u)=(t-s) • u by module,
      norm_smul,Real.norm_eq_abs,hu,mul_one]
    exact hst
  apply mem_thickening_iff.mpr
  refine ⟨z,hz,?_⟩
  have hx' : dist x (b+t • u) < δ := hn
  have h₁ := dist_triangle x (b+t • u) z
  have h₂ := dist_triangle (b+t • u) (b+s • u) z
  linarith

end KakeyaTwoScale
#print axioms KakeyaTwoScale.mem_axisCylinder_iff
#print axioms KakeyaTwoScale.axisCylinder_subset_parent
#print axioms KakeyaTwoScale.disjoint_axisCylinders
#print axioms KakeyaTwoScale.axisCylinder_near_variety
