module
public import KakeyaTwoScale.MultilinearScale
public import KakeyaTwoScale.FiniteRootIntervals

@[expose] public section

open Set MeasureTheory
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- Equal-width, equally oriented containment forces a coaxial translation. -/
theorem equal_width_cylinder_base {n : ℕ}
    (b c u : EuclideanSpace ℝ (Fin n)) (L l r : ℝ)
    (hu : ‖u‖=1) (hl : 0<l) (hr : 0<r)
    (hsub : flatCylinder c u l r ⊆ flatCylinder b u L r) :
    c = b + (inner ℝ u (c-b)) • u := by
  let a := inner ℝ u (c-b)
  let v := c-b-a • u
  have hiv : inner ℝ u v=0 := by
    dsimp [v,a]
    rw [inner_sub_right,inner_smul_right,real_inner_self_eq_norm_sq,hu]
    ring
  have hpoint (w : EuclideanSpace ℝ (Fin n)) (hw : inner ℝ u w=0) (hn : ‖w‖<r) :
      ‖v+w‖<r := by
    have hc : c+(l/2) • u+w ∈ flatCylinder c u l r := by
      refine ⟨l/2,by linarith,by linarith,?_,?_⟩ <;> simpa using ‹_›
    have h := (mem_flatCylinder_iff_coordinates b u _ L r hu).mp (hsub hc)
    have ha : inner ℝ u (c+(l/2) • u+w-b)=a+l/2 := by
      have he : c+(l/2) • u+w-b=(c-b)+(l/2) • u+w := by module
      rw [he,inner_add_right,inner_add_right,inner_smul_right,hw,
        real_inner_self_eq_norm_sq,hu]
      dsimp [a]; ring
    rw [ha] at h
    convert h.2.2 using 1
    dsimp [v]
    congr 1
    module
  have hv : ‖v‖<r := by simpa using hpoint 0 (by simp) (by simpa using hr)
  have hvzero : v=0 := by
    by_contra hvne
    have hvpos : 0<‖v‖ := norm_pos_iff.mpr hvne
    let q := r/‖v‖-1/2
    have hq : 0<q := by dsimp [q]; have hh : 1<r/‖v‖ := (lt_div_iff₀ hvpos).mpr (by simpa using hv); linarith
    have he : q*‖v‖=r-‖v‖/2 := by dsimp [q]; field_simp
    have hn : ‖q • v‖<r := by rw [norm_smul,Real.norm_eq_abs,abs_of_pos hq,he]; linarith
    have h := hpoint (q • v) (by rw [inner_smul_right,hiv,mul_zero]) hn
    have he2 : v+q • v=(1+q) • v := by module
    rw [he2,norm_smul,Real.norm_eq_abs,abs_of_pos (by linarith : 0<1+q)] at h
    nlinarith
  dsimp [v] at hvzero
  dsimp [a] at hvzero ⊢
  exact ((sub_eq_iff_eq_add).mp (sub_eq_zero.mp hvzero)).trans (add_comm _ _)

/-- The actual axial interval of a contained cylinder lies inside its parent. -/
theorem contained_cylinder_interval {n : ℕ}
    (b c u : EuclideanSpace ℝ (Fin n)) (L l r : ℝ)
    (hu : ‖u‖=1) (hl : 0<l) (hr : 0<r)
    (hsub : flatCylinder c u l r ⊆ flatCylinder b u L r) :
    Ioo (inner ℝ u (c-b)) (inner ℝ u (c-b)+l) ⊆ Ioo (0:ℝ) L := by
  intro t ht
  let a := inner ℝ u (c-b)
  have hc := equal_width_cylinder_base b c u L l r hu hl hr hsub
  have hm : b+t • u ∈ flatCylinder c u l r := by
    refine ⟨t-a,by dsimp [a]; linarith [ht.1],by dsimp [a]; linarith [ht.2],?_,?_⟩
    all_goals rw [hc]; have he : b+t • u-(b+a • u+(t-a) • u)=0 := by module
    all_goals rw [he]
    · simp
    · simpa using hr
  have h := (mem_flatCylinder_iff_coordinates b u _ L r hu).mp (hsub hm)
  have he : inner ℝ u (b+t • u-b)=t := by
    simp only [add_sub_cancel_left,inner_smul_right,real_inner_self_eq_norm_sq,hu]
    ring
  rw [he] at h
  exact ⟨h.1,h.2.1⟩

/-- Disjoint positive-length subcylinders conserve the full parent's axial
length. This is deduplicated physical counting, not incidence counting. -/
theorem disjoint_contained_cylinders_length_sum {n : ℕ} {I : Type*}
    (F : Finset I) (b u : EuclideanSpace ℝ (Fin n))
    (c : I→EuclideanSpace ℝ (Fin n)) (ell : I→ℝ) (L r : ℝ)
    (hu : ‖u‖=1) (hL : 0<L) (hr : 0<r)
    (hell : ∀ i∈F, 0<ell i)
    (hsub : ∀ i∈F, flatCylinder (c i) u (ell i) r ⊆ flatCylinder b u L r)
    (hdis : PairwiseDisjoint (↑F : Set I) (fun i => flatCylinder (c i) u (ell i) r)) :
    (∑ i∈F, ell i) ≤ L := by
  classical
  let a := fun i => inner ℝ u (c i-b)
  have hbase (i) (hi : i∈F) : c i=b+a i • u :=
    equal_width_cylinder_base b (c i) u L (ell i) r hu (hell i hi) hr (hsub i hi)
  have hmem (i) (hi : i∈F) (t : ℝ) (ht : t∈Ioo (a i) (a i+ell i)) :
      b+t • u ∈ flatCylinder (c i) u (ell i) r := by
    refine ⟨t-a i,by linarith [ht.1],by linarith [ht.2],?_,?_⟩
    all_goals rw [hbase i hi]
    all_goals have he : b+t • u-(b+a i • u+(t-a i) • u)=0 := by module
    all_goals rw [he]
    · simp
    · simpa using hr
  have hd : PairwiseDisjoint (↑F : Set I) (fun i => Ioo (a i) (a i+ell i)) := by
    intro i hi j hj hij
    apply Set.disjoint_left.mpr
    intro t hti htj
    exact Set.disjoint_left.mp (hdis hi hj hij) (hmem i hi t hti) (hmem j hj t htj)
  have hs : (⋃ i∈F, Ioo (a i) (a i+ell i)) ⊆ Ioo (0:ℝ) L := by
    intro t ht
    obtain ⟨i,hi,ht⟩ := Set.mem_iUnion₂.mp ht
    exact contained_cylinder_interval b (c i) u L (ell i) r hu (hell i hi) hr (hsub i hi) ht
  have hm := measureReal_mono (μ:=volume) hs (by simp [Real.volume_Ioo])
  rw [measureReal_biUnion_finset hd (fun _ _ => measurableSet_Ioo)
    (fun _ _ => by simp [Real.volume_Ioo]),Real.volume_real_Ioo_of_le hL.le,sub_zero] at hm
  convert hm using 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [Real.volume_real_Ioo_of_le (by linarith [hell i hi])]
  ring

end KakeyaTwoScale
#print axioms KakeyaTwoScale.equal_width_cylinder_base
#print axioms KakeyaTwoScale.contained_cylinder_interval

#print axioms KakeyaTwoScale.disjoint_contained_cylinders_length_sum
