module
public import KakeyaTwoScale.EqualWidthCylinderAncestry

@[expose] public section

open Set Metric MeasureTheory
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- Disjoint physical components of one original cylinder, localized in one
ball, have a total axial length at most the ball's diameter. -/
theorem localized_original_cylinders_length_sum {n : ℕ} {I : Type*}
    (F : Finset I) (b u center : EuclideanSpace ℝ (Fin n))
    (base : I → EuclideanSpace ℝ (Fin n)) (ell : I → ℝ) (L δ R : ℝ)
    (hu : ‖u‖=1) (hδ : 0<δ) (hR : 0≤R)
    (hell : ∀ i∈F, 0<ell i)
    (hsub : ∀ i∈F, flatCylinder (base i) u (ell i) δ ⊆ flatCylinder b u L δ)
    (hball : ∀ i∈F, flatCylinder (base i) u (ell i) δ ⊆ ball center R)
    (hdis : PairwiseDisjoint (↑F : Set I) (fun i => flatCylinder (base i) u (ell i) δ)) :
    (∑ i∈F, ell i) ≤ 2*R := by
  classical
  let a := fun i => inner ℝ u (base i-b)
  let d := inner ℝ u (center-b)
  have hb (i) (hi : i∈F) : base i=b+a i • u :=
    equal_width_cylinder_base b (base i) u L (ell i) δ hu (hell i hi) hδ (hsub i hi)
  have hm (i) (hi : i∈F) (t : ℝ) (ht : t∈Ioo (a i) (a i+ell i)) :
      b+t • u ∈ flatCylinder (base i) u (ell i) δ := by
    refine ⟨t-a i,by linarith [ht.1],by linarith [ht.2],?_,?_⟩
    all_goals rw [hb i hi]
    all_goals have he : b+t • u-(b+a i • u+(t-a i) • u)=0 := by module
    all_goals rw [he]
    · simp
    · simpa using hδ
  have hd : PairwiseDisjoint (↑F : Set I) (fun i => Ioo (a i) (a i+ell i)) := by
    intro i hi j hj hij
    apply Set.disjoint_left.mpr
    intro t hti htj
    exact Set.disjoint_left.mp (hdis hi hj hij) (hm i hi t hti) (hm j hj t htj)
  have hs : (⋃ i∈F, Ioo (a i) (a i+ell i)) ⊆ Ioo (d-R) (d+R) := by
    intro t ht
    obtain ⟨i,hi,ht⟩ := Set.mem_iUnion₂.mp ht
    have hp := hball i hi (hm i hi t ht)
    change dist (b+t • u) center < R at hp
    have hinner := abs_real_inner_le_norm u (b+t • u-center)
    have he : inner ℝ u (b+t • u-center)=t-d := by
      have hv : b+t • u-center=t • u-(center-b) := by module
      rw [hv,inner_sub_right,inner_smul_right,real_inner_self_eq_norm_sq,hu]
      dsimp [d]
      ring
    rw [he,hu,one_mul,← dist_eq_norm] at hinner
    have ht' := abs_lt.mp (hinner.trans_lt hp)
    exact ⟨by linarith [ht'.1],by linarith [ht'.2]⟩
  have hmeasure := measureReal_mono (μ:=volume) hs (by simp [Real.volume_Ioo])
  rw [measureReal_biUnion_finset hd (fun _ _ => measurableSet_Ioo)
    (fun _ _ => by simp [Real.volume_Ioo]),Real.volume_real_Ioo_of_le (by linarith)] at hmeasure
  have he : (d+R)-(d-R)=2*R := by ring
  rw [he] at hmeasure
  convert hmeasure using 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [Real.volume_real_Ioo_of_le (by linarith [hell i hi])]
  ring

/-- A local multiplicity bound for physical records of one original line;
its constant depends on radius/length, not on inverse scale. -/
theorem localized_original_cylinder_card {n : ℕ} {I : Type*}
    (F : Finset I) (b u center : EuclideanSpace ℝ (Fin n))
    (base : I → EuclideanSpace ℝ (Fin n)) (ell L δ C : ℝ)
    (hu : ‖u‖=1) (hell : 0<ell) (hδ : 0<δ) (hC : 0≤C)
    (hsub : ∀ i∈F, flatCylinder (base i) u ell δ ⊆ flatCylinder b u L δ)
    (hball : ∀ i∈F, flatCylinder (base i) u ell δ ⊆ ball center (C*ell))
    (hdis : PairwiseDisjoint (↑F : Set I) (fun i => flatCylinder (base i) u ell δ)) :
    (F.card:ℝ) ≤ 2*C := by
  have h := localized_original_cylinders_length_sum F b u center base (fun _=>ell)
    L δ (C*ell) hu hδ (mul_nonneg hC hell.le) (fun _ _=>hell) hsub hball hdis
  simp only [Finset.sum_const,nsmul_eq_mul] at h
  exact (mul_le_mul_iff_left₀ hell).mp (by nlinarith)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.localized_original_cylinders_length_sum
#print axioms KakeyaTwoScale.localized_original_cylinder_card
