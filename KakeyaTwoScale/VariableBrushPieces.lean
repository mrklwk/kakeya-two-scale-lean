module
public import KakeyaTwoScale.RefinedBrushPieces
public import KakeyaTwoScale.BrushVolumeTools

@[expose] public section

open MeasureTheory
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
open Classical

 theorem normalDirection_pos_smul {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (H : Submodule ℝ X) [H.HasOrthogonalProjection] (u : X) {l : ℝ} (hl : 0<l) :
    normalDirection H (l • u)=normalDirection H u := by
  simp only [normalDirection,map_smul,norm_smul,Real.norm_eq_abs,abs_of_pos hl,
    mul_inv_rev,smul_smul]
  congr 1
  field_simp

 theorem short_capsule_subset_variable_quarter {d : ℕ}
    (b u : EuclideanSpace ℝ (Fin d)) (I : Set ℝ) (r l : ℝ) (hl : 1≤l)
    (hI : I=Set.Icc (0:ℝ) (1/4) ∨ I=Set.Icc (3/4:ℝ) 1) :
    euclideanTube (b+quarterStart I • (l • u)) ((1/4:ℝ) • u) r ⊆
      Metric.thickening r (segmentPoint b (l • u) '' I) := by
  intro x hx
  obtain ⟨t,ht,hx⟩ := hx
  have hlp : 0<l := by linarith
  have hsmall : 0≤t/(4*l) ∧ t/(4*l)≤1/4 := by
    constructor
    · exact div_nonneg ht.1 (by positivity)
    · apply (div_le_iff₀ (by positivity)).mpr
      nlinarith [ht.2]
  have hparam : quarterStart I+t/(4*l) ∈ I := by
    rcases hI with hI|hI
    · simpa [hI,quarterStart] using hsmall
    · have hne : Set.Icc (3/4:ℝ) 1 ≠ Set.Icc (0:ℝ) (1/4) := by
        intro he
        have h : (0:ℝ)∈Set.Icc (3/4:ℝ) 1 := by rw [he]; norm_num
        norm_num at h
      simp only [hI,quarterStart,ite_eq_right hne,Set.mem_Icc]
      constructor <;> linarith [hsmall.1,hsmall.2]
  refine Metric.mem_thickening_iff.mpr ⟨_,⟨_,hparam,rfl⟩,?_⟩
  have he : segmentPoint b (l • u) (quarterStart I+t/(4*l))=
      (b+quarterStart I • (l • u))+t • ((1/4:ℝ) • u) := by
    unfold segmentPoint
    simp only [smul_smul]
    have heq : (quarterStart I+t/(4*l))*l=quarterStart I*l+t*(1/4) := by field_simp
    rw [heq,add_smul]
    abel
  rwa [he]

 theorem variable_quarter_plane_weighted_volume (n k : ℕ) (R L B C : ℝ)
    (hR : 0≤R) (hL : 1≤L) (hB : 0<B) (hC : 0≤C) :
    ∃ c : ℝ, 0<c ∧
      ∀ (H : Submodule ℝ (EuclideanSpace ℝ (Fin (n+1)))) [H.HasOrthogonalProjection],
      Module.finrank ℝ H=k+1 → ∀ r : ℝ, 0<r → r≤1 →
      ∀ {J : Type*} (G : Finset J) (b u : J → EuclideanSpace ℝ (Fin (n+1)))
        (ell w : J → ℝ) (I : J → Set ℝ),
      (∀ j∈G, 1≤ell j ∧ ell j≤L) →
      (∀ j∈G, I j=Set.Icc (0:ℝ) (1/4) ∨ I j=Set.Icc (3/4:ℝ) 1) →
      (∀ j∈G, ‖b j‖≤R) → (∀ j∈G, ‖u j‖=1) → (∀ j∈G, 0≤w j) →
      (∀ j∈G, planeAngle H (u j)≤C*r) →
      (∀ v : EuclideanSpace ℝ (Fin (n+1)), ‖v‖=1 →
        (∑ j∈G.filter (fun j => Real.arccos |inner ℝ (u j) v|≤r),w j)≤B) →
      c*r^n*(r^k)^theta*(∑ j∈G,w j)≤
        volume.real (⋃ j∈G,Metric.thickening r (segmentPoint (b j) (ell j • u j) '' I j)) := by
  obtain ⟨c,hc,hvol⟩ := plane_weighted_capsule_volume n k (R+L) (1/4) B C
    (by linarith) (by norm_num) (by norm_num) hB hC
  refine ⟨c,hc,?_⟩
  intro H instH hdim r hr hrone J G b u ell w I hell hI hb hu hw ha hcap
  let b' := fun j => b j+quarterStart (I j) • (ell j • u j)
  have hb' : ∀ j∈G, ‖b' j‖≤R+L := by
    intro j hj
    have hq := quarterStart_bounds (I j)
    have he0 : 0≤ell j := by linarith [(hell j hj).1]
    have hh := norm_add_le (b j) (quarterStart (I j) • (ell j • u j))
    simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg hq.1,abs_of_nonneg he0,hu j hj,mul_one] at hh
    have hmul := mul_le_mul_of_nonneg_right hq.2 he0
    dsimp [b']
    nlinarith [hb j hj,(hell j hj).2]
  have hh := hvol H hdim r hr hrone G b' u w hb' hu hw ha hcap
  apply hh.trans
  apply measureReal_mono
  · intro x hx
    obtain ⟨j,hj,hx⟩ := Set.mem_iUnion₂.mp hx
    exact Set.mem_iUnion₂.mpr ⟨j,hj,short_capsule_subset_variable_quarter (b j) (u j) (I j) r (ell j) (hell j hj).1 (hI j hj) hx⟩
  · apply measure_ne_top_of_subset _ (euclideanTube_union_finite G b (fun j => ell j • u j) r)
    intro x hx
    obtain ⟨j,hj,hx⟩ := Set.mem_iUnion₂.mp hx
    exact Set.mem_iUnion₂.mpr ⟨j,hj,quarter_piece_subset_tube (b j) (ell j • u j) (I j) r (hI j hj) hx⟩

end KakeyaTwoScale
#print axioms KakeyaTwoScale.normalDirection_pos_smul
#print axioms KakeyaTwoScale.short_capsule_subset_variable_quarter
#print axioms KakeyaTwoScale.variable_quarter_plane_weighted_volume
