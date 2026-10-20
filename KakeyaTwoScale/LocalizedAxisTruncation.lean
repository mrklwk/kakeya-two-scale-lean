module
public import KakeyaTwoScale.LocalizedAncestorCylinder
public import KakeyaTwoScale.PolynomialArchiveSnapshot

@[expose] public section

open Set Metric
noncomputable section
namespace KakeyaTwoScale

/-- Concentric truncations preserve a genuinely nested variety flag when
the actual lengths decrease. No neighborhood-volume conclusion is inferred. -/
theorem concentric_truncations_nested {X : Type*} [PseudoMetricSpace X]
    (V W : Set X) (center : X) (R r : ℝ) (hVW : W⊆V) (hr : r≤R) :
    W ∩ closedBall center r ⊆ V ∩ closedBall center R :=
  Set.inter_subset_inter hVW (closedBall_subset_closedBall hr)

/-- An ancestor cylinder meeting a localized descendant supplies an actual
middle-half axis segment near the truncated variety. The truncation has a
positive diameter comparable to the ancestor length. -/
theorem localized_axis_truncation {n : ℕ}
    (b u center w : EuclideanSpace ℝ (Fin n)) (V : Set (EuclideanSpace ℝ (Fin n)))
    (L ell δ rho C : ℝ) (hu : ‖u‖=1) (hL : 0<L) (hδ : 0<δ)
    (hδL : δ≤L) (hell : ell≤L) (hC : 0≤C) (hrho : 8*rho≤L)
    (hw : w∈flatCylinder b u L δ) (hwball : dist w center < C*ell)
    (hcapture : flatCylinder b u L δ ⊆ thickening rho V) :
    let S := V ∩ closedBall center ((C+4)*L)
    (∀ t∈Icc (L/4) (3*L/4), b+t • u∈thickening rho S) ∧
    L/4 ≤ diam S ∧ diam S ≤ 2*(C+4)*L := by
  let S := V ∩ closedBall center ((C+4)*L)
  have hmem (t : ℝ) (ht : t∈Icc (L/4) (3*L/4)) : b+t • u∈flatCylinder b u L δ := by
    refine ⟨t,by linarith [ht.1],by linarith [ht.2],?_,?_⟩
    · simp
    · simpa using hδ
  have hcore (t : ℝ) (ht : t∈Icc (L/4) (3*L/4)) : b+t • u∈thickening rho S := by
    have hd := flatCylinder_pair_dist_lt b u (b+t • u) w L δ hu (hmem t ht) hw
    have hb := dist_triangle (b+t • u) w center
    have hscale : C*ell ≤ C*L := mul_le_mul_of_nonneg_left hell hC
    obtain ⟨z,hz,hdz⟩ := mem_thickening_iff.mp (hcapture (hmem t ht))
    refine mem_thickening_iff.mpr ⟨z,⟨hz,?_⟩,hdz⟩
    have hztri := dist_triangle z (b+t • u) center
    rw [dist_comm z (b+t • u)] at hztri
    change dist z center ≤ (C+4)*L
    nlinarith
  have hbound : Bornology.IsBounded S := isBounded_closedBall.subset inter_subset_right
  have hlow : L/4 ≤ diam S := by
    obtain ⟨z₁,hz₁,hd₁⟩ := mem_thickening_iff.mp (hcore (L/4) ⟨le_rfl,by linarith⟩)
    obtain ⟨z₂,hz₂,hd₂⟩ := mem_thickening_iff.mp (hcore (3*L/4) ⟨by linarith,le_rfl⟩)
    have he : dist (b+(L/4) • u) (b+(3*L/4) • u)=L/2 := by
      rw [dist_eq_norm,show (b+(L/4) • u)-(b+(3*L/4) • u)=(-L/2) • u by module,
        norm_smul,Real.norm_eq_abs,hu,mul_one,abs_of_neg (by linarith : -L/2<0)]
      ring
    have htri := dist_triangle (b+(L/4) • u) z₁ (b+(3*L/4) • u)
    have htri' := dist_triangle z₁ z₂ (b+(3*L/4) • u)
    rw [he] at htri
    rw [dist_comm z₂ (b+(3*L/4) • u)] at htri'
    have hd := dist_le_diam_of_mem hbound hz₁ hz₂
    linarith
  refine ⟨hcore,hlow,?_⟩
  have hd := diam_le_of_subset_closedBall (show 0≤(C+4)*L by positivity)
    (show S⊆closedBall center ((C+4)*L) from inter_subset_right)
  nlinarith

/-- The diameter-normalized line-segment length in the analytic source is
available with an explicit constant after the geometric truncation lemma. -/
theorem diameter_normalized_axis_segment {n : ℕ}
    (b u : EuclideanSpace ℝ (Fin n)) (S : Set (EuclideanSpace ℝ (Fin n)))
    (L rho C : ℝ) (hu : ‖u‖=1) (hL : 0<L) (hC : 0≤C)
    (hlow : L/4≤diam S) (hup : diam S≤2*(C+4)*L)
    (hcore : ∀ t∈Icc (L/4) (3*L/4), b+t • u∈thickening rho S) :
    0<diam S/(4*(C+4)) ∧
    (∀ t∈Icc (L/4) (L/4+diam S/(4*(C+4))), b+t • u∈thickening rho S) ∧
    dist (b+(L/4) • u) (b+(L/4+diam S/(4*(C+4))) • u)=diam S/(4*(C+4)) := by
  have hden : 0<4*(C+4) := by positivity
  have hlen : diam S/(4*(C+4))≤L/2 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have hpos : 0<diam S/(4*(C+4)) := div_pos (by linarith) hden
  refine ⟨hpos,?_,?_⟩
  · intro t ht
    apply hcore t
    exact ⟨ht.1,by linarith [ht.2]⟩
  · rw [dist_eq_norm,
      show (b+(L/4) • u)-(b+(L/4+diam S/(4*(C+4))) • u)=
        (-(diam S/(4*(C+4)))) • u by module,
      norm_smul,Real.norm_eq_abs,hu,mul_one,abs_neg,abs_of_pos hpos]

namespace PolynomialArchiveSnapshot

theorem zeroSet_isClosed {k : ℕ} {T C O : Type}
    (S : PolynomialArchiveSnapshot k T C O) (g : S.state.Grain) : IsClosed (S.zeroSet g) :=
  isClosed_eq ((rectangularPolynomialMap_contDiff (S.equations g) 0).continuous) continuous_const

theorem truncated_zeroSet_isCompact {k : ℕ} {T C O : Type}
    (S : PolynomialArchiveSnapshot k T C O) (g : S.state.Grain)
    (center : EuclideanSpace ℝ (Fin S.dimension)) (R : ℝ) :
    IsCompact (S.zeroSet g ∩ closedBall center R) :=
  (isCompact_closedBall center R).inter_left (S.zeroSet_isClosed g)

end PolynomialArchiveSnapshot
end KakeyaTwoScale
#print axioms KakeyaTwoScale.concentric_truncations_nested
#print axioms KakeyaTwoScale.localized_axis_truncation
#print axioms KakeyaTwoScale.diameter_normalized_axis_segment
#print axioms KakeyaTwoScale.PolynomialArchiveSnapshot.truncated_zeroSet_isCompact
