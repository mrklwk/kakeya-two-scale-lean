module
public import KakeyaTwoScale.EuclideanTubeSource

@[expose] public section

open MeasureTheory
open scoped Pointwise
noncomputable section
namespace KakeyaTwoScale

/-- Dilation of a unit tube fits inside the corresponding shortened tube;
we deliberately keep the original width when the length is at most one. -/
theorem scaled_tube_subset {d : ℕ} (b u : EuclideanSpace ℝ (Fin d))
    {L r : ℝ} (hL : 0 < L) (hLone : L ≤ 1) (hr : 0 < r) :
    L • euclideanTube (L⁻¹ • b) u r ⊆ euclideanTube b (L • u) r := by
  rintro x ⟨y,hy,rfl⟩
  obtain ⟨t,ht,hd⟩ := hy
  refine ⟨t,ht,?_⟩
  have he : b+t • (L • u)=L • (L⁻¹ • b+t • u) := by
    simp [smul_add,smul_smul,hL.ne',mul_comm]
  rw [he, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hL]
  have hh := mul_lt_mul_of_pos_left hd hL
  rw [dist_eq_norm] at hh
  exact hh.trans_le (mul_le_of_le_one_left hr.le hLone)

/-- Ordinary tube estimate for every fixed positive length at most one.
Directions retain the source angular separation at the original width. -/
theorem short_separated_euclidean_tubes_volume (n : ℕ) (R L : ℝ)
    (hR : 0 ≤ R) (hL : 0 < L) (hLone : L ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r →
      ∀ {J : Type*} (G : Finset J), G.Nonempty →
      ∀ b u : J → EuclideanSpace ℝ (Fin (n+1)),
      (∀ j ∈ G, ‖b j‖ ≤ R) → (∀ j ∈ G, ‖u j‖=1) →
      (∀ j ∈ G, ∀ k ∈ G, j ≠ k → r ≤ Real.arccos |inner ℝ (u j) (u k)|) →
      C*r^n*(G.card:ℝ)^a ≤ volume.real (⋃ j ∈ G, euclideanTube (b j) (L • u j) r) := by
  obtain ⟨C,hC,h⟩ := source_separated_euclidean_tubes_volume n (L⁻¹*R) (by positivity)
  refine ⟨L^(n+1)*C,by positivity,?_⟩
  intro r hr J G hG b u hb hu hs
  let U := ⋃ j ∈ G, euclideanTube (L⁻¹ • b j) (u j) r
  let E := ⋃ j ∈ G, euclideanTube (b j) (L • u j) r
  have hbase : ∀ j ∈ G, ‖L⁻¹ • b j‖ ≤ L⁻¹*R := by
    intro j hj
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hL)]
    exact mul_le_mul_of_nonneg_left (hb j hj) (inv_nonneg.mpr hL.le)
  have hv := h r hr G hG (fun j => L⁻¹ • b j) u hbase hu hs
  have hsub : L • U ⊆ E := by
    rintro x ⟨y,hy,rfl⟩
    obtain ⟨j,hj,hy⟩ := Set.mem_iUnion₂.mp hy
    exact Set.mem_iUnion₂.mpr ⟨j,hj,scaled_tube_subset (b j) (u j) hL hLone hr ⟨y,hy,rfl⟩⟩
  have hvol : volume.real (L • U)=L^(n+1)*volume.real U := by
    rw [Measure.real,Measure.addHaar_smul_of_nonneg volume hL.le,finrank_euclideanSpace_fin,
      ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity)]
    rfl
  have hm := measureReal_mono hsub (euclideanTube_union_finite G b (fun j => L • u j) r)
  rw [hvol] at hm
  have hh := mul_le_mul_of_nonneg_left hv (show 0 ≤ L^(n+1) by positivity)
  change _ ≤ volume.real E
  calc
    _ = L^(n+1)*(C*r^n*(G.card:ℝ)^a) := by ring
    _ ≤ L^(n+1)*volume.real U := hh
    _ ≤ volume.real E := hm

end KakeyaTwoScale
#print axioms KakeyaTwoScale.scaled_tube_subset
#print axioms KakeyaTwoScale.short_separated_euclidean_tubes_volume
