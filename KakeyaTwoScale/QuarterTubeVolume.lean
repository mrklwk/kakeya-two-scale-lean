module
public import KakeyaTwoScale.PlaneWeightedVolume

@[expose] public section

open MeasureTheory
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
open Classical

theorem euclideanTube_subsegment {d : ℕ} (b u : EuclideanSpace ℝ (Fin d))
    (s L r : ℝ) (hL : 0 < L) :
    euclideanTube (b+s • u) (L • u) r =
      Metric.thickening r (segmentPoint b u '' Set.Icc s (s+L)) := by
  ext x
  rw [Metric.mem_thickening_iff]
  constructor
  · rintro ⟨t,ht,hx⟩
    have hi : s+L*t ∈ Set.Icc s (s+L) := by constructor <;> nlinarith [ht.1,ht.2]
    refine ⟨segmentPoint b u (s+L*t),⟨s+L*t,hi,rfl⟩,?_⟩
    have he : b+s • u+t • (L • u)=segmentPoint b u (s+L*t) := by
      unfold segmentPoint; rw [smul_smul]; module
    rwa [← he]
  · rintro ⟨y,⟨t,ht,rfl⟩,hx⟩
    have hi : (t-s)/L ∈ Set.Icc (0:ℝ) 1 := by
      constructor
      · exact div_nonneg (by linarith [ht.1]) hL.le
      · apply (div_le_iff₀ hL).mpr; linarith [ht.2]
    refine ⟨(t-s)/L,hi,?_⟩
    have he : b+s • u+((t-s)/L) • (L • u)=segmentPoint b u t := by
      rw [smul_smul,div_mul_cancel₀ _ hL.ne']
      unfold segmentPoint; module
    rwa [he]

def quarterStart (I : Set ℝ) : ℝ := if I=Set.Icc (0:ℝ) (1/4) then 0 else 3/4

theorem quarterStart_bounds (I : Set ℝ) : 0 ≤ quarterStart I ∧ quarterStart I ≤ 1 := by
  unfold quarterStart; split_ifs <;> norm_num

theorem quarter_tube_eq {d : ℕ} (b u : EuclideanSpace ℝ (Fin d)) (I : Set ℝ) (r : ℝ)
    (hI : I=Set.Icc (0:ℝ) (1/4) ∨ I=Set.Icc (3/4:ℝ) 1) :
    euclideanTube (b+quarterStart I • u) ((1/4:ℝ) • u) r =
      Metric.thickening r (segmentPoint b u '' I) := by
  rw [euclideanTube_subsegment b u _ _ _ (by norm_num)]
  congr 2
  rcases hI with hI | hI
  · simp [quarterStart,hI]
  · have hne : (Set.Icc (3/4:ℝ) 1) ≠ Set.Icc (0:ℝ) (1/4) := by
      intro he
      have hh : (0:ℝ) ∈ Set.Icc (3/4:ℝ) 1 := by rw [he]; norm_num
      norm_num at hh
    simp only [hI,quarterStart,ite_eq_right hne]
    norm_num

/-- Apply the closed weighted plane estimate to the literal endpoint-quarter
sets returned by the shortening construction, allowing a different quarter
for each tube. Original directions and weights are unchanged. -/
theorem quarter_plane_weighted_volume (n k : ℕ) (R B C : ℝ)
    (hR : 0 ≤ R) (hB : 0 < B) (hC : 0 ≤ C) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (H : Submodule ℝ (EuclideanSpace ℝ (Fin (n+1)))) [H.HasOrthogonalProjection],
      Module.finrank ℝ H=k+1 → ∀ r : ℝ, 0 < r → r ≤ 1 →
      ∀ {J : Type*} (G : Finset J) (b u : J → EuclideanSpace ℝ (Fin (n+1)))
        (w : J → ℝ) (I : J → Set ℝ),
      (∀ j ∈ G, I j=Set.Icc (0:ℝ) (1/4) ∨ I j=Set.Icc (3/4:ℝ) 1) →
      (∀ j ∈ G, ‖b j‖ ≤ R) → (∀ j ∈ G, ‖u j‖=1) → (∀ j ∈ G, 0 ≤ w j) →
      (∀ j ∈ G, planeAngle H (u j) ≤ C*r) →
      (∀ v : EuclideanSpace ℝ (Fin (n+1)), ‖v‖=1 →
        (∑ j ∈ G.filter (fun j => Real.arccos |inner ℝ (u j) v| ≤ r), w j) ≤ B) →
      c*r^n*(r^k)^theta*(∑ j ∈ G, w j) ≤
        volume.real (⋃ j ∈ G, Metric.thickening r (segmentPoint (b j) (u j) '' I j)) := by
  obtain ⟨c,hc,hvol⟩ := plane_weighted_capsule_volume n k (R+1) (1/4) B C
    (by linarith) (by norm_num) (by norm_num) hB hC
  refine ⟨c,hc,?_⟩
  intro H instH hdim r hr hrone J G b u w I hI hb hu hw ha hcap
  let b' := fun j => b j+quarterStart (I j) • u j
  have hb' : ∀ j ∈ G, ‖b' j‖ ≤ R+1 := by
    intro j hj
    have hh := norm_add_le (b j) (quarterStart (I j) • u j)
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (quarterStart_bounds _).1,hu j hj,mul_one] at hh
    exact hh.trans (add_le_add (hb j hj) (quarterStart_bounds _).2)
  have hh := hvol H hdim r hr hrone G b' u w hb' hu hw ha hcap
  have he : (⋃ j ∈ G, euclideanTube (b' j) ((1/4:ℝ) • u j) r)=
      ⋃ j ∈ G, Metric.thickening r (segmentPoint (b j) (u j) '' I j) := by
    apply Set.iUnion_congr
    intro j
    apply Set.iUnion_congr
    intro hj
    exact quarter_tube_eq (b j) (u j) (I j) r (hI j hj)
  rwa [he] at hh

end KakeyaTwoScale
#print axioms KakeyaTwoScale.euclideanTube_subsegment
#print axioms KakeyaTwoScale.quarterStart_bounds
#print axioms KakeyaTwoScale.quarter_tube_eq
#print axioms KakeyaTwoScale.quarter_plane_weighted_volume
