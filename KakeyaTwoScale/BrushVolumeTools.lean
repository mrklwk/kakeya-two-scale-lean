module
public import KakeyaTwoScale.QuarterTubeVolume
public import KakeyaTwoScale.BrushCaptureGeometry

@[expose] public section

open MeasureTheory
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
open Classical

theorem angular_weight_cap_subset {d : ℕ} {J : Type*} (G S : Finset J)
    (hSG : S ⊆ G) (u : J → EuclideanSpace ℝ (Fin d)) (w : J → ℝ) (r B : ℝ)
    (hw : ∀ j ∈ G, 0 ≤ w j)
    (hcap : ∀ v : EuclideanSpace ℝ (Fin d), ‖v‖=1 →
      (∑ j ∈ G.filter (fun j => Real.arccos |inner ℝ (u j) v| ≤ r), w j) ≤ B) :
    ∀ v : EuclideanSpace ℝ (Fin d), ‖v‖=1 →
      (∑ j ∈ S.filter (fun j => Real.arccos |inner ℝ (u j) v| ≤ r), w j) ≤ B := by
  intro v hv
  apply le_trans _ (hcap v hv)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro j hj
    obtain ⟨hj,ha⟩ := Finset.mem_filter.mp hj
    exact Finset.mem_filter.mpr ⟨hSG hj,ha⟩
  · intro j hj _
    exact hw j (Finset.mem_filter.mp hj).1

theorem quarter_piece_subset_tube {d : ℕ} (b u : EuclideanSpace ℝ (Fin d))
    (I : Set ℝ) (r : ℝ)
    (hI : I=Set.Icc (0:ℝ) (1/4) ∨ I=Set.Icc (3/4:ℝ) 1) :
    Metric.thickening r (segmentPoint b u '' I) ⊆ euclideanTube b u r := by
  intro x hx
  obtain ⟨y,⟨t,ht,rfl⟩,hx⟩ := Metric.mem_thickening_iff.mp hx
  refine ⟨t,?_,hx⟩
  rcases hI with h | h <;> rw [h] at ht <;> constructor <;> linarith [ht.1,ht.2]

/-- Sum actual bounded pieces inside a finite-measure set. Restriction is
only a proof device; both sides are the original Lebesgue volumes. -/
theorem piece_volume_sum_le_container {X P : Type*} [MeasurableSpace X]
    (μ : Measure X) (U : Set X) (hfin : μ U ≠ ⊤)
    (net : Finset P) (pieces : P → Set X) (N : ℝ) (hN : 0 ≤ N)
    (hm : ∀ j ∈ net, MeasurableSet (pieces j))
    (hsub : ∀ j ∈ net, pieces j ⊆ U)
    (hover : ∀ x, weightedOverlap net pieces (fun _ => (1:ℝ)) x ≤ N) :
    (∑ j ∈ net, μ.real (pieces j)) ≤ N*μ.real U := by
  let nu := μ.restrict U
  let : IsFiniteMeasure nu := isFiniteMeasure_restrict.mpr hfin
  have he : ∀ j ∈ net, nu.real (pieces j)=μ.real (pieces j) :=
    fun j hj => restricted_real_eq_of_subset μ U (pieces j) (hm j hj) (hsub j hj)
  have hu : (⋃ j ∈ net, pieces j) ⊆ U := by
    intro x hx
    obtain ⟨j,hj,hx⟩ := Set.mem_iUnion₂.mp hx
    exact hsub j hj hx
  have hreal := restricted_real_eq_of_subset μ U (⋃ j ∈ net, pieces j)
    (Finset.measurableSet_biUnion _ hm) hu
  have hh := weighted_union_volume nu net pieces (fun _ => (1:ℝ)) N hm hover
  simp only [one_mul] at hh
  rw [hreal] at hh
  have hsum : (∑ j ∈ net, nu.real (pieces j))=∑ j ∈ net, μ.real (pieces j) :=
    Finset.sum_congr rfl he
  rw [hsum] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (measureReal_mono hu hfin) hN)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.angular_weight_cap_subset
#print axioms KakeyaTwoScale.quarter_piece_subset_tube
#print axioms KakeyaTwoScale.piece_volume_sum_le_container
