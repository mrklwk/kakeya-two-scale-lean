module
public import KakeyaTwoScale.NarrowSelectionMass

@[expose] public section

open MeasureTheory
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
open Classical

/-- Actual grid portions attain their average multiplicity on an occupied
cell. Integrability, finite support volume and positive support measure are
proved internally from the portion data and positive retained mass. -/
theorem grid_mass_point {n : ℕ} {J : Type*} (G : Finset J)
    (b v : J → Fin n → ℝ) {d : ℝ} (hd : 0 < d) (I : J → Set ℝ)
    (hI : ∀ j∈G, MeasurableSet (I j))
    (hunit : ∀ j∈G, I j ⊆ Set.Icc (0:ℝ) 1)
    (hpos : 0 < d^n*∑ j∈G, volume.real (I j)) :
    ∃ z ∈ occupiedGridRegion G b v d I,
      d^n*∑ j∈G, volume.real (I j) ≤
        volume.real (occupiedGridRegion G b v d I)*
          ((G.filter (fun j => z.1∈I j ∧
            gridIndex d z.2=gridIndex d (segmentPoint (b j) (v j) z.1))).card:ℝ) := by
  let S := occupiedGridRegion G b v d I
  let f := membershipCount G (fun j => gridPortion (b j) (v j) d (I j))
  have hs : MeasurableSet S := measurableSet_occupiedGridRegion G b v d I hI
  have hfin : volume S ≠ ⊤ := occupiedGridRegion_finite_volume G b v hd I hI hunit
  obtain ⟨hint,hint_eq⟩ := grid_portion_multiplicity_integral G b v hd I hI hunit
  have he : S.indicator f=f := by
    funext z
    by_cases hz : z∈S
    · exact Set.indicator_of_mem hz _
    · rw [Set.indicator_of_notMem hz]
      symm
      apply Finset.sum_eq_zero
      intro j hj
      apply Set.indicator_of_notMem
      intro hzj
      exact hz (Set.mem_iUnion₂.mpr ⟨j,hj,hzj⟩)
  have hi : (∫ z in S, f z)=d^n*∑ j∈G, volume.real (I j) := by
    rw [←integral_indicator hs,he]
    exact hint_eq
  have hnonzero : volume S ≠ 0 := by
    intro hzero
    rw [Measure.restrict_eq_zero.mpr hzero] at hi
    simp only [integral_zero_measure] at hi
    linarith
  obtain ⟨z,hz,havg⟩ := exists_setAverage_le hnonzero hfin hint.integrableOn
  refine ⟨z,hz,?_⟩
  have hvolpos : 0 < volume.real S := ENNReal.toReal_pos hnonzero hfin
  rw [setAverage_eq] at havg
  rw [hi] at havg
  have hh := mul_le_mul_of_nonneg_left havg hvolpos.le
  rw [smul_eq_mul,←mul_assoc,mul_inv_cancel₀ hvolpos.ne',one_mul] at hh
  simpa only [f,membershipCount_eq_card,gridPortion,S,Set.mem_ofPred_eq] using hh

end KakeyaTwoScale
#print axioms KakeyaTwoScale.grid_mass_point
