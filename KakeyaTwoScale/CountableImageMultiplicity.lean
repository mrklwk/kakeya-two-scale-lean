module
public import KakeyaTwoScale.RegularInjectivePartition
public import Mathlib.Data.Set.Card

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BigOperators Function
noncomputable section
namespace KakeyaTwoScale

/-- A countable measurable family with point multiplicity at most N has total
measure at most N times the measure of any measurable containing set. -/
theorem countable_measure_sum_le_multiplicity {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (U : ℕ → Set α) (hU : ∀ i, MeasurableSet (U i))
    (T : Set α) (hT : MeasurableSet T) (hsub : ∀ i, U i ⊆ T)
    (N : ℕ) (hmult : ∀ z, ({i | z ∈ U i} : Set ℕ).encard ≤ N) :
    ∑' i, μ (U i) ≤ (N : ℝ≥0∞) * μ T := by
  classical
  apply ENNReal.summable.tsum_le_of_sum_le
  intro I
  have hp (z : α) : (∑ i ∈ I, (U i).indicator (fun _ => (1 : ℝ≥0∞)) z) ≤
      T.indicator (fun _ => (N : ℝ≥0∞)) z := by
    by_cases hz : z ∈ T
    · rw [Set.indicator_of_mem hz]
      have hc : (I.filter (fun i => z ∈ U i)).card ≤ N := by
        have henc := (Set.encard_mono (show (↑(I.filter (fun i => z ∈ U i)) : Set ℕ) ⊆
          {i | z ∈ U i} from fun i hi => (Finset.mem_filter.mp hi).2)).trans (hmult z)
        simpa only [Set.encard_coe_eq_coe_finsetCard, Nat.cast_le] using henc
      calc
        (∑ i ∈ I, (U i).indicator (fun _ => (1 : ℝ≥0∞)) z) =
            ((I.filter (fun i => z ∈ U i)).card : ℝ≥0∞) := by
          simp [Set.indicator]
        _ ≤ N := by exact_mod_cast hc
    · rw [Set.indicator_of_notMem hz]
      have hi (i : ℕ) : z ∉ U i := fun hi => hz (hsub i hi)
      simp [Set.indicator_of_notMem, hi]
  calc
    ∑ i ∈ I, μ (U i) = ∫⁻ z, ∑ i ∈ I, (U i).indicator (fun _ => (1 : ℝ≥0∞)) z ∂μ := by
      rw [lintegral_finsetSum]
      · simp [lintegral_indicator, hU]
      · intro i hi; exact measurable_const.indicator (hU i)
    _ ≤ ∫⁻ z, T.indicator (fun _ => (N : ℝ≥0∞)) z ∂μ := lintegral_mono hp
    _ = _ := by simp [lintegral_indicator, hT]

/-- Disjoint source pieces cannot create more image overlaps than the number
of actual preimages in their union. -/
theorem image_piece_multiplicity {α β : Type*} [Nonempty α]
    (f : α → β) (P : ℕ → Set α) (hdis : Pairwise (Disjoint on P))
    (R : Set α) (hsub : ∀ i, P i ⊆ R) (N : ℕ)
    (hmult : ∀ z, ({x | x ∈ R ∧ f x=z} : Set α).encard ≤ N) :
    ∀ z, ({i | z ∈ f '' P i} : Set ℕ).encard ≤ N := by
  classical
  intro z
  let J : Set ℕ := {i | z ∈ f '' P i}
  choose x hx using fun i : J => i.property
  let g (i : ℕ) : α := if hi : i ∈ J then x ⟨i,hi⟩ else Classical.ofNonempty
  have hg (i : ℕ) (hi : i ∈ J) : g i ∈ P i ∧ f (g i)=z := by
    simpa [g, hi] using hx ⟨i,hi⟩
  have hinj : InjOn g J := by
    intro i hi j hj he
    by_contra hij
    exact Set.disjoint_left.mp (hdis hij) (hg i hi).1 (he ▸ (hg j hj).1)
  have hmaps : MapsTo g J {x | x ∈ R ∧ f x=z} := by
    intro i hi
    exact ⟨hsub i (hg i hi).1, (hg i hi).2⟩
  exact (Set.encard_le_encard_of_injOn hmaps hinj).trans (hmult z)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.countable_measure_sum_le_multiplicity
#print axioms KakeyaTwoScale.image_piece_multiplicity
