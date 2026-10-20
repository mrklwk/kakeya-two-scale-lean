module
public import KakeyaTwoScale.CountableImageMultiplicity
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BigOperators Function
noncomputable section
namespace KakeyaTwoScale

/-- Disjoint injective source pieces count actual preimages exactly, including
infinite fibers. No finiteness or bound on multiplicity is assumed. -/
theorem image_piece_multiplicity_eq {α β : Type*} [Nonempty α]
    (f : α → β) (P : ℕ → Set α) (hdis : Pairwise (Disjoint on P))
    (hinj : ∀ i, InjOn f (P i)) (z : β) :
    ({i | z ∈ f '' P i} : Set ℕ).encard =
      ({x | x ∈ ⋃ i, P i ∧ f x = z} : Set α).encard := by
  classical
  let J : Set ℕ := {i | z ∈ f '' P i}
  choose x hx using fun i : J => i.property
  let g (i : ℕ) : α := if hi : i ∈ J then x ⟨i, hi⟩ else Classical.ofNonempty
  have hg (i : ℕ) (hi : i ∈ J) : g i ∈ P i ∧ f (g i) = z := by
    simpa [g, hi] using hx ⟨i, hi⟩
  have hgi : InjOn g J := by
    intro i hi j hj he
    by_contra hij
    exact Set.disjoint_left.mp (hdis hij) (hg i hi).1 (he ▸ (hg j hj).1)
  have himg : g '' J = {x | x ∈ ⋃ i, P i ∧ f x = z} := by
    ext a
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨mem_iUnion.mpr ⟨i, (hg i hi).1⟩, (hg i hi).2⟩
    · rintro ⟨ha, he⟩
      obtain ⟨i, hi⟩ := mem_iUnion.mp ha
      have hiJ : i ∈ J := ⟨a, hi, he⟩
      exact ⟨i, hiJ, hinj i (hg i hiJ).1 hi ((hg i hiJ).2.trans he.symm)⟩
  rw [← himg, hgi.encard_image]

/-- The sum of image indicators equals the exact extended fiber cardinality. -/
theorem image_indicator_tsum_eq_fiber_count {α β : Type*} [Nonempty α]
    (f : α → β) (P : ℕ → Set α) (hdis : Pairwise (Disjoint on P))
    (hinj : ∀ i, InjOn f (P i)) (z : β) :
    (∑' i, (f '' P i).indicator (fun _ => (1 : ℝ≥0∞)) z) =
      ({x | x ∈ ⋃ i, P i ∧ f x = z} : Set α).encard.toENNReal := by
  classical
  rw [← image_piece_multiplicity_eq f P hdis hinj z, ← ENNReal.tsum_set_one]
  rw [tsum_subtype {i | z ∈ f '' P i} (fun _ : ℕ => (1 : ℝ≥0∞))]
  apply tsum_congr
  intro i
  simp [Set.indicator]

/-- Tonelli turns exact point multiplicity into exact total image measure. -/
theorem countable_measure_sum_eq_fiber_integral {α β : Type*} [Nonempty α]
    [MeasurableSpace β] (μ : Measure β) (f : α → β) (P : ℕ → Set α)
    (hdis : Pairwise (Disjoint on P)) (hinj : ∀ i, InjOn f (P i))
    (himage : ∀ i, MeasurableSet (f '' P i)) :
    (∑' i, μ (f '' P i)) =
      ∫⁻ z, ({x | x ∈ ⋃ i, P i ∧ f x = z} : Set α).encard.toENNReal ∂μ := by
  simp_rw [← image_indicator_tsum_eq_fiber_count f P hdis hinj]
  rw [lintegral_tsum (fun i => (measurable_const.indicator (himage i)).aemeasurable)]
  apply tsum_congr
  intro i
  simp [lintegral_indicator, himage]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.image_piece_multiplicity_eq
#print axioms KakeyaTwoScale.image_indicator_tsum_eq_fiber_count
#print axioms KakeyaTwoScale.countable_measure_sum_eq_fiber_integral
