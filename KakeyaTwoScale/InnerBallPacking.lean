module
public import KakeyaTwoScale.FlatCylinderThickness
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

@[expose] public section

open Set Metric MeasureTheory
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- Quantitative packing from actual measurable inner balls, with no
measurability assumption on the containing set. -/
theorem inner_ball_packing {d : ℕ} (W : Set (EuclideanSpace ℝ (Fin d)))
    (r : ℝ) (_hr : 0<r) (F : Finset (EuclideanSpace ℝ (Fin d)))
    (hinner : ∀ x∈F, ∃ y, ball y (r/8)⊆W∩ball x r)
    (hsep : ∀ x∈F, ∀ y∈F, x≠y → 2*r≤dist x y) :
    (F.card : ℝ≥0∞)*volume (ball (0 : EuclideanSpace ℝ (Fin d)) (r/8))≤volume W := by
  classical
  choose f hf using fun x : F => hinner x x.property
  have hdis : Set.PairwiseDisjoint (↑(Finset.univ : Finset F) : Set F)
      (fun x => ball (f x) (r/8)) := by
    intro x _ y _ hne
    apply Disjoint.mono (fun z hz => (hf x hz).2) (fun z hz => (hf y hz).2)
    apply ball_disjoint_ball
    simpa only [two_mul] using hsep x x.property y y.property (fun h => hne (Subtype.ext h))
  have hv (x : F) : volume (ball (f x) (r/8))=
      volume (ball (0 : EuclideanSpace ℝ (Fin d)) (r/8)) := by
    exact Measure.addHaar_ball_center volume (f x) (r/8)
  calc
    _ = volume (⋃ x∈(Finset.univ : Finset F),ball (f x) (r/8)) := by
      rw [measure_biUnion_finset hdis (fun _ _ => measurableSet_ball)]
      simp only [hv,Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul]
    _ ≤ volume W := measure_mono (by
      rintro z hz
      obtain ⟨x,_,hx⟩ := mem_iUnion₂.mp hz
      exact (hf x hx).1)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.inner_ball_packing
