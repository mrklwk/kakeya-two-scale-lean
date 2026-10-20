module
public import Mathlib.Topology.MetricSpace.CoveringNumbers
public import Mathlib.Analysis.Normed.Group.Basic

@[expose] public section

open Set Metric
open scoped ENNReal NNReal
noncomputable section
namespace KakeyaTwoScale

/-- An actual finite packing, constructed by maximizing a separated subset of
an arbitrary compact set. The open unit balls are disjoint and the radius-three
balls cover the set. No cardinality or packing certificate is assumed. -/
theorem compact_disjoint_unit_ball_cover {E : Type*} [MetricSpace E]
    (S : Set E) (hS : IsCompact S) :
    ∃ F : Finset E, (↑F : Set E) ⊆ S ∧
      (↑F : Set E).PairwiseDisjoint (fun x => ball x 1) ∧
      S ⊆ ⋃ x ∈ F, ball x 3 := by
  classical
  obtain ⟨T,hTS,hTf,hT⟩ := exists_finite_isCover_of_isCompact (ε:=1) one_ne_zero hS
  have hp : packingNumber 2 S ≠ ⊤ := by
    apply ne_of_lt
    calc
      packingNumber 2 S ≤ externalCoveringNumber 1 S := by
        simpa using packingNumber_two_mul_le_externalCoveringNumber 1 S
      _ ≤ T.encard := hT.externalCoveringNumber_le_encard
      _ < ⊤ := hTf.encard_lt_top
  let P := maximalSeparatedSet 2 S
  have hPf : P.Finite := by
    apply Set.encard_ne_top_iff.mp
    simpa [P,encard_maximalSeparatedSet hp] using hp
  refine ⟨hPf.toFinset,by simpa [P] using (maximalSeparatedSet_subset (ε:=2) (A:=S)),?_,?_⟩
  · intro x hx y hy hxy
    have hs := isSeparated_maximalSeparatedSet (ε:=2) (A:=S)
      (show x ∈ P from by simpa using hx) (show y ∈ P from by simpa using hy) hxy
    have hd : (2:ℝ) < dist x y := by
      have hh : ENNReal.ofReal 2 < ENNReal.ofReal (dist x y) := by
        simpa [edist_dist] using hs
      exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num) |>.mp hh
    exact ball_disjoint_ball (by linarith)
  · intro x hx
    obtain ⟨y,hy,hxy⟩ := isCover_maximalSeparatedSet hp hx
    have hd : dist x y ≤ (2:ℝ) := by
      have hh : ENNReal.ofReal (dist x y) ≤ ENNReal.ofReal 2 := by
        simpa [SetRel.IsCover,edist_dist] using hxy
      exact (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0:ℝ) ≤ 2)).mp hh
    exact mem_iUnion₂.mpr ⟨y,by simpa [P] using hy,by simpa only [mem_ball] using (lt_of_le_of_lt hd (by norm_num : (2:ℝ)<3))⟩

/-- A compact set has a uniform finite bound for the cardinality of every
positively separated finite subset. The bound is chosen before the subset. -/
theorem compact_separated_card_bound {E : Type*} [MetricSpace E]
    (S : Set E) (hS : IsCompact S) (δ : ℝ≥0) (hδ : 0 < δ) :
    ∃ M : ℕ, ∀ F : Finset E, (↑F : Set E) ⊆ S →
      Metric.IsSeparated δ (↑F : Set E) → F.card ≤ M := by
  obtain ⟨T,_,hTf,hT⟩ := exists_finite_isCover_of_isCompact
    (ε:=δ/2) (ne_of_gt (by positivity)) hS
  refine ⟨hTf.toFinset.card,?_⟩
  intro F hFS hsep
  have hh : (↑F : Set E).encard ≤ T.encard := calc
    _ ≤ packingNumber δ S := hsep.encard_le_packingNumber hFS
    _ = packingNumber (2*(δ/2)) S := by congr 1; ring
    _ ≤ externalCoveringNumber (δ/2) S := packingNumber_two_mul_le_externalCoveringNumber _ _
    _ ≤ T.encard := hT.externalCoveringNumber_le_encard
  have hTcard : T.encard = (hTf.toFinset.card : ℕ∞) := by
    rw [← Set.encard_coe_eq_coe_finsetCard,hTf.coe_toFinset]
  rw [Set.encard_coe_eq_coe_finsetCard,hTcard] at hh
  exact_mod_cast hh

end KakeyaTwoScale
#print axioms KakeyaTwoScale.compact_disjoint_unit_ball_cover

#print axioms KakeyaTwoScale.compact_separated_card_bound
