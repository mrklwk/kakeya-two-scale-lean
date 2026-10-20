module
public import KakeyaTwoScale.ParentLevel
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
namespace WeightedGrain

/-- The actual multiplicity band, formed using original multiplicities. -/
def band {Cube : Type*} (Q : Finset Cube) (m : Cube → ℕ) (j : ℕ) : Finset Cube :=
  Q.filter fun q => (m q).log2 = j

/-- Weighted dyadic pigeonholing with exact B+1 loss. Weights may be arbitrary
real values; nonnegativity is not needed for this averaging statement. -/
theorem exists_weighted_band {Cube : Type*} (Q : Finset Cube) (m : Cube → ℕ)
    (B : ℕ) (hbound : ∀ q ∈ Q, m q ≤ 2^B) (w : Cube → ℝ) :
    ∃ j ≤ B, (∑ q ∈ Q, w q) ≤ ((B+1:ℕ):ℝ) * ∑ q ∈ band Q m j, w q := by
  classical
  let levels := Finset.range (B+1)
  have hm : ∀ q ∈ Q, (m q).log2 ∈ levels := by
    intro q hq
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (ParentLevel.log2_le_of_card_bound (hbound q hq)))
  have hn : levels.Nonempty := ⟨0,Finset.mem_range.mpr (by omega)⟩
  have hden : (0:ℝ) < ((B+1:ℕ):ℝ) := by positivity
  have he : levels.card • ((∑ q ∈ Q, w q) / ((B+1:ℕ):ℝ)) ≤ ∑ q ∈ Q, w q := by
    simp only [levels,Finset.card_range,nsmul_eq_mul]
    exact le_of_eq (mul_div_cancel₀ _ hden.ne')
  obtain ⟨j,hj,hret⟩ := Finset.exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum hm hn he
  refine ⟨j,by simpa only [levels,Finset.mem_range,Nat.lt_add_one_iff] using hj,?_⟩
  have h := (div_le_iff₀ hden).mp hret
  simpa only [band,mul_comm] using h

/-- Positive original multiplicities lie in the genuine half-open dyadic band. -/
theorem band_bounds {Cube : Type*} (Q : Finset Cube) (m : Cube → ℕ) (j : ℕ)
    (hpos : ∀ q ∈ Q, 0 < m q) {q : Cube} (hq : q ∈ band Q m j) :
    2^j ≤ m q ∧ m q < 2^(j+1) := by
  obtain ⟨hq,hlog⟩ := Finset.mem_filter.mp hq
  have hn := ne_of_gt (hpos q hq)
  constructor
  · exact (Nat.le_log2 hn).mp (by omega)
  · exact (Nat.log2_lt hn).mp (by omega)

/-- The nonlinear cube objective is retained with exact B+1 loss. In particular
this covers p=1/(k-1), k≥2. The averaging works for every real p. -/
theorem exists_rpow_band {Cube : Type*} (Q : Finset Cube) (m : Cube → ℕ)
    (B : ℕ) (hpos : ∀ q ∈ Q, 0 < m q) (hbound : ∀ q ∈ Q, m q ≤ 2^B) (p : ℝ) :
    ∃ j ≤ B, (∀ q ∈ band Q m j, 2^j ≤ m q ∧ m q < 2^(j+1)) ∧
      (∑ q ∈ Q, (m q:ℝ)^p) ≤ ((B+1:ℕ):ℝ) * ∑ q ∈ band Q m j, (m q:ℝ)^p := by
  obtain ⟨j,hj,hw⟩ := exists_weighted_band Q m B hbound (fun q => (m q:ℝ)^p)
  exact ⟨j,hj,fun _ hq => band_bounds Q m j hpos hq,hw⟩

end WeightedGrain
end KakeyaTwoScale
#print axioms KakeyaTwoScale.WeightedGrain.exists_weighted_band
#print axioms KakeyaTwoScale.WeightedGrain.band_bounds
#print axioms KakeyaTwoScale.WeightedGrain.exists_rpow_band
