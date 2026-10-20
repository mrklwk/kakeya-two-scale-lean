module
public import KakeyaTwoScale.DimensionBridge
public import Mathlib.Topology.MetricSpace.Bounded

@[expose] public section

open MeasureTheory Metric Filter
noncomputable section
namespace KakeyaTwoScale

/-- A finite cover of the unit ball can be translated and rescaled to refine any
ball. This is the elementary geometric step behind bounded-set admissibility. -/
theorem refine_ball_cover {n : ℕ}
    (S : Finset (EuclideanSpace ℝ (Fin n)))
    (hS : closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ ⋃ s ∈ S, ball s (1/2))
    (c : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r) :
    ball c r ⊆ ⋃ s ∈ S, ball (c + r • s) (r/2) := by
  intro x hx
  have hn : ‖r⁻¹ • (x-c)‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr]
    have hx' : ‖x-c‖ < r := by simpa [mem_ball, dist_eq_norm] using hx
    exact le_of_lt ((inv_mul_lt_iff₀ hr).2 (by simpa using hx'))
  have hm := hS (by simpa [mem_closedBall, dist_zero_right] using hn)
  obtain ⟨s, hs, hxs⟩ := Set.mem_iUnion₂.mp hm
  refine Set.mem_iUnion₂.mpr ⟨s,hs,?_⟩
  rw [mem_ball, dist_eq_norm] at hxs ⊢
  have heq : x-(c+r • s) = r • (r⁻¹ • (x-c)-s) := by
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    abel
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
  nlinarith

 theorem dyadicRadius_succ (q : ℕ) : dyadicRadius (q+1) = dyadicRadius q/2 := by
  unfold dyadicRadius
  rw [Nat.cast_add, Nat.cast_one, mul_add, mul_one, Real.exp_add]
  rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ)<2)]
  ring

/-- Repeated affine refinement constructs actual finite covers with exponential
cardinality, without assuming any analytic covering estimate. -/
theorem dyadic_covers_of_unit_cover {n : ℕ}
    (K : Set (EuclideanSpace ℝ (Fin n)))
    (A S : Finset (EuclideanSpace ℝ (Fin n)))
    (hA : K ⊆ ⋃ c ∈ A, ball c 1)
    (hS : closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ ⋃ s ∈ S, ball s (1/2)) :
    ∀ q : ℕ, ∃ C : Finset (EuclideanSpace ℝ (Fin n)),
      K ⊆ ⋃ c ∈ C, ball c (dyadicRadius q) ∧ C.card ≤ A.card*S.card^q := by
  classical
  intro q
  induction q with
  | zero => exact ⟨A, by simpa [dyadicRadius] using hA, by simp⟩
  | succ q ih =>
    obtain ⟨C,hC,hcard⟩ := ih
    let D := (C.product S).image (fun p => p.1 + dyadicRadius q • p.2)
    refine ⟨D, ?_, ?_⟩
    · intro x hx
      obtain ⟨c,hc,hxc⟩ := Set.mem_iUnion₂.mp (hC hx)
      obtain ⟨s,hs,hxs⟩ := Set.mem_iUnion₂.mp
        (refine_ball_cover S hS c (Real.exp_pos _) hxc)
      apply Set.mem_iUnion₂.mpr
      refine ⟨c + dyadicRadius q • s, ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨(c,s),Finset.mem_product.mpr ⟨hc,hs⟩,rfl⟩
      · rw [dyadicRadius_succ]
        simpa only [dyadicRadius] using hxs
    · calc D.card ≤ (C.product S).card := Finset.card_image_le
           _ = C.card*S.card := Finset.card_product C S
           _ ≤ (A.card*S.card^q)*S.card := Nat.mul_le_mul_right _ hcard
           _ = A.card*S.card^(q+1) := by rw [pow_succ, Nat.mul_assoc]

/-- Every bounded Euclidean set has an admissible covering exponent. The exponent
is deliberately nonoptimal: compactness supplies a finite unit-ball refinement
and iteration turns its cardinality into a polynomial covering rate. -/
theorem bounded_has_dyadicCoverGrowth {n : ℕ}
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : Bornology.IsBounded K) :
    ∃ d : ℝ, 0 ≤ d ∧ DyadicCoverGrowth K d := by
  classical
  obtain ⟨A,_,hAf,hA⟩ := exists_finite_cover_balls_of_isCompact_closure
    hK.isCompact_closure (by norm_num : (0:ℝ)<1)
  obtain ⟨S,_,hSf,hS⟩ := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1).finite_cover_balls
    (by norm_num : (0:ℝ)<1/2)
  let a := hAf.toFinset
  let s := hSf.toFinset
  have hA' : K ⊆ ⋃ c ∈ a, ball c 1 := by simpa [a] using hA
  have hS' : closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ ⋃ c ∈ s, ball c (1/2) := by
    simpa [s] using hS
  let m : ℝ := max (s.card:ℝ) 1
  have hm : 0 < m := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨Real.log m / Real.log 2, div_nonneg (Real.log_nonneg (le_max_right _ _)) hl.le,
    (a.card:ℝ)+1, by positivity, 0, ?_⟩
  intro q _
  obtain ⟨C,hC,hcard⟩ := dyadic_covers_of_unit_cover K a s hA' hS' q
  refine ⟨C,hC,?_⟩
  have hcard' : (C.card:ℝ) ≤ (a.card:ℝ)*(s.card:ℝ)^q := by exact_mod_cast hcard
  have hp : (s.card:ℝ)^q ≤ m^q := pow_le_pow_left₀ (by positivity) (le_max_left _ _) q
  have he : Real.exp (Real.log 2*(Real.log m/Real.log 2)*(q:ℝ)) = m^q := by
    rw [mul_div_cancel₀ _ hl.ne', mul_comm, Real.exp_nat_mul, Real.exp_log hm]
  rw [he]
  have hnon : 0 ≤ m^q := by positivity
  exact hcard'.trans (by nlinarith [mul_le_mul_of_nonneg_left hp (show (0:ℝ) ≤ a.card by positivity)])

/-- The geometric endpoint now needs only boundedness, with no separate
admissibility assumption. The deep volume-transfer alternative stays explicit. -/
theorem upperBoxDimension_lower_of_bounded_transfer (n : ℕ) (hn : 4 ≤ n)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : Bornology.IsBounded K)
    (transfer : BroadTransfer n (n/2:ℕ) (fun q => neighborhoodVolume K (20*q)) ∨
      NarrowTransfer n (n/2:ℕ) (fun q => neighborhoodVolume K (20*q)) (neighborhoodVolume K)) :
    (597/1000:ℝ)*n ≤ upperBoxDimension K :=
  upperBoxDimension_lower_of_transfer n hn K (bounded_has_dyadicCoverGrowth hK) transfer

end KakeyaTwoScale
#print axioms KakeyaTwoScale.refine_ball_cover
#print axioms KakeyaTwoScale.dyadic_covers_of_unit_cover
#print axioms KakeyaTwoScale.bounded_has_dyadicCoverGrowth
#print axioms KakeyaTwoScale.upperBoxDimension_lower_of_bounded_transfer
