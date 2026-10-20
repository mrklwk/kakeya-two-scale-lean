module
public import KakeyaTwoScale.BoundedAdmissibility
public import KakeyaTwoScale.DyadicCover

@[expose] public section

open MeasureTheory Metric Filter
open scoped ENNReal BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- Same-scale covers control fixed enlarged neighborhoods directly. -/
theorem enlarged_neighborhood_volume_le_cover {n : ℕ} [NeZero n]
    (K : Set (EuclideanSpace ℝ (Fin n))) (S : Finset (EuclideanSpace ℝ (Fin n)))
    (r C : ℝ) (hcover : K ⊆ ⋃ c ∈ S, ball c r) :
    volume (thickening (C*r) K) ≤ (S.card:ℝ≥0∞)*ENNReal.ofReal ((C+1)*r)^n*
      ENNReal.ofReal (Real.sqrt Real.pi^n/Real.Gamma ((n:ℝ)/2+1)) := by
  have hsub : thickening (C*r) K ⊆ ⋃ c ∈ S, ball c ((C+1)*r) := by
    intro x hx
    obtain ⟨y,hy,hxy⟩ := mem_thickening_iff.mp hx
    obtain ⟨c,hc,hyc⟩ := Set.mem_iUnion₂.mp (hcover hy)
    refine Set.mem_iUnion₂.mpr ⟨c,hc,?_⟩
    change dist x c < _
    have h := dist_triangle x y c
    have : dist y c < r := hyc
    nlinarith
  calc
    _ ≤ volume (⋃ c ∈ S, ball c ((C+1)*r)) := measure_mono hsub
    _ ≤ ∑ c ∈ S, volume (ball c ((C+1)*r)) := measure_biUnion_finset_le _ _
    _ = _ := by simp [EuclideanSpace.volume_ball, mul_assoc]

theorem enlarged_neighborhood_finite_of_cover {n : ℕ} [NeZero n]
    (K : Set (EuclideanSpace ℝ (Fin n))) (S : Finset (EuclideanSpace ℝ (Fin n)))
    (r C : ℝ) (hcover : K ⊆ ⋃ c ∈ S, ball c r) :
    volume (thickening (C*r) K) ≠ ⊤ := by
  apply ne_top_of_le_ne_top _ (enlarged_neighborhood_volume_le_cover K S r C hcover)
  finiteness

theorem enlarged_neighborhood_real_le_cover {n : ℕ} [NeZero n]
    (K : Set (EuclideanSpace ℝ (Fin n))) (S : Finset (EuclideanSpace ℝ (Fin n)))
    {r C : ℝ} (hr : 0 ≤ r) (hC : 0 ≤ C) (hcover : K ⊆ ⋃ c ∈ S, ball c r) :
    volume.real (thickening (C*r) K) ≤ (S.card:ℝ)*((C+1)*r)^n*ballConstant n := by
  have h := ENNReal.toReal_mono (by finiteness) (enlarged_neighborhood_volume_le_cover K S r C hcover)
  simpa only [Measure.real,ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (C+1)*r),ballConstant] using h

/-- The coefficient precedes every q; no scale shift or cover stability assumption. -/
theorem DyadicCoverGrowth.enlarged_volume_bound {n : ℕ} [NeZero n]
    {K : Set (EuclideanSpace ℝ (Fin n))} {d : ℝ} (H : DyadicCoverGrowth K d)
    (C : ℝ) (hC : 0 ≤ C) :
    ∃ B : ℝ, 0 < B ∧ ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q →
      volume (thickening (C*dyadicRadius q) K) ≠ ⊤ ∧
      volume.real (thickening (C*dyadicRadius q) K) ≤
        B*Real.exp (-Real.log 2*((n:ℝ)-d)*q) := by
  obtain ⟨B,hB,Q,hQ⟩ := H
  refine ⟨B*(C+1)^n*(ballConstant n+1),by
    have : 0 ≤ ballConstant n := ENNReal.toReal_nonneg
    positivity,Q,?_⟩
  intro q hq
  obtain ⟨S,hcover,hcard⟩ := hQ q hq
  refine ⟨enlarged_neighborhood_finite_of_cover K S _ C hcover,?_⟩
  have h := enlarged_neighborhood_real_le_cover K S (show 0 ≤ dyadicRadius q from (Real.exp_pos _).le) hC hcover
  have hr : 0 < dyadicRadius q := Real.exp_pos _
  have hb : 0 ≤ ballConstant n := ENNReal.toReal_nonneg
  have hh := h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcard (by positivity)) hb)
  have hid : (B*Real.exp (Real.log 2*d*q))*((C+1)*dyadicRadius q)^n*ballConstant n =
      (B*(C+1)^n*ballConstant n)*Real.exp (-Real.log 2*((n:ℝ)-d)*q) := by
    rw [mul_pow]
    unfold dyadicRadius
    rw [← Real.exp_nat_mul]
    calc
      _ = (B*(C+1)^n*ballConstant n)*
        (Real.exp (Real.log 2*d*q)*Real.exp ((n:ℝ)*(-Real.log 2*q))) := by ring
      _ = _ := by rw [← Real.exp_add]; congr 2; ring
  rw [hid] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (by
    have : 0 ≤ B*(C+1)^n := by positivity
    nlinarith) (Real.exp_pos _).le)

/-- Boundedness alone makes every fixed neighborhood finite. -/
theorem bounded_neighborhood_finite {n : ℕ}
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : Bornology.IsBounded K) (r : ℝ) :
    volume (thickening r K) ≠ ⊤ := hK.thickening.measure_lt_top.ne

/-- Fixed enlargement and prefactor defining a common geometric envelope. -/
def enlargedEnvelope {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (A C : ℝ)
    (q : ℕ) : ℝ := A * volume.real (thickening (C*dyadicRadius q) K)

 theorem DyadicCoverGrowth.enlarged_envelope_bound {n : ℕ} [NeZero n]
    {K : Set (EuclideanSpace ℝ (Fin n))} {d : ℝ} (H : DyadicCoverGrowth K d)
    (A C : ℝ) (hA : 0 < A) (hC : 0 < C) :
    ∃ B : ℝ, 0 < B ∧ ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q →
      enlargedEnvelope K A C q ≤ B*Real.exp (-Real.log 2*((n:ℝ)-d)*q) := by
  obtain ⟨B,hB,Q,hQ⟩ := H.enlarged_volume_bound C hC.le
  refine ⟨A*B,mul_pos hA hB,Q,?_⟩
  intro q hq
  unfold enlargedEnvelope
  simpa [mul_assoc] using mul_le_mul_of_nonneg_left (hQ q hq).2 hA.le

 theorem DyadicCoverGrowth.enlarged_neighborhoodUpper {n : ℕ} [NeZero n]
    {K : Set (EuclideanSpace ℝ (Fin n))} {d : ℝ} (H : DyadicCoverGrowth K d)
    (A C : ℝ) (hA : 0 < A) (hC : 0 < C) :
    NeighborhoodUpper n d (fun q => enlargedEnvelope K A C (20*q))
      (enlargedEnvelope K A C) := by
  obtain ⟨B,hB,Q,hV⟩ := H.enlarged_envelope_bound A C hA hC
  refine ⟨fun _ => mul_nonneg hA.le ENNReal.toReal_nonneg,
    fun _ => mul_nonneg hA.le ENNReal.toReal_nonneg, ?_⟩
  intro ε hε
  refine ⟨B,B,hB,hB,eventually_atTop.mpr ⟨Q,?_⟩⟩
  intro q hq
  have hq0 : (0:ℝ) ≤ q := by positivity
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hεq : 0 ≤ Real.log 2*ε*q := by positivity
  have hf := hV (20*q) (by omega)
  have hc := hV q hq
  constructor
  · apply hf.trans
    apply mul_le_mul_of_nonneg_left _ hB.le
    apply Real.exp_le_exp.mpr
    push_cast
    nlinarith
  · apply hc.trans
    apply mul_le_mul_of_nonneg_left _ hB.le
    apply Real.exp_le_exp.mpr
    nlinarith

/-- Bounded, nonempty sets have a strictly positive envelope at every scale. -/
theorem enlargedEnvelope_pos {n : ℕ}
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : Bornology.IsBounded K)
    (hne : K.Nonempty) (A C : ℝ) (hA : 0 < A) (hC : 0 < C) (q : ℕ) :
    0 < enlargedEnvelope K A C q := by
  apply mul_pos hA
  apply ENNReal.toReal_pos _ (bounded_neighborhood_finite hK _)
  apply ne_of_gt
  apply isOpen_thickening.measure_pos (μ := volume)
  exact hne.mono (self_subset_thickening (mul_pos hC (Real.exp_pos _)) K)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.enlarged_neighborhood_volume_le_cover
#print axioms KakeyaTwoScale.bounded_neighborhood_finite
#print axioms KakeyaTwoScale.DyadicCoverGrowth.enlarged_volume_bound
#print axioms KakeyaTwoScale.DyadicCoverGrowth.enlarged_envelope_bound
#print axioms KakeyaTwoScale.DyadicCoverGrowth.enlarged_neighborhoodUpper

#print axioms KakeyaTwoScale.enlargedEnvelope_pos
