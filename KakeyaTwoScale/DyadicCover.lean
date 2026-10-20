module
public import KakeyaTwoScale.CoveringVolume
public import KakeyaTwoScale.TwoScaleCertificate

@[expose] public section

open MeasureTheory Metric Filter
noncomputable section
namespace KakeyaTwoScale

def dyadicRadius (q : ℕ) : ℝ := Real.exp (-Real.log 2*q)

 theorem dyadicRadius_mul (p q : ℕ) : dyadicRadius (p*q) = (dyadicRadius q)^p := by
  unfold dyadicRadius
  rw [← Real.exp_nat_mul]
  push_cast
  congr 1
  ring

def neighborhoodVolume {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (q : ℕ) : ℝ :=
  volume.real (thickening (dyadicRadius q) K)

def ballConstant (n : ℕ) : ℝ :=
  (ENNReal.ofReal (Real.sqrt Real.pi^n/Real.Gamma ((n:ℝ)/2+1))).toReal

/-- A concrete upper bound on metric covering numbers at dyadic scales. -/
def DyadicCoverGrowth {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (d : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q →
    ∃ centers : Finset (EuclideanSpace ℝ (Fin n)),
      K ⊆ ⋃ c ∈ centers, ball c (dyadicRadius q) ∧
      (centers.card:ℝ) ≤ C*Real.exp (Real.log 2*d*q)

 theorem dyadic_cover_volume_bound (n : ℕ) [NeZero n]
    (K : Set (EuclideanSpace ℝ (Fin n))) (q : ℕ) (d C : ℝ)
    (_hC : 0 < C) (centers : Finset (EuclideanSpace ℝ (Fin n)))
    (hcover : K ⊆ ⋃ c ∈ centers, ball c (dyadicRadius q))
    (hcard : (centers.card:ℝ) ≤ C*Real.exp (Real.log 2*d*q)) :
    neighborhoodVolume K q ≤ (C*2^n*ballConstant n)*
      Real.exp (-Real.log 2*((n:ℝ)-d)*q) := by
  have h := neighborhood_real_volume_le_cover n K centers (dyadicRadius q)
    (Real.exp_pos _).le hcover
  have hr : 0 < dyadicRadius q := Real.exp_pos _
  have hB : 0 ≤ ballConstant n := ENNReal.toReal_nonneg
  change neighborhoodVolume K q ≤ (centers.card:ℝ)*(2*dyadicRadius q)^n*ballConstant n at h
  calc
    neighborhoodVolume K q ≤ (C*Real.exp (Real.log 2*d*q))*(2*dyadicRadius q)^n*ballConstant n :=
      h.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcard (by positivity)) hB)
    _ = _ := by
      rw [mul_pow]
      unfold dyadicRadius
      rw [← Real.exp_nat_mul]
      calc
        _ = (C*2^n*ballConstant n)*
          (Real.exp (Real.log 2*d*q)*Real.exp ((n:ℝ)*(-Real.log 2*q))) := by ring
        _ = _ := by rw [← Real.exp_add]; congr 2; ring

 theorem DyadicCoverGrowth.volume_bound {n : ℕ} [NeZero n]
    {K : Set (EuclideanSpace ℝ (Fin n))} {d : ℝ} (H : DyadicCoverGrowth K d) :
    ∃ C : ℝ, 0 < C ∧ ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q →
      neighborhoodVolume K q ≤ C*Real.exp (-Real.log 2*((n:ℝ)-d)*q) := by
  obtain ⟨C,hC,Q,h⟩ := H
  refine ⟨C*2^n*(ballConstant n+1), ?_, Q, ?_⟩
  · have : 0 ≤ ballConstant n := ENNReal.toReal_nonneg
    positivity
  · intro q hq
    obtain ⟨centers,hcover,hcard⟩ := h q hq
    have hv := dyadic_cover_volume_bound n K q d C hC centers hcover hcard
    have he : 0 < Real.exp (-Real.log 2*((n:ℝ)-d)*q) := Real.exp_pos _
    have hcoef : C*2^n*ballConstant n ≤ C*2^n*(ballConstant n+1) := by
      have : 0 < C*2^n := by positivity
      nlinarith
    exact hv.trans (mul_le_mul_of_nonneg_right hcoef he.le)
end KakeyaTwoScale
#print axioms KakeyaTwoScale.dyadic_cover_volume_bound
#print axioms KakeyaTwoScale.DyadicCoverGrowth.volume_bound
