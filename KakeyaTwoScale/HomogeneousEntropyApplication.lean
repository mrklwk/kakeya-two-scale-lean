module
public import KakeyaTwoScale.FiniteEntropyChain

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical
open scoped BigOperators

theorem finiteEntropy_congr {A : Type*} (S : Finset A) (q p : A → ℝ)
    (he : ∀ x ∈ S, q x = p x) : finiteEntropy S q = finiteEntropy S p := by
  unfold finiteEntropy
  congr 1
  exact Finset.sum_congr rfl (fun x hx => by rw [he x hx])

/-- The actual joint law has exactly the prescribed marginal and uniform
conditional fibers, so its joint entropy has the required decomposition. -/
theorem jointFiberLaw_entropy (G : Finset (ℤ × ℤ)) (hG : G.Nonempty) (p : ℝ) :
    finiteEntropy G (jointFiberLaw G p) =
      finiteEntropy (slopeSupport G) (fiberLaw (slopeSupport G) (slopeMass G) p)+
      ∑ v ∈ slopeSupport G, fiberLaw (slopeSupport G) (slopeMass G) p v * Real.log (slopeMass G v) := by
  have h := finiteEntropy_chain_rule G (jointFiberLaw G p) Prod.snd
    (fun z hz => jointFiberLaw_pos G hG p hz)
  have hm : ∀ v ∈ slopeSupport G,
      finitePushLaw G (jointFiberLaw G p) Prod.snd v = fiberLaw (slopeSupport G) (slopeMass G) p v := by
    intro v hv
    exact jointFiberLaw_marginal G p hv
  have he := finiteEntropy_congr (slopeSupport G) _ _ hm
  change finiteEntropy G (jointFiberLaw G p) =
    finiteEntropy (slopeSupport G) (finitePushLaw G (jointFiberLaw G p) Prod.snd)+_ at h
  rw [he] at h
  rw [h]
  congr 1
  apply Finset.sum_congr rfl
  intro v hv
  rw [hm v hv]
  have hc : finiteEntropy (slopeFiber G v)
      (fun z => jointFiberLaw G p z/fiberLaw (slopeSupport G) (slopeMass G) p v) =
      Real.log (slopeMass G v) := by
    rw [finiteEntropy_congr _ _ (fun _ => (slopeMass G v)⁻¹)
      (fun z hz => jointFiberLaw_conditional G hG p hv hz)]
    exact finiteEntropy_uniform _ (slopeFiber_nonempty hv)
  exact congrArg (fun e => fiberLaw (slopeSupport G) (slopeMass G) p v*e) hc

/-- Exact homogeneous entropy expression for the source's optimized law. -/
theorem jointFiber_partition_identity (G : Finset (ℤ × ℤ)) (hG : G.Nonempty) (p : ℝ) :
    p*finiteEntropy G (jointFiberLaw G p)+(1-p)*
      finiteEntropy (slopeSupport G) (fiberLaw (slopeSupport G) (slopeMass G) p) =
      Real.log (fiberPartition (slopeSupport G) (slopeMass G) p) := by
  rw [jointFiberLaw_entropy G hG p]
  have h := fiberLaw_entropy_identity (slopeSupport G) (slopeMass G) p (hG.image _) (slopeMass_pos G)
  nlinarith only [h]

/-- CONDITIONAL application only: the homogeneous entropy inequality is
explicitly supplied. This theorem does not prove PZ homogenization. It
verifies the exact scalar conclusion once that missing bridge is available. -/
theorem source_partition_bound_of_homogeneous_entropy
    (G : Finset (ℤ × ℤ)) (hG : G.Nonempty) (r : ℚ)
    (hh : (252/373:ℝ)*finiteEntropy G (jointFiberLaw G (252/373))+
      (121/373:ℝ)*finiteEntropy (slopeSupport G)
        (fiberLaw (slopeSupport G) (slopeMass G) (252/373)) ≤
      (625/373:ℝ)*finiteEntropy (G.image (fun z => (z.1:ℚ)+r*z.2))
        (finitePushLaw G (jointFiberLaw G (252/373)) (fun z => (z.1:ℚ)+r*z.2))) :
    fiberPartition (slopeSupport G) (slopeMass G) (252/373) ≤
      ((G.image (fun z => (z.1:ℚ)+r*z.2)).card:ℝ)^(625/373:ℝ) := by
  have hid := jointFiber_partition_identity G hG (252/373)
  norm_num only [show (1:ℝ)-252/373 = 121/373 by norm_num] at hid
  rw [hid] at hh
  have hb := mul_le_mul_of_nonneg_left (rational_projection_entropy_bound G hG (252/373) r)
    (show (0:ℝ) ≤ 625/373 by norm_num)
  have hc : (0:ℝ) < (G.image (fun z => (z.1:ℚ)+r*z.2)).card := by
    exact_mod_cast Finset.card_pos.mpr (hG.image _)
  have he := Real.exp_le_exp.mpr (hh.trans hb)
  have hz : 0 < fiberPartition (slopeSupport G) (slopeMass G) (252/373) :=
    fiberPartition_pos _ _ _ (hG.image _) (slopeMass_pos G)
  rw [Real.exp_log hz] at he
  simpa only [Real.rpow_def_of_pos hc,mul_comm (Real.log _)] using he

end KakeyaTwoScale
#print axioms KakeyaTwoScale.finiteEntropy_congr
#print axioms KakeyaTwoScale.jointFiberLaw_entropy
#print axioms KakeyaTwoScale.jointFiber_partition_identity
#print axioms KakeyaTwoScale.source_partition_bound_of_homogeneous_entropy
