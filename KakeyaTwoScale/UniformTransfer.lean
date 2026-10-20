module
public import KakeyaTwoScale.TransferAssembly
public import KakeyaTwoScale.TwoScaleCertificate
public import KakeyaTwoScale.DyadicCover

@[expose] public section

open Filter
noncomputable section
namespace KakeyaTwoScale

/-- The power of retained mass in the source's narrow transfer inequality. -/
def retainedPower : ℝ := 2+a*a/theta

/-- Substitute the actual two-scale factors into parent-weight elimination.
Constants are retained exactly, with no asymptotic notation. -/
theorem transfer_with_scale_factors
    (n k q fine coarse u U S M eta loss cA cR cG : ℝ)
    (hf : 0 ≤ fine) (hc : 0 < coarse) (hu : 0 < u) (hU : 0 < U)
    (heta : 0 ≤ eta) (hA : 0 < cA) (hR : 0 ≤ cR) (hG : 0 ≤ cG)
    (weight : cA*Real.exp (-Real.log 2*omega n*q)*U^a ≤ coarse*u^theta)
    (represented : (cR*Real.exp (-Real.log 2*(19*omega n)*q))*u^a*U ≤ S*fine)
    (brush : (cG*Real.exp (-Real.log 2*gamma n k*q))*S*M ≤ coarse*loss)
    (threshold : M*coarse = eta*U) :
    (cG*cR*eta*cA^(a/theta))*Real.exp (-Real.log 2*transferExponent n k*q)*U^retainedPower ≤
      fine*coarse^(2+a/theta)*loss := by
  have h := transfer_of_weight_and_brush fine coarse u U S M eta loss
    (cA*Real.exp (-Real.log 2*omega n*q)*U^a)
    (cR*Real.exp (-Real.log 2*(19*omega n)*q))
    (cG*Real.exp (-Real.log 2*gamma n k*q)) hf hc hu hU.le heta
    (by positivity) (by positivity) (by positivity) weight represented brush threshold
  have he :
      (cG*Real.exp (-Real.log 2*gamma n k*q)) *
      (cR*Real.exp (-Real.log 2*(19*omega n)*q)) * eta *
      (cA*Real.exp (-Real.log 2*omega n*q)*U^a)^(a/theta)*U^2 =
      (cG*cR*eta*cA^(a/theta))*Real.exp (-Real.log 2*transferExponent n k*q)*U^retainedPower := by
    rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hU.le _),
      Real.mul_rpow hA.le (Real.exp_pos _).le, ← Real.rpow_mul hU.le, ← Real.exp_mul]
    have hp : U^(a*(a/theta))*U^2 = U^retainedPower := by
      rw [show U^2 = U^(2:ℝ) by simp, ← Real.rpow_add hU]
      congr 1
      unfold retainedPower
      ring
    calc
      _ = (cG*cR*eta*cA^(a/theta))*
          (Real.exp (-Real.log 2*gamma n k*q)*Real.exp (-Real.log 2*(19*omega n)*q)*
           Real.exp ((-Real.log 2*omega n*q)*(a/theta)))*(U^(a*(a/theta))*U^2) := by ring
      _ = _ := by
        have hexp : (-Real.log 2*gamma n k*q + -Real.log 2*(19*omega n)*q) +
            ((-Real.log 2*omega n*q)*(a/theta)) = -Real.log 2*transferExponent n k*q := by
          unfold transferExponent omega gamma a theta
          ring
        rw [hp, ← Real.exp_add, ← Real.exp_add, hexp]
  rwa [he] at h

/-- A single-scale polynomial-loss conversion with a uniform positive constant.
L and H may be arbitrary real exponents; q must be positive. -/
theorem polynomial_loss_transfer
    (q E V U loss p c cU C L H : ℝ)
    (hq : 0 < q) (hV : 0 ≤ V) (_hU : 0 ≤ U) (hp : 0 ≤ p)
    (hc : 0 < c) (hcU : 0 < cU) (hC : 0 < C)
    (hUmass : cU/q^L ≤ U) (hloss : loss ≤ C*q^H)
    (htransfer : c*Real.exp E*U^p ≤ V*loss) :
    (c*cU^p/C)*Real.exp E/q^(L*p+H) ≤ V := by
  have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ cU/q^L) hUmass hp
  rw [Real.div_rpow hcU.le (Real.rpow_nonneg hq.le _), ← Real.rpow_mul hq.le] at hpow
  have hlo := mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ c*Real.exp E)
  have hmain : c*Real.exp E*(cU^p/q^(L*p)) ≤ V*(C*q^H) :=
    hlo.trans (htransfer.trans (mul_le_mul_of_nonneg_left hloss hV))
  have hqpow : 0 < q^(L*p) := Real.rpow_pos_of_pos hq _
  have hqH : 0 < q^H := Real.rpow_pos_of_pos hq _
  rw [Real.rpow_add hq]
  apply (div_le_iff₀ (mul_pos hqpow hqH)).mpr
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hC).mpr
  have hh := (div_le_iff₀ hqpow).mp (show (c*Real.exp E*cU^p)/q^(L*p) ≤ V*(C*q^H) by
    convert hmain using 1; ring)
  nlinarith

/-- Uniform-in-scale constants convert a frequent physical transfer estimate
into the existing NarrowTransfer predicate. Constants precede q, so the result
does not permit choosing a new loss constant at each scale. -/
theorem narrowTransfer_of_uniform_mass_and_loss
    (n k : ℝ) (fine coarse U loss : ℕ → ℝ)
    (c cU C L H : ℝ) (hc : 0 < c) (hcU : 0 < cU) (hC : 0 < C)
    (hpos : ∀ᶠ q : ℕ in atTop, 0 ≤ fine q ∧ 0 ≤ coarse q ∧ 0 ≤ U q)
    (hmass : ∀ᶠ q : ℕ in atTop, cU/(q:ℝ)^L ≤ U q)
    (hloss : ∀ᶠ q : ℕ in atTop, loss q ≤ C*(q:ℝ)^H)
    (htransfer : ∃ᶠ q : ℕ in atTop,
      c*Real.exp (-Real.log 2*transferExponent n k*q)*(U q)^retainedPower ≤
        volumeProduct fine coarse q * loss q) :
    NarrowTransfer n k fine coarse := by
  refine ⟨c*cU^retainedPower/C, by positivity, L*retainedPower+H, ?_⟩
  apply (htransfer.and_eventually (hpos.and (hmass.and (hloss.and (eventually_gt_atTop 0))))).mono
  intro q hq
  obtain ⟨ht,hpos,hm,hl,hqpos⟩ := hq
  exact polynomial_loss_transfer (q:ℝ) _ (volumeProduct fine coarse q) (U q) (loss q)
    retainedPower c cU C L H (by exact_mod_cast hqpos)
    (mul_nonneg hpos.1 (Real.rpow_nonneg hpos.2.1 _)) hpos.2.2
    (by norm_num [retainedPower,a,theta]) hc hcU hC hm hl ht
/-- The dyadic logarithms appearing in the source, with fixed constants valid
for every q≥1. This includes the fine scale delta=rho^20. -/
theorem dyadic_log_loss_bounds (q : ℕ) (hq : 1 ≤ q) :
    0 < Real.log (2/dyadicRadius q) ∧
    Real.log (2/dyadicRadius q) ≤ (2*Real.log 2)*(q:ℝ) ∧
    0 < Real.log (2/dyadicRadius (20*q)) ∧
    Real.log (2/dyadicRadius (20*q)) ≤ (21*Real.log 2)*(q:ℝ) := by
  have he (j : ℕ) : Real.log (2/dyadicRadius j) = Real.log 2*((j:ℝ)+1) := by
    rw [dyadicRadius, Real.log_div (by norm_num : (2:ℝ) ≠ 0) (Real.exp_pos _).ne', Real.log_exp]
    ring
  have hq' : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [he q, he (20*q)]
  push_cast
  constructor
  · positivity
  constructor
  · nlinarith
  constructor <;> nlinarith

/-- Convert the source's fine-scale logarithmic retained-mass bound into a
polynomial bound with a single constant, uniform for all q≥1. -/
theorem retained_mass_from_dyadic_log (q : ℕ) (hq : 1 ≤ q) (c U : ℝ) (hc : 0 ≤ c)
    (hm : c/Real.log (2/dyadicRadius (20*q)) ≤ U) :
    (c/(21*Real.log 2))/(q:ℝ) ≤ U := by
  obtain ⟨_,_,hp,hb⟩ := dyadic_log_loss_bounds q hq
  calc
    _ = c/((21*Real.log 2)*(q:ℝ)) := by rw [div_div]
    _ ≤ c/Real.log (2/dyadicRadius (20*q)) := div_le_div_of_nonneg_left hc hp hb
    _ ≤ U := hm

/-- Actual-scale arithmetic, represented-parent and brush estimates imply
NarrowTransfer when all constants are fixed before q. The geometric estimates
may hold only frequently; the mass and loss controls hold eventually. -/
theorem narrowTransfer_of_uniform_scale_estimates
    (n k : ℝ) (fine coarse U loss : ℕ → ℝ)
    (eta cA cR cG cU C L H : ℝ)
    (heta : 0 < eta) (hA : 0 < cA) (hR : 0 < cR) (hG : 0 < cG)
    (hcU : 0 < cU) (hC : 0 < C)
    (hpos : ∀ᶠ q : ℕ in atTop, 0 ≤ fine q ∧ 0 < coarse q ∧ 0 < U q)
    (hmass : ∀ᶠ q : ℕ in atTop, cU/(q:ℝ)^L ≤ U q)
    (hloss : ∀ᶠ q : ℕ in atTop, loss q ≤ C*(q:ℝ)^H)
    (hgeometry : ∃ᶠ q : ℕ in atTop, ∃ u S M : ℝ, 0 < u ∧
      cA*Real.exp (-Real.log 2*omega n*q)*(U q)^a ≤ coarse q*u^theta ∧
      (cR*Real.exp (-Real.log 2*(19*omega n)*q))*u^a*(U q) ≤ S*fine q ∧
      (cG*Real.exp (-Real.log 2*gamma n k*q))*S*M ≤ coarse q*loss q ∧
      M*coarse q = eta*U q) : NarrowTransfer n k fine coarse := by
  apply narrowTransfer_of_uniform_mass_and_loss n k fine coarse U loss
    (cG*cR*eta*cA^(a/theta)) cU C L H (by positivity) hcU hC
    (hpos.mono fun _ h => ⟨h.1,h.2.1.le,h.2.2.le⟩) hmass hloss
  apply (hgeometry.and_eventually hpos).mono
  intro q hq
  obtain ⟨⟨u,S,M,hu,hw,hr,hg,ht⟩,hf,hc,hU⟩ := hq
  exact transfer_with_scale_factors n k q (fine q) (coarse q) u (U q) S M eta (loss q)
    cA cR cG hf hc hu hU heta.le hA hR.le hG.le hw hr hg ht

end KakeyaTwoScale
#print axioms KakeyaTwoScale.transfer_with_scale_factors
#print axioms KakeyaTwoScale.polynomial_loss_transfer
#print axioms KakeyaTwoScale.narrowTransfer_of_uniform_mass_and_loss

#print axioms KakeyaTwoScale.dyadic_log_loss_bounds
#print axioms KakeyaTwoScale.narrowTransfer_of_uniform_scale_estimates

#print axioms KakeyaTwoScale.retained_mass_from_dyadic_log
