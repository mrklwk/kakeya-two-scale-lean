module
public import KakeyaTwoScale.GlobalParentMass
public import KakeyaTwoScale.ZahlExponents

@[expose] public section

open Filter
noncomputable section
namespace KakeyaTwoScale

/-- Exact conversion of the physical broad powers at delta=rho^20. The loss
is parameterized in the final dimension exponent, after dividing by B. -/
theorem broad_dyadic_scale (n k η : ℝ) (q : ℕ) :
    (dyadicRadius (20*q))^(n-zahlB n k+η)*(dyadicRadius q)^(k-1) =
      Real.exp (-Real.log 2*20*(n-(zahlB n k-(k-1)/20)+η)*q) := by
  unfold dyadicRadius
  rw [← Real.exp_mul,← Real.exp_mul,← Real.exp_add]
  congr 1
  push_cast
  ring

/-- A uniform polynomial retained-mass bound absorbs any nonnegative broad
mass power. The actual broad estimates may hold only on an unbounded set. -/
theorem broadTransfer_of_uniform_mass (n k p cU : ℝ) (fine U : ℕ → ℝ)
    (hp : 0≤p) (hcU : 0<cU)
    (hpos : ∀ᶠ q : ℕ in atTop, 0≤fine q ∧ 0≤U q)
    (hmass : ∀ᶠ q : ℕ in atTop, cU/(q:ℝ)≤U q)
    (hphysical : ∀ η : ℝ, 0<η → ∃ c : ℝ, 0<c ∧ ∃ᶠ q : ℕ in atTop,
      c*(dyadicRadius (20*q))^(n-zahlB n k+η)*(dyadicRadius q)^(k-1)*(U q)^p ≤ fine q) :
    BroadTransfer n k fine := by
  intro η hη
  obtain ⟨c,hc,h⟩ := hphysical η hη
  refine ⟨c*cU^p,by positivity,p,?_⟩
  apply (h.and_eventually (hpos.and (hmass.and (eventually_gt_atTop 0)))).mono
  intro q hq
  obtain ⟨ht,hpos,hm,hqpos⟩ := hq
  have hs := broad_dyadic_scale n k η q
  have ht' : c*Real.exp (-Real.log 2*20*(n-(zahlB n k-(k-1)/20)+η)*q)*(U q)^p ≤ fine q*1 := by
    rw [← hs]
    simpa only [mul_one,mul_assoc] using ht
  have hr := polynomial_loss_transfer (q:ℝ) _ (fine q) (U q) 1 p c cU 1 1 0
    (by exact_mod_cast hqpos) hpos.1 hpos.2 hp hc hcU (by norm_num)
    (by simpa using hm) (by simp) ht'
  simpa using hr

/-- Frequent broad scales versus eventual narrow scales, with the same
retained family and epsilon-independent branch predicate throughout. -/
theorem transfer_dichotomy_of_physical_scales (n k p cU cN : ℝ)
    (fine coarse U : ℕ → ℝ) (P : ℕ → Prop)
    (hp : 0≤p) (hcU : 0<cU) (hcN : 0<cN)
    (hpos : ∀ᶠ q : ℕ in atTop, 0≤fine q ∧ 0≤coarse q ∧ 0≤U q)
    (hmass : ∀ᶠ q : ℕ in atTop, cU/((q:ℝ)+1)≤U q)
    (hbroad : ∀ η : ℝ, 0<η → ∃ c : ℝ, 0<c ∧ ∀ᶠ q : ℕ in atTop, P q →
      c*(dyadicRadius (20*q))^(n-zahlB n k+η)*(dyadicRadius q)^(k-1)*(U q)^p ≤ fine q)
    (hnarrow : ∀ᶠ q : ℕ in atTop, ¬P q →
      cN*Real.exp (-Real.log 2*transferExponent n k*q)*(U q)^retainedPower ≤
        volumeProduct fine coarse q*(q:ℝ)) :
    BroadTransfer n k fine ∨ NarrowTransfer n k fine coarse := by
  have hm : ∀ᶠ q : ℕ in atTop, (cU/2)/(q:ℝ)≤U q := by
    filter_upwards [hmass,eventually_ge_atTop 1] with q hq hq1
    exact reciprocal_succ_mass hcU.le hq1 hq
  by_cases hP : ∃ᶠ q : ℕ in atTop, P q
  · left
    apply broadTransfer_of_uniform_mass n k p (cU/2) fine U hp (by positivity)
      (hpos.mono fun _ h => ⟨h.1,h.2.2⟩) hm
    intro η hη
    obtain ⟨c,hc,h⟩ := hbroad η hη
    exact ⟨c,hc,(hP.and_eventually h).mono fun _ hq => hq.2 hq.1⟩
  · right
    apply narrowTransfer_of_uniform_mass_and_loss n k fine coarse U (fun q => (q:ℝ))
      cN (cU/2) 1 1 1 hcN (by positivity) (by norm_num) hpos
      (by simpa using hm) (Eventually.of_forall fun _ => by simp)
    exact ((Filter.not_frequently.mp hP).and hnarrow).frequently.mono fun _ hq => hq.2 hq.1

end KakeyaTwoScale
#print axioms KakeyaTwoScale.broad_dyadic_scale
#print axioms KakeyaTwoScale.broadTransfer_of_uniform_mass
#print axioms KakeyaTwoScale.transfer_dichotomy_of_physical_scales
