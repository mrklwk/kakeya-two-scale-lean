module
public import KakeyaTwoScale.SelectedAncestorSurvival
public import KakeyaTwoScale.UniformStageLoss

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- Actual cube-owned seed grains: their individual mass cap and retained
original mass force a grain count. No leaf-sum surrogate is assumed. -/
theorem actual_seed_grain_count {T C G : Type*}
    [DecidableEq T] [DecidableEq C] [DecidableEq G]
    (Z : Finset T) (cube : T → C) (cubes : Finset C) (grain : C → G)
    {p H eta cap : ℝ} (hp : 0 < p)
    (hret : eta*H ≤ tupleCubeMass Z cube cubes p)
    (hcap : ∀ g ∈ Z.image (grain ∘ cube),
      tupleCubeMass (Z.filter fun y => grain (cube y)=g) cube cubes p ≤ cap) :
    eta*H ≤ ((Z.image (grain ∘ cube)).card:ℝ)*cap := by
  have hs := selected_mass_le_ancestor_mass Z Z cube cubes grain (Finset.Subset.refl _) hp
  have hb := Finset.sum_le_sum hcap
  simpa only [Finset.sum_const,nsmul_eq_mul] using hret.trans (hs.trans hb)

/-- The log seed inequality from ONE common depth and the SAME counted
physical seed. h,c are log cardinalities; b=log B, a=log cellular cap,
z=log crossing/B. All retention/binning costs belong in loss. -/
theorem synchronized_seed_log_bound {d s b a z loss hOld hNew cOld cNew K : ℝ}
    (hd : 0 < d) (_hs : 0 ≤ s)
    (hgrains : hOld+s*(d*b-a)-loss ≤ hNew)
    (hpieces : cNew ≤ cOld+K+s*(b+z)) :
    cNew-hNew/d ≤ cOld-hOld/d+K+loss/d+s*(z+a/d) := by
  apply (mul_le_mul_iff_right₀ hd).mp
  have hmul := mul_le_mul_of_nonneg_right hpieces hd.le
  field_simp
  nlinarith

/-- The B-dependent mass-floor depth estimate absorbs accumulated crossing
and cellular constants, with an independently chosen error coefficient. -/
theorem cellular_depth_error {d b a s logH rate gamma : ℝ}
    (hgap : 0 < d*b-a) (hs : 0 ≤ s) (hrate : 0 ≤ rate)
    (hdepth : s*(d*b-a) ≤ logH)
    (hsmall : rate ≤ gamma*(d*b-a)) :
    s*rate ≤ gamma*logH := by
  have hg : 0 ≤ gamma := by nlinarith
  have h1 := mul_le_mul_of_nonneg_left hsmall hs
  have h2 := mul_le_mul_of_nonneg_left hdepth hg
  nlinarith

/-- Closed accumulated seed implication. The hypotheses are explicitly
numerical consequences to be supplied by an actual geometric construction. -/
theorem synchronized_seed_absorbed {d s b a z loss hOld hNew cOld cNew K logH gamma : ℝ}
    (hd : 0 < d) (hs : 0 ≤ s) (hgap : 0 < d*b-a)
    (hrate : 0 ≤ z+a/d) (hsmall : z+a/d ≤ gamma*(d*b-a))
    (hdepth : s*(d*b-a) ≤ logH)
    (hgrains : hOld+s*(d*b-a)-loss ≤ hNew)
    (hpieces : cNew ≤ cOld+K+s*(b+z)) :
    cNew-hNew/d ≤ cOld-hOld/d+K+loss/d+gamma*logH := by
  have h1 := synchronized_seed_log_bound hd hs hgrains hpieces
  have h2 := cellular_depth_error hgap hs hrate hdepth hsmall
  linarith

/-- A new degree is introduced once; the old product and old grain count
remain the same symbols in the normalization target. -/
theorem coherent_seed_target_log {d hOld hNew productOld family : ℝ} (hd : d ≠ 0) :
    family+productOld+(hNew-hOld)/d-hNew =
      (family+productOld-hOld/d)+(1/d-1)*hNew := by
  field_simp
  ring

/-- Explicit sufficient logarithmic degree threshold, after all incoming
cellular constants and the requested accuracy are fixed. -/
theorem seed_accuracy_threshold {d a z gamma b : ℝ}
    (hd : 0 < d) (hg : 0 < gamma) (hz : z ≤ 1)
    (hb : (a+(1+a/d)/gamma)/d ≤ b) :
    z+a/d ≤ gamma*(d*b-a) := by
  have h1 := (div_le_iff₀ hd).mp hb
  have h2 : (1+a/d)/gamma ≤ d*b-a := by linarith
  have h3 := (div_le_iff₀ hg).mp h2
  nlinarith

end KakeyaTwoScale
#print axioms KakeyaTwoScale.actual_seed_grain_count
#print axioms KakeyaTwoScale.synchronized_seed_log_bound
#print axioms KakeyaTwoScale.cellular_depth_error
#print axioms KakeyaTwoScale.synchronized_seed_absorbed
#print axioms KakeyaTwoScale.coherent_seed_target_log

#print axioms KakeyaTwoScale.seed_accuracy_threshold
