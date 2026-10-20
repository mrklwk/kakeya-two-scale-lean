module
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.MetricSpace.HausdorffDimension
public import Mathlib.Tactic

@[expose] public section

open Set Metric Filter MeasureTheory
open scoped Topology NNReal ENNReal ContDiff
noncomputable section
namespace KakeyaTwoScale

universe u
/-- A factorial-free Taylor bound constructed by iterating the convex mean
value theorem on the actual derivative tower. -/
theorem norm_sub_le_pow_of_flat_jets_on {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (m : ℕ) :
    ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
      (f : E → F) (U : Set E) (_hU : Convex ℝ U)
      (_hf : ∀ z ∈ U, ContDiffAt ℝ (m+1) f z) (C : ℝ) (_hC : 0 ≤ C)
      (_hbound : ∀ z ∈ U, ‖iteratedFDeriv ℝ (m+1) f z‖ ≤ C)
      (x y : E) (_hx : x ∈ U) (_hy : y ∈ U)
      (_hjet : ∀ j, 1 ≤ j → j ≤ m → iteratedFDeriv ℝ j f x = 0),
      ‖f y-f x‖ ≤ C * ‖y-x‖^(m+1) := by
  induction m with
  | zero =>
    intro F _ _ f U hU hf C _ hbound x y hx hy _
    have hd : ∀ z ∈ U, ‖fderiv ℝ f z‖ ≤ C := by
      intro z hz
      have hh := hbound z hz
      change ‖iteratedFDeriv ℝ 1 f z‖ ≤ C at hh
      rwa [norm_iteratedFDeriv_one] at hh
    simpa using hU.norm_image_sub_le_of_norm_fderiv_le
      (fun z hz => (hf z hz).differentiableAt (by simp)) hd hx hy
  | succ m ih =>
    intro F _ _ f U hU hf C hC hbound x y hx hy hjet
    have hdx : fderiv ℝ f x = 0 := by
      apply norm_eq_zero.mp
      have h := congrArg norm (hjet 1 (by omega) (by omega))
      simpa only [norm_iteratedFDeriv_one, norm_zero] using h
    have hdf : ∀ z ∈ U, ContDiffAt ℝ (m+1) (fderiv ℝ f) z := by
      intro z hz
      exact (hf z hz).fderiv_right (by simp only [Nat.cast_add, Nat.cast_one]; rfl)
    have hjdf : ∀ j, 1 ≤ j → j ≤ m → iteratedFDeriv ℝ j (fderiv ℝ f) x = 0 := by
      intro j hj hjm
      apply norm_eq_zero.mp
      rw [norm_iteratedFDeriv_fderiv, hjet (j+1) (by omega) (by omega), norm_zero]
    have hbdf : ∀ z ∈ U, ‖iteratedFDeriv ℝ (m+1) (fderiv ℝ f) z‖ ≤ C := by
      intro z hz
      rw [norm_iteratedFDeriv_fderiv]
      exact hbound z hz
    have hseg : segment ℝ x y ⊆ U := hU.segment_subset hx hy
    have hd : ∀ z ∈ segment ℝ x y, ‖fderiv ℝ f z‖ ≤ C * ‖y-x‖^(m+1) := by
      intro z hz
      have h := ih (fderiv ℝ f) U hU hdf C hC hbdf x z hx (hseg hz) hjdf
      rw [hdx, sub_zero] at h
      exact h.trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le_of_mem_segment hz) _) hC)
    have h := (convex_segment x y).norm_image_sub_le_of_norm_fderiv_le
      (fun z hz => (hf z (hseg hz)).differentiableAt (by simp)) hd
      (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
    simpa only [pow_succ, mul_assoc] using h

/-- Points where the first m actual Frechet derivatives vanish. -/
def flatCriticalJetSet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (m : ℕ) : Set E :=
  {x | ∀ j, 1 ≤ j → j ≤ m → iteratedFDeriv ℝ j f x = 0}

/-- Local smoothness at the base point constructs a Holder neighborhood on
an arbitrary flat-jet subset. Smoothness is not assumed away from that subset. -/
theorem flat_jets_locally_holder_on {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (S : Set E) (m : ℕ)
    (hjet : ∀ x ∈ S, ∀ j, 1 ≤ j → j ≤ m → iteratedFDeriv ℝ j f x = 0)
    (a : E) (hf : ContDiffAt ℝ ∞ f a) :
    ∃ C : ℝ≥0, ∃ U ∈ 𝓝[S] a,
      HolderOnWith C ((m+1 : ℕ) : ℝ≥0) f U := by
  let C : ℝ := ‖iteratedFDeriv ℝ (m+1) f a‖ + 1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hc : ContinuousAt (fun x => ‖iteratedFDeriv ℝ (m+1) f x‖) a :=
    (hf.continuousAt_iteratedFDeriv (by simp)).norm
  have he : ∀ᶠ x in 𝓝 a, ‖iteratedFDeriv ℝ (m+1) f x‖ < C :=
    hc.eventually_lt continuousAt_const (by dsimp [C]; linarith)
  have hfinite : ContDiffAt ℝ (m+1) f a := hf.of_le (by simp)
  have hsmooth : ∀ᶠ x in 𝓝 a, ContDiffAt ℝ (m+1) f x :=
    hfinite.eventually (by simp)
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (he.and hsmooth)
  refine ⟨⟨C,hC⟩, ball a r ∩ S,
    by simpa only [Set.inter_comm] using inter_mem_nhdsWithin S (ball_mem_nhds a hr), ?_⟩
  intro x hx y hy
  have h := norm_sub_le_pow_of_flat_jets_on m f (ball a r) (convex_ball a r)
    (fun z hz => (hball hz).2) C hC (fun z hz => (hball hz).1.le)
    y x hy.1 hx.1 (hjet y hy.2)
  have hdist : dist (f x) (f y) ≤ C * dist x y^(m+1) := by
    simpa only [dist_eq_norm] using h
  have hh := ENNReal.ofReal_le_ofReal hdist
  simpa only [NNReal.coe_natCast, ENNReal.rpow_natCast, edist_dist,
    ENNReal.ofReal_mul hC, ENNReal.ofReal_pow dist_nonneg,
    ENNReal.ofReal_eq_coe_nnreal hC, NNReal.mk] using hh

/-- Global smoothness specialization of the actual local construction. -/
theorem flatCriticalJetSet_locally_holder {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (hf : ContDiff ℝ ∞ f) (m : ℕ) (a : E) :
    ∃ C : ℝ≥0, ∃ U ∈ 𝓝[flatCriticalJetSet f m] a,
      HolderOnWith C ((m+1 : ℕ) : ℝ≥0) f U :=
  flat_jets_locally_holder_on f (flatCriticalJetSet f m) m (fun _ hx => hx) a hf.contDiffAt

/-- Flat critical jets force a genuine image dimension drop by the actual
smooth-jet-derived local Holder estimates. -/
theorem flatCriticalJetSet_dimH_image_le {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E → ℝ) (hf : ContDiff ℝ ∞ f) (m : ℕ) :
    dimH (f '' flatCriticalJetSet f m) ≤
      (Module.finrank ℝ E : ℝ≥0∞) / (m+1 : ℕ) := by
  have h := dimH_image_le_of_locally_holder_on
    (f := f) (s := flatCriticalJetSet f m) (r := ((m+1 : ℕ) : ℝ≥0))
    (by positivity) (fun x _ => flatCriticalJetSet_locally_holder f hf m x)
  apply h.trans
  apply ENNReal.div_le_div_right
  exact (dimH_mono (subset_univ _)).trans_eq (Real.dimH_univ_eq_finrank E)

/-- For scalar output, jets through order at least dim(E) vanishing imply
zero volume of their image. This is the flat stratum of smooth scalar Sard. -/
theorem flatCriticalJetSet_image_volume_zero {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E → ℝ) (hf : ContDiff ℝ ∞ f) (m : ℕ) (hm : Module.finrank ℝ E ≤ m) :
    volume (f '' flatCriticalJetSet f m) = 0 := by
  have hdim : dimH (f '' flatCriticalJetSet f m) < (1 : ℝ≥0∞) := by
    apply (flatCriticalJetSet_dimH_image_le f hf m).trans_lt
    apply (ENNReal.div_lt_iff (by simp) (by simp)).mpr
    simp only [one_mul]
    exact_mod_cast (show Module.finrank ℝ E < m+1 by omega)
  have hz := hausdorffMeasure_of_dimH_lt (d := (1 : ℝ≥0)) hdim
  simpa only [NNReal.coe_one, hausdorffMeasure_real] using hz

/-- Arbitrary flat subsets need smoothness only AT their own points. This is
the local form suitable for induction through implicit hypersurface charts. -/
theorem flat_jet_dimH_image_le_of_contDiffAt {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E → ℝ) (S : Set E) (m : ℕ)
    (hf : ∀ x ∈ S, ContDiffAt ℝ ∞ f x)
    (hjet : ∀ x ∈ S, ∀ j, 1 ≤ j → j ≤ m → iteratedFDeriv ℝ j f x = 0) :
    dimH (f '' S) ≤ (Module.finrank ℝ E : ℝ≥0∞) / (m+1 : ℕ) := by
  have h := dimH_image_le_of_locally_holder_on
    (f := f) (s := S) (r := ((m+1 : ℕ) : ℝ≥0)) (by positivity)
    (fun x hx => flat_jets_locally_holder_on f S m hjet x (hf x hx))
  apply h.trans
  apply ENNReal.div_le_div_right
  exact (dimH_mono (subset_univ _)).trans_eq (Real.dimH_univ_eq_finrank E)

/-- Actual scalar flat-critical image nullity from local smooth jets. No
supplied Holder estimate, nullity, or globally smooth extension is assumed. -/
theorem flat_jet_image_volume_zero_of_contDiffAt {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E → ℝ) (S : Set E) (m : ℕ) (hm : Module.finrank ℝ E ≤ m)
    (hf : ∀ x ∈ S, ContDiffAt ℝ ∞ f x)
    (hjet : ∀ x ∈ S, ∀ j, 1 ≤ j → j ≤ m → iteratedFDeriv ℝ j f x = 0) :
    volume (f '' S) = 0 := by
  have hdim : dimH (f '' S) < (1 : ℝ≥0∞) := by
    apply (flat_jet_dimH_image_le_of_contDiffAt f S m hf hjet).trans_lt
    apply (ENNReal.div_lt_iff (by simp) (by simp)).mpr
    simp only [one_mul]
    exact_mod_cast (show Module.finrank ℝ E < m+1 by omega)
  have hz := hausdorffMeasure_of_dimH_lt (d := (1 : ℝ≥0)) hdim
  simpa only [NNReal.coe_one, hausdorffMeasure_real] using hz

end KakeyaTwoScale
#print axioms KakeyaTwoScale.norm_sub_le_pow_of_flat_jets_on
#print axioms KakeyaTwoScale.flat_jets_locally_holder_on

#print axioms KakeyaTwoScale.flatCriticalJetSet_locally_holder
#print axioms KakeyaTwoScale.flatCriticalJetSet_dimH_image_le
#print axioms KakeyaTwoScale.flatCriticalJetSet_image_volume_zero

#print axioms KakeyaTwoScale.flat_jet_dimH_image_le_of_contDiffAt
#print axioms KakeyaTwoScale.flat_jet_image_volume_zero_of_contDiffAt
