module
public import KakeyaTwoScale.PolynomialZeroNull
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

open MeasureTheory Filter
open scoped Topology
noncomputable section
namespace KakeyaTwoScale

def realSign (x : ℝ) : ℝ := if 0<x then 1 else if x<0 then -1 else 0

theorem abs_realSign_le_one (x : ℝ) : |realSign x|≤1 := by
  unfold realSign
  split_ifs <;> norm_num

theorem realSign_neg (x : ℝ) : realSign (-x) = -realSign x := by
  rcases lt_trichotomy x 0 with h | h | h
  · simp [realSign,h,show 0< -x by linarith,show ¬0<x by linarith]
  · simp [h,realSign]
  · simp [realSign,h,show -x<0 by linarith,show ¬0< -x by linarith]

theorem measurable_realSign : Measurable realSign := by
  unfold realSign
  exact Measurable.ite measurableSet_Ioi measurable_const
    (Measurable.ite measurableSet_Iio measurable_const measurable_const)

theorem continuousAt_realSign {x : ℝ} (hx : x≠0) : ContinuousAt realSign x := by
  rcases lt_or_gt_of_ne hx with hn | hp
  · apply (continuousAt_const (y:=(-1:ℝ))).congr_of_eventuallyEq
    filter_upwards [isOpen_Iio.mem_nhds hn] with y hy
    change y<0 at hy
    simp [realSign,hy,show ¬0<y by linarith]
  · apply (continuousAt_const (y:=(1:ℝ))).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioi.mem_nhds hp] with y hy
    change 0<y at hy
    simp [realSign,hy]

/-- Signed mass is dominated by the absolute value of the original density. -/
theorem integrable_realSign_mul {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (f w : A → ℝ) (hf : Measurable f) (hw : Integrable w μ) :
    Integrable (fun x => realSign (f x)*w x) μ := by
  apply hw.norm.mono' ((measurable_realSign.comp hf).aestronglyMeasurable.mul hw.aestronglyMeasurable)
  exact Eventually.of_forall (fun x => by
    change ‖realSign (f x)*w x‖≤‖w x‖
    rw [norm_mul,Real.norm_eq_abs (realSign (f x))]
    exact mul_le_of_le_one_left (norm_nonneg _) (abs_realSign_le_one _))

/-- Local dominated convergence needs nullity only at the limiting member. -/
theorem continuousAt_signed_mass {X A : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    [MeasurableSpace A] (μ : Measure A) (f : X → A → ℝ) (w : A → ℝ) (c : X)
    (hf : ∀ c, Measurable (f c)) (hw : Integrable w μ)
    (hcont : ∀ x, ContinuousAt (fun c => f c x) c)
    (hzero : ∀ᵐ x ∂μ, f c x≠0) :
    ContinuousAt (fun c => ∫ x, realSign (f c x)*w x ∂μ) c := by
  apply continuousAt_of_dominated (bound:=fun x => ‖w x‖)
  · exact Eventually.of_forall (fun c => (integrable_realSign_mul μ (f c) w (hf c) hw).aestronglyMeasurable)
  · exact Eventually.of_forall (fun c => Eventually.of_forall (fun x => by
      rw [norm_mul,Real.norm_eq_abs (realSign (f c x))]
      exact mul_le_of_le_one_left (norm_nonneg _) (abs_realSign_le_one _)))
  · exact hw.norm
  · filter_upwards [hzero] with x hx
    have hc : ContinuousAt (fun y : X => realSign (f y x)) c :=
      ContinuousAt.comp (f:=fun y : X => f y x) (continuousAt_realSign hx) (hcont x)
    exact hc.mul continuousAt_const

def signedPolynomialMass {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (w : (Fin n → ℝ) → ℝ) : ℝ :=
  ∫ x, realSign (MvPolynomial.eval x p)*w x

theorem integrable_signedPolynomialMass {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (w : (Fin n → ℝ) → ℝ) (hw : Integrable w volume) :
    Integrable (fun x => realSign (MvPolynomial.eval x p)*w x) volume :=
  integrable_realSign_mul volume _ w p.continuous_eval.measurable hw

theorem signedPolynomialMass_neg {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (w : (Fin n → ℝ) → ℝ) : signedPolynomialMass (-p) w = -signedPolynomialMass p w := by
  simp only [signedPolynomialMass,map_neg,realSign_neg,neg_mul,integral_neg]

def euclideanSignedPolynomialMass {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (w : EuclideanSpace ℝ (Fin n) → ℝ) : ℝ :=
  ∫ x, realSign (MvPolynomial.eval (fun i => x i) p)*w x

theorem euclideanSignedPolynomialMass_neg {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (w : EuclideanSpace ℝ (Fin n) → ℝ) :
    euclideanSignedPolynomialMass (-p) w = -euclideanSignedPolynomialMass p w := by
  simp only [euclideanSignedPolynomialMass,map_neg,realSign_neg,neg_mul,integral_neg]

/-- The signed integral is exactly the positive-side mass minus negative-side mass. -/
theorem signed_mass_eq_positive_sub_negative {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (f w : A → ℝ) (hf : Measurable f) (hw : Integrable w μ) :
    (∫ x, realSign (f x)*w x ∂μ) =
      (∫ x in {x | 0<f x}, w x ∂μ) - ∫ x in {x | f x<0}, w x ∂μ := by
  have hpos : MeasurableSet {x | 0<f x} := measurableSet_lt measurable_const hf
  have hneg : MeasurableSet {x | f x<0} := measurableSet_lt hf measurable_const
  have he : (fun x => realSign (f x)*w x) =
      (fun x => ({x | 0<f x} : Set A).indicator w x - ({x | f x<0} : Set A).indicator w x) := by
    funext x
    rcases lt_trichotomy (f x) 0 with h | h | h
    · simp [realSign,h,show ¬0<f x by linarith]
    · simp [realSign,h]
    · simp [realSign,h,show ¬f x<0 by linarith]
  rw [he,integral_sub (hw.indicator hpos) (hw.indicator hneg),integral_indicator hpos,
    integral_indicator hneg]

/-- Zero signed mass gives exact bisection once the zero locus carries no mass. -/
theorem signed_mass_zero_bisects {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (f w : A → ℝ) (hf : Measurable f) (hw : Integrable w μ)
    (hzero : ∀ᵐ x ∂μ, f x≠0) (hmass : (∫ x, realSign (f x)*w x ∂μ)=0) :
    (∫ x in {x | 0<f x}, w x ∂μ)=(∫ x, w x ∂μ)/2 ∧
    (∫ x in {x | f x<0}, w x ∂μ)=(∫ x, w x ∂μ)/2 := by
  have hpos : MeasurableSet {x | 0<f x} := measurableSet_lt measurable_const hf
  have hneg : MeasurableSet {x | f x<0} := measurableSet_lt hf measurable_const
  have he : (fun x => ({x | 0<f x} : Set A).indicator w x +
      ({x | f x<0} : Set A).indicator w x) =ᵐ[μ] w := by
    filter_upwards [hzero] with x hx
    rcases lt_or_gt_of_ne hx with hn | hp
    · simp [hn,show ¬0<f x by linarith]
    · simp [hp,show ¬f x<0 by linarith]
  have hs := integral_congr_ae he
  rw [integral_add (hw.indicator hpos) (hw.indicator hneg),integral_indicator hpos,
    integral_indicator hneg] at hs
  rw [signed_mass_eq_positive_sub_negative μ f w hf hw] at hmass
  constructor <;> linarith

/-- At every nonzero member of a parameterized polynomial family, signed mass
is continuous. Nullity is proved for that member, not assumed for the family. -/
theorem continuousAt_signedPolynomialMass {X : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] {n : ℕ} (P : X → MvPolynomial (Fin n) ℝ)
    (c : X) (hP : P c≠0) (w : (Fin n → ℝ) → ℝ) (hw : Integrable w volume)
    (hcont : ∀ x : Fin n → ℝ, ContinuousAt (fun y => MvPolynomial.eval x (P y)) c) :
    ContinuousAt (fun y => signedPolynomialMass (P y) w) c := by
  apply continuousAt_signed_mass volume (fun y x => MvPolynomial.eval x (P y)) w c
    (fun y => (P y).continuous_eval.measurable) hw hcont
  apply ae_iff.mpr
  simpa only [not_not] using polynomial_zero_volume (P c) hP

theorem continuousAt_euclideanSignedPolynomialMass {X : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] {n : ℕ} (P : X → MvPolynomial (Fin n) ℝ)
    (c : X) (hP : P c≠0) (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : Integrable w volume)
    (hcont : ∀ x : EuclideanSpace ℝ (Fin n),
      ContinuousAt (fun y => MvPolynomial.eval (fun i => x i) (P y)) c) :
    ContinuousAt (fun y => euclideanSignedPolynomialMass (P y) w) c := by
  have hm (y : X) : Measurable (fun x : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (WithLp.ofLp x) (P y)) :=
    ((P y).continuous_eval.comp (PiLp.continuous_ofLp 2 (fun _ : Fin n => ℝ))).measurable
  apply continuousAt_signed_mass volume (fun (y : X) (x : EuclideanSpace ℝ (Fin n)) =>
    MvPolynomial.eval (WithLp.ofLp x) (P y)) w c hm hw hcont
  apply ae_iff.mpr
  simpa only [not_not,Function.comp_apply] using polynomial_zero_volume_euclidean (P c) hP

theorem signedPolynomialMass_zero_bisects {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hp : p≠0) (w : (Fin n → ℝ) → ℝ) (hw : Integrable w volume)
    (hmass : signedPolynomialMass p w=0) :
    (∫ x in {x | 0<MvPolynomial.eval x p}, w x)=(∫ x, w x)/2 ∧
    (∫ x in {x | MvPolynomial.eval x p<0}, w x)=(∫ x, w x)/2 := by
  apply signed_mass_zero_bisects volume _ w p.continuous_eval.measurable hw _ hmass
  apply ae_iff.mpr
  simpa only [not_not] using polynomial_zero_volume p hp

theorem euclideanSignedPolynomialMass_zero_bisects {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hp : p≠0) (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : Integrable w volume)
    (hmass : euclideanSignedPolynomialMass p w=0) :
    (∫ x in {x : EuclideanSpace ℝ (Fin n) | 0<MvPolynomial.eval (fun i => x i) p}, w x)=(∫ x, w x)/2 ∧
    (∫ x in {x : EuclideanSpace ℝ (Fin n) | MvPolynomial.eval (fun i => x i) p<0}, w x)=(∫ x, w x)/2 := by
  apply signed_mass_zero_bisects volume _ w
    (p.continuous_eval.comp (PiLp.continuous_ofLp 2 (fun _ : Fin n => ℝ))).measurable hw _ hmass
  apply ae_iff.mpr
  simpa only [not_not,Function.comp_apply] using polynomial_zero_volume_euclidean p hp

end KakeyaTwoScale
#print axioms KakeyaTwoScale.continuousAt_signed_mass

#print axioms KakeyaTwoScale.signedPolynomialMass_neg

#print axioms KakeyaTwoScale.signed_mass_zero_bisects

#print axioms KakeyaTwoScale.continuousAt_signedPolynomialMass
#print axioms KakeyaTwoScale.continuousAt_euclideanSignedPolynomialMass
#print axioms KakeyaTwoScale.euclideanSignedPolynomialMass_zero_bisects
