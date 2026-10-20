module
public import KakeyaTwoScale.PolynomialCoefficients
public import KakeyaTwoScale.SignedPolynomialMass

@[expose] public section

open MeasureTheory
noncomputable section
namespace KakeyaTwoScale

abbrev CoefficientSphere (ι : Type*) [Fintype ι] :=
  {c : EuclideanSpace ℝ ι // ‖c‖=1}

def coefficientAntipode {ι : Type*} [Fintype ι] (c : CoefficientSphere ι) :
    CoefficientSphere ι := ⟨-c.val,by simpa using c.property⟩

theorem coefficientSphere_nonzero {ι : Type*} [Fintype ι] (c : CoefficientSphere ι) :
    c.val≠0 := by
  intro h
  have hp := c.property
  rw [h,norm_zero] at hp
  norm_num at hp

def sphereSignedMass {ι : Type*} [Fintype ι] {n : ℕ}
    (m : ι → (Fin n →₀ ℕ)) (w : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : CoefficientSphere ι) : ℝ :=
  euclideanSignedPolynomialMass (coefficientPolynomial m c.val) w

/-- The actual signed-mass map on a finite Euclidean coefficient sphere is
continuous. Nullity is established separately at every nonzero polynomial. -/
theorem continuous_sphereSignedMass {ι : Type*} [Fintype ι] {n : ℕ}
    (m : ι → (Fin n →₀ ℕ)) (hm : Function.Injective m)
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : Integrable w volume) :
    Continuous (sphereSignedMass m w) := by
  apply continuous_iff_continuousAt.mpr
  intro c
  apply continuousAt_euclideanSignedPolynomialMass
    (fun c : CoefficientSphere ι => coefficientPolynomial m c.val) c
    (coefficientPolynomial_nonzero m hm c.val (coefficientSphere_nonzero c)) w hw
  intro x
  exact ((coefficientPolynomial_eval_continuous m (fun i => x i)).comp continuous_subtype_val).continuousAt

theorem sphereSignedMass_odd {ι : Type*} [Fintype ι] {n : ℕ}
    (m : ι → (Fin n →₀ ℕ)) (w : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : CoefficientSphere ι) :
    sphereSignedMass m w (coefficientAntipode c) = -sphereSignedMass m w c := by
  simp only [sphereSignedMass,coefficientAntipode,coefficientPolynomial_neg,euclideanSignedPolynomialMass_neg]

/-- The concrete odd vector map whose zero would bisect a finite list of
integrable densities. Existence of such a zero is not asserted here. -/
def polynomialMassVector {ι : Type*} [Fintype ι] {n M : ℕ}
    (m : ι → (Fin n →₀ ℕ)) (w : Fin M → EuclideanSpace ℝ (Fin n) → ℝ)
    (c : CoefficientSphere ι) : EuclideanSpace ℝ (Fin M) :=
  WithLp.toLp 2 (fun j => sphereSignedMass m (w j) c)

theorem continuous_polynomialMassVector {ι : Type*} [Fintype ι] {n M : ℕ}
    (m : ι → (Fin n →₀ ℕ)) (hm : Function.Injective m)
    (w : Fin M → EuclideanSpace ℝ (Fin n) → ℝ) (hw : ∀ j, Integrable (w j) volume) :
    Continuous (polynomialMassVector m w) := by
  exact (PiLp.continuous_toLp 2 (fun _ : Fin M => ℝ)).comp
    (continuous_pi (fun j => continuous_sphereSignedMass m hm (w j) (hw j)))

theorem polynomialMassVector_odd {ι : Type*} [Fintype ι] {n M : ℕ}
    (m : ι → (Fin n →₀ ℕ)) (w : Fin M → EuclideanSpace ℝ (Fin n) → ℝ)
    (c : CoefficientSphere ι) :
    polynomialMassVector m w (coefficientAntipode c) = -polynomialMassVector m w c := by
  ext j
  exact sphereSignedMass_odd m (w j) c

/-- A zero of the constructed map gives simultaneous exact bisections by an
actual nonzero polynomial, with the proved quantitative degree bound. -/
theorem box_massVector_zero_bisects (n D M : ℕ)
    (w : Fin M → EuclideanSpace ℝ (Fin n) → ℝ) (hw : ∀ j, Integrable (w j) volume)
    (c : CoefficientSphere (Fin n → Fin (D+1)))
    (hc : polynomialMassVector (boxMonomial n D) w c=0) :
    ∃ p : MvPolynomial (Fin n) ℝ, p≠0 ∧ p.totalDegree≤n*D ∧ ∀ j,
      (∫ x in {x : EuclideanSpace ℝ (Fin n) | 0<MvPolynomial.eval (fun i => x i) p}, w j x)=
        (∫ x, w j x)/2 ∧
      (∫ x in {x : EuclideanSpace ℝ (Fin n) | MvPolynomial.eval (fun i => x i) p<0}, w j x)=
        (∫ x, w j x)/2 := by
  let p := coefficientPolynomial (boxMonomial n D) c.val
  have hp : p≠0 := coefficientPolynomial_nonzero _ (boxMonomial_injective n D) c.val
    (coefficientSphere_nonzero c)
  refine ⟨p,hp,boxCoefficientPolynomial_degree n D c.val,?_⟩
  intro j
  apply euclideanSignedPolynomialMass_zero_bisects p hp (w j) (hw j)
  exact congrArg (fun x : EuclideanSpace ℝ (Fin M) => x j) hc

end KakeyaTwoScale
#print axioms KakeyaTwoScale.continuous_sphereSignedMass
#print axioms KakeyaTwoScale.sphereSignedMass_odd
#print axioms KakeyaTwoScale.continuous_polynomialMassVector
#print axioms KakeyaTwoScale.polynomialMassVector_odd
#print axioms KakeyaTwoScale.box_massVector_zero_bisects
