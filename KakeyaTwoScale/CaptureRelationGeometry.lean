module
public import KakeyaTwoScale.UniversalCaptureRelation
public import KakeyaTwoScale.LocalizedCylinderDirectionBall

@[expose] public section

open Set Metric MvPolynomial
noncomputable section
namespace KakeyaTwoScale

/-- Literal coefficient insertion for the geometric data, with no choice or
complexity constant depending on the values of those coefficients. -/
def captureParameters {n r e : ℕ} (P : Fin r → Fin e → MvPolynomial (Fin (n+1)) ℝ)
    (center : EuclideanSpace ℝ (Fin (n+1))) (L : Fin r → ℝ) (rho s ell : ℝ) :
    CaptureParameter n r e → ℝ
  | .coefficient i j a => (P i j).coeff a
  | .center k => center k
  | .length i => L i
  | .radius => rho
  | .slabStart => s
  | .slabLength => ell

def captureZeroSet {n e : ℕ} (P : Fin e → MvPolynomial (Fin (n+1)) ℝ) :
    Set (EuclideanSpace ℝ (Fin (n+1))) := {x | ∀ j, eval x.ofLp (P j)=0}

theorem euclidean_sum_sq_dist {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) :
    (∑ k, (x k-y k)^2)=dist x y^2 := by
  rw [dist_eq_norm,EuclideanSpace.real_norm_sq_eq]
  rfl

/-- The formula's inequalities are exactly Euclidean truncated-variety capture,
not an algebraic proxy or a sup-norm replacement. Positivity removes the
extraneous negative-radius solutions of squared inequalities. -/
theorem universalCapturePoint_geometry {n r e : ℕ} (D : ℕ) (C : ℝ) (h : Fin (n+1))
    (P : Fin r → Fin e → MvPolynomial (Fin (n+1)) ℝ)
    (hP : ∀ i j, (P i j).totalDegree ≤ D)
    (center : EuclideanSpace ℝ (Fin (n+1))) (L : Fin r → ℝ) (rho s ell : ℝ)
    (hrho : 0 < rho) (i : Fin r) (hR : 0 ≤ (C+4)*L i)
    (v a : Fin n → ℝ) (t : ℝ) (y : Fin (n+1) → ℝ) :
    universalCapturePoint D C h (captureParameters P center L rho s ell) v a i t y ↔
      (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin (n+1))) ∈
        captureZeroSet (P i) ∩ closedBall center ((C+4)*L i) ∧
      dist (center+euclideanUnsplit h (t,a+t • v)) (WithLp.toLp 2 y) < rho := by
  have he (j) := universalCapturePolynomial_specialize D P
    (captureParameters P center L rho s ell) (fun _ _ _ => rfl) hP i j y
  have hb := euclidean_sum_sq_dist (WithLp.toLp 2 y) center
  have hd := euclidean_sum_sq_dist (center+euclideanUnsplit h (t,a+t • v)) (WithLp.toLp 2 y)
  change ((∀ j, universalCapturePolynomial D (captureParameters P center L rho s ell) i j y=0) ∧
    (∑ k, (y k-center k)^2) ≤ ((C+4)*L i)^2 ∧
    (∑ k, (center k+h.insertNth (α := fun _ => ℝ) t (fun j => a j+t*v j) k-y k)^2)<rho^2) ↔ _
  simp only [he]
  rw [hb]
  change ((∀ j, eval y (P i j)=0) ∧ _ ∧
    (∑ k, ((center+euclideanUnsplit h (t,a+t • v)) k-(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin (n+1))) k)^2)<rho^2) ↔ _
  rw [hd,sq_le_sq₀ dist_nonneg hR,sq_lt_sq₀ dist_nonneg hrho.le]
  change (_ ∧ _ ∧ _) ↔ ((_ ∧ _) ∧ _)
  tauto

/-- Eliminating the point witness preserves the literal open thickening. -/
theorem universalCaptureNear_geometry {n r e : ℕ} (D : ℕ) (C : ℝ) (h : Fin (n+1))
    (P : Fin r → Fin e → MvPolynomial (Fin (n+1)) ℝ)
    (hP : ∀ i j, (P i j).totalDegree ≤ D)
    (center : EuclideanSpace ℝ (Fin (n+1))) (L : Fin r → ℝ) (rho s ell : ℝ)
    (hrho : 0 < rho) (i : Fin r) (hR : 0 ≤ (C+4)*L i)
    (v a : Fin n → ℝ) (t : ℝ) :
    universalCaptureNear D C h (captureParameters P center L rho s ell) v a i t ↔
      center+euclideanUnsplit h (t,a+t • v) ∈
        thickening rho (captureZeroSet (P i) ∩ closedBall center ((C+4)*L i)) := by
  constructor
  · rintro ⟨y,hy⟩
    have hy' := (universalCapturePoint_geometry D C h P hP center L rho s ell hrho i hR v a t y).mp hy
    exact mem_thickening_iff.mpr ⟨WithLp.toLp 2 y,hy'⟩
  · intro hx
    obtain ⟨y,hy,hd⟩ := mem_thickening_iff.mp hx
    refine ⟨y.ofLp,?_⟩
    apply (universalCapturePoint_geometry D C h P hP center L rho s ell hrho i hR v a t y.ofLp).mpr
    exact ⟨hy,hd⟩

end KakeyaTwoScale
#print axioms KakeyaTwoScale.universalCapturePoint_geometry
#print axioms KakeyaTwoScale.universalCaptureNear_geometry
