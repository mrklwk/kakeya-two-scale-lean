module
public import KakeyaTwoScale.NestedTubeFormula

@[expose] public section

open Set Metric MvPolynomial
noncomputable section
namespace KakeyaTwoScale

def nestedTubeSet {n r e : ℕ} (D : ℕ) (B kappa beta : ℝ) (levels : List (Fin r))
    (p : TubeRecursionParameter n r e→ℝ) : Set (EuclideanSpace ℝ (Fin (n+1))) :=
  {x | nestedTubeFormula D B kappa beta levels p x.ofLp}

def nestedPolynomialZero {n r e : ℕ} (D : ℕ) (p : TubeRecursionParameter n r e→ℝ)
    (i : Fin r) : Set (EuclideanSpace ℝ (Fin (n+1))) :=
  {x | ∀ j, universalCapturePolynomial D (fun q => p (Sum.inl q)) i j x.ofLp=0}

def nestedCenter {n r e : ℕ} (p : TubeRecursionParameter n r e→ℝ) : EuclideanSpace ℝ (Fin (n+1)) :=
  WithLp.toLp 2 (fun j => p (Sum.inl (.center j)))

theorem nestedTubeSet_singleton {n r e : ℕ} (D : ℕ) (B kappa beta : ℝ)
    (p : TubeRecursionParameter n r e→ℝ) (i : Fin r)
    (hB : 0≤B) (hrho : 0<p (Sum.inl .radius)) (hL : 0<p (Sum.inl (.length i))) :
    nestedTubeSet D B kappa beta [i] p=
      thickening (2*p (Sum.inl .radius)) (nestedPolynomialZero D p i)∩
        ball (nestedCenter p) ((B+2)*p (Sum.inl (.length i))) := by
  ext x
  change (0<p (Sum.inl (.length i)) ∧
    universalZeroNear D (fun q => p (Sum.inl q)) i x.ofLp ∧
    (∑ j, (x j-(nestedCenter p) j)^2)<((B+2)*p (Sum.inl (.length i)))^2) ↔ _
  rw [universalZeroNear_geometry D _ i hrho x,euclidean_sum_sq_dist x (nestedCenter p),
    sq_lt_sq₀ dist_nonneg (by positivity)]
  simp only [hL,true_and,mem_inter_iff,mem_ball,nestedPolynomialZero]

theorem nestedTubeSet_cons {n r e : ℕ} (D : ℕ) (B kappa beta : ℝ)
    (p : TubeRecursionParameter n r e→ℝ) (i j : Fin r) (rest : List (Fin r))
    (hrho : 0<p (Sum.inl .radius)) :
    nestedTubeSet D B kappa beta (i::j::rest) p=
      thickening (2*p (Sum.inl .radius)) (nestedPolynomialZero D p i)∩
        prescribedCylinderFat (p (Sum.inr i)) (kappa*p (Sum.inl (.length j)))
          (beta*p (Sum.inl .radius)) (nestedTubeSet D B kappa beta (j::rest) p) := by
  ext x
  change (universalZeroNear D (fun q => p (Sum.inl q)) i x.ofLp ∧
    prescribedFatFormula _ _ _ _ x.ofLp) ↔ _
  rw [universalZeroNear_geometry D _ i hrho x,prescribedFatFormula_geometry]
  rfl

/-- Exact specialization keeps the original polynomial coefficients. -/
def nestedRecursionParameters {n r e : ℕ}
    (P : Fin r→Fin e→MvPolynomial (Fin (n+1)) ℝ)
    (center : EuclideanSpace ℝ (Fin (n+1))) (L A : Fin r→ℝ) (rho : ℝ) :
    TubeRecursionParameter n r e→ℝ :=
  Sum.elim (captureParameters P center L rho 0 1) A

theorem nestedPolynomialZero_specialize {n r e : ℕ} (D : ℕ)
    (P : Fin r→Fin e→MvPolynomial (Fin (n+1)) ℝ)
    (hP : ∀ i j, (P i j).totalDegree≤D)
    (center : EuclideanSpace ℝ (Fin (n+1))) (L A : Fin r→ℝ) (rho : ℝ) (i : Fin r) :
    nestedPolynomialZero D (nestedRecursionParameters P center L A rho) i=captureZeroSet (P i) := by
  ext x
  change (∀ j, universalCapturePolynomial D (captureParameters P center L rho 0 1) i j x.ofLp=0) ↔ _
  simp only [universalCapturePolynomial_specialize D P (captureParameters P center L rho 0 1) (fun _ _ _ => rfl) hP,captureZeroSet,mem_ofPred_eq]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.nestedTubeSet_singleton
#print axioms KakeyaTwoScale.nestedTubeSet_cons
#print axioms KakeyaTwoScale.nestedPolynomialZero_specialize
