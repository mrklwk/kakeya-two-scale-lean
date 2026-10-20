module
public import KakeyaTwoScale.NestedTubeSweepContainment
public import KakeyaTwoScale.UniversalCaptureSweep

@[expose] public section

open Set Metric
noncomputable section
namespace KakeyaTwoScale

theorem chart_affine_point {n : ℕ} (h : Fin (n+1))
    (center : EuclideanSpace ℝ (Fin (n+1))) (a v : Fin n→ℝ) (t : ℝ) :
    center+euclideanUnsplit h (t,a+t • v)=
      (center+euclideanUnsplit h (0,a))+t • euclideanUnsplit h (1,v) := by
  change center+euclideanUnsplit h (t,segmentPoint a v t)=_
  rw [unsplit_graph_point]
  module

theorem chart_affine_speed {n : ℕ} (h : Fin (n+1)) (v : Fin n→ℝ) :
    1≤‖euclideanUnsplit h (1,v)‖ := by
  simpa only [Real.norm_eq_abs,graphVector_height,abs_one] using
    PiLp.norm_apply_le (euclideanUnsplit h (1,v)) h

theorem nestedCenter_specialize {n r e : ℕ}
    (P : Fin r→Fin e→MvPolynomial (Fin (n+1)) ℝ)
    (center : EuclideanSpace ℝ (Fin (n+1))) (L A : Fin r→ℝ) (rho : ℝ) :
    nestedCenter (nestedRecursionParameters P center L A rho)=center := by
  apply PiLp.ext
  intro j
  rfl

/-- Every line in the literal universal eligible relation has the same affine
base/vector at all levels and actual captured working intervals. -/
theorem eligibleLine_nested_capture {n r e : ℕ} (D : ℕ) (C : ℝ) (hC : 0≤C)
    (h : Fin (n+1)) (outer : Fin r)
    (P : Fin r→Fin e→MvPolynomial (Fin (n+1)) ℝ) (hP : ∀ i j, (P i j).totalDegree≤D)
    (center : EuclideanSpace ℝ (Fin (n+1))) (L A : Fin r→ℝ) (rho s ell : ℝ)
    (v a : Fin n→ℝ)
    (helig : universalEligibleLine D C h outer (captureParameters P center L rho s ell) v a)
    (levels : List (Fin r)) :
    ∃ starts, nestedLineCapture D (C+4) levels (nestedRecursionParameters P center L A rho)
      (center+euclideanUnsplit h (0,a)) (euclideanUnsplit h (1,v)) starts := by
  have hrho : 0<rho := helig.1
  have hL : ∀ i,0<L i := helig.2.2.1
  have hlevels : ∀ i, ∃ t, universalCaptureInterval D C h
      (captureParameters P center L rho s ell) v a i t (L i/(4*(n+2:ℝ))) := by
    intro i
    obtain ⟨t,_ht0,_ht1,hint⟩ := helig.2.2.2.2.2.1 i
    exact ⟨t,hint⟩
  choose starts hstarts using hlevels
  refine ⟨starts,?_⟩
  intro i _hi t ht
  change (center+euclideanUnsplit h (0,a))+t • euclideanUnsplit h (1,v)∈
    thickening rho (nestedPolynomialZero D (nestedRecursionParameters P center L A rho) i∩
      closedBall (nestedCenter (nestedRecursionParameters P center L A rho)) ((C+4)*L i))
  rw [nestedPolynomialZero_specialize D P hP center L A rho i,nestedCenter_specialize,← chart_affine_point]
  apply (universalCaptureNear_geometry D C h P hP center L rho s ell hrho i
    (mul_nonneg (by linarith) (hL i).le) v a t).mp
  apply hstarts i t
  have he : recursionKappa n*L i=L i/(4*(n+2:ℝ)) := by unfold recursionKappa; ring
  simpa only [nestedRecursionParameters,Sum.elim_inl,captureParameters,he] using ht

/-- The fixed slab of every eligible line lies in the exact recursively
constructed target, using full-point containment rather than a shortened axis. -/
theorem eligibleLine_nested_slab {n r e : ℕ} (D : ℕ) (C : ℝ) (hC : 0≤C)
    (h : Fin (n+1)) (outer : Fin r) (rest : List (Fin r))
    (P : Fin r→Fin e→MvPolynomial (Fin (n+1)) ℝ) (hP : ∀ i j, (P i j).totalDegree≤D)
    (center : EuclideanSpace ℝ (Fin (n+1))) (L A : Fin r→ℝ) (rho s ell : ℝ)
    (hscale : ∀ i∈outer::rest, 0<L i ∧ rho≤L i/4)
    (hchain : (outer::rest).IsChain (fun i j => L j≤L i ∧ A i=recursionDilation n (C+4)*L i/L j))
    (v a : Fin n→ℝ)
    (helig : universalEligibleLine D C h outer (captureParameters P center L rho s ell) v a) :
    ∀ t∈Icc s (s+ell), center+euclideanUnsplit h (t,a+t • v)∈
      nestedTubeSet D (C+4) (recursionKappa n) (recursionBeta n) (outer::rest)
        (nestedRecursionParameters P center L A rho) := by
  obtain ⟨starts,hcapture⟩ := eligibleLine_nested_capture D C hC h outer P hP center L A rho s ell
    v a helig (outer::rest)
  intro t ht
  rw [chart_affine_point]
  apply nestedTubeSet_retains_captured_point D (C+4) _ _ _ starts outer rest
    (by linarith) helig.1 (chart_affine_speed h v) hscale hchain hcapture t
  rw [nestedPolynomialZero_specialize D P hP center L A rho outer,nestedCenter_specialize,← chart_affine_point]
  exact (universalCaptureNear_geometry D C h P hP center L rho s ell helig.1 outer
    (mul_nonneg (by linarith) (hscale outer (by simp)).1.le) v a t).mp (helig.2.2.2.2.2.2 t ht)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.chart_affine_point
#print axioms KakeyaTwoScale.eligibleLine_nested_capture
#print axioms KakeyaTwoScale.eligibleLine_nested_slab
