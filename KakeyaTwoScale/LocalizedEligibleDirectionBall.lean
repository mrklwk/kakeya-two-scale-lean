module
public import KakeyaTwoScale.LocalizedChartBoxes
public import KakeyaTwoScale.CaptureSlabBank
public import KakeyaTwoScale.CaptureRelationGeometry

@[expose] public section

open Set Metric
noncomputable section
namespace KakeyaTwoScale

/-- A finite slab bank, fixed before all real data, places each actual captured
line's entire perturbed slope ball in the universal eligible relation. A single
concrete intercept is used for every perturbed slope and every level. -/
theorem localized_eligible_direction_ball (n : ℕ) (C : ℝ) (hC : 0≤C) :
    ∃ K : ℕ, 0<K ∧ ∀ (r e D : ℕ) (h : Fin (n+1)) (outer : Fin r)
      (P : Fin r→Fin e→MvPolynomial (Fin (n+1)) ℝ),
    (∀ i j, (P i j).totalDegree≤D) →
    ∀ (b : Fin r→EuclideanSpace ℝ (Fin (n+1)))
      (c u center w : EuclideanSpace ℝ (Fin (n+1))) (L : Fin r→ℝ) (ell delta rho : ℝ),
    ‖u‖=1 → 1/(n+2:ℝ)≤u h → 0<ell → 0<delta → 0<rho →
    (∀ i, 0<L i) → (∀ i, L i≤1) → (∀ i, delta≤L i) → (∀ i, ell≤L i) →
    (∀ i, 8*rho≤L i) →
    (∀ i, flatCylinder c u ell delta⊆flatCylinder (b i) u (L i) delta) →
    w∈flatCylinder c u ell delta → dist w center<C*ell →
    (∀ i, flatCylinder (b i) u (L i) delta⊆thickening rho (captureZeroSet (P i))) →
    ∃ q∈Finset.Icc (-(K:ℤ)) (K:ℤ),
      ball (chartSlope h u) (delta/(16*(n+2:ℝ)*(C+3))) ⊆
        {v | universalEligibleLine D C h outer
          (captureParameters P center L (rho+delta)
            ((q:ℝ)*L outer/(16*(n+2:ℝ))) (L outer/(16*(n+2:ℝ))))
          v (chartIntercept h (c-center) u 0)} := by
  obtain ⟨K,hK,hbank⟩ := uniform_capture_slab_bank n (C+3) (by linarith)
  refine ⟨K,hK,?_⟩
  intro r e D h outer P hP b c u center w L ell delta rho hu hh hell hdelta hrho
    hL hLone hdeltaL hellL hlong hcontain hw hwb hcapture
  have hup : 0<u h := (one_div_pos.mpr (by positivity : 0<(n+2:ℝ))).trans_le hh
  let start : Fin r→ℝ := fun i => (b i-center) h+(L i/4)*u h
  have hfixed (i) := middleHalfHeights_fixed_interval h (b i) u center (L i) (hL i) hh
  have htime (i) := localized_middleHalfHeights_bound h (b i) u center w (L i) ell delta C
    hu (hL i) hdelta (hdeltaL i) (hellL i) hC (hcontain i hw) hwb
  have hstart (i) : |start i|≤(C+3)*L i := by
    have hLi := hL i
    apply htime i (start i) (hfixed i ?_)
    exact ⟨le_rfl,le_add_of_nonneg_right (by positivity)⟩
  obtain ⟨q,hq,hslab⟩ := hbank (L outer) (hL outer) (start outer) (hstart outer)
  refine ⟨q,hq,?_⟩
  intro v hv
  have hball := localized_cylinder_fixed_intercept_ball h b c u center w
    (fun i => captureZeroSet (P i)) L ell delta rho C hu hup.ne' hell hdelta hC hL hLone
    hdeltaL hellL hlong hcontain hw hwb hcapture hv
  have hpos : 0<rho+delta := add_pos hrho hdelta
  refine ⟨hpos,div_pos (hL outer) (by positivity),hL,?_,?_,?_,?_⟩
  · exact perturbed_chart_slope_box h u delta C hu hh ((hdeltaL outer).trans (hLone outer)) hC v hv
  · exact localized_chart_intercept_box h c u center w ell delta C hu hh
      ((hellL outer).trans (hLone outer)) ((hdeltaL outer).trans (hLone outer)) hC hw hwb
  · intro i
    have hLi := hL i
    refine ⟨start i,?_,?_,?_⟩
    · simpa only [captureParameters,neg_mul] using (abs_le.mp (hstart i)).1
    · have hb := htime i (start i+L i/(4*(n+2:ℝ)))
        (hfixed i ⟨le_add_of_nonneg_right (by positivity),le_rfl⟩)
      exact (abs_le.mp hb).2
    · intro t ht
      apply (universalCaptureNear_geometry D C h P hP center L (rho+delta)
        ((q:ℝ)*L outer/(16*(n+2:ℝ))) (L outer/(16*(n+2:ℝ))) hpos i
        (mul_nonneg (by linarith) (hL i).le) v _ t).mpr
      exact hball i t (hfixed i ht)
  · intro t ht
    apply (universalCaptureNear_geometry D C h P hP center L (rho+delta)
      ((q:ℝ)*L outer/(16*(n+2:ℝ))) (L outer/(16*(n+2:ℝ))) hpos outer
      (mul_nonneg (by linarith) (hL outer).le) v _ t).mpr
    exact hball outer t (hfixed outer (hslab ht))

end KakeyaTwoScale
#print axioms KakeyaTwoScale.localized_eligible_direction_ball
