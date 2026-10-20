module
public import KakeyaTwoScale.FixedProjectionRegularChart
public import KakeyaTwoScale.BufferedProjectionCapture

@[expose] public section

open Set Metric
open scoped NNReal
noncomputable section
namespace KakeyaTwoScale

/-- General closed-fiber buffered capture derived from pointwise differential
regularity. Local sections, their radii, and the capture point are constructed.
The projection is fixed; no global injectivity, proper projection, or successful
path-lifting premise is required. Polynomial Gauss-minor estimates and generic
transverse level selection are separate obligations. -/
theorem exists_fixed_projection_fiber_capture {E F V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [ProperSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (f : E → F) (hf : Continuous f) (value : F)
    (π : E →L[ℝ] V) (g : E → ℝ) (hg : Continuous g)
    (hderiv : ∀ y, f y = value → 0 < g y →
      ∃ (A : E →L[ℝ] F) (B : V →L[ℝ] E),
        HasStrictFDerivAt f A y ∧ A.range = ⊤ ∧
        A.comp B = 0 ∧ π.comp B = ContinuousLinearMap.id ℝ V ∧
        (∀ x, A x = 0 → π x = 0 → x = 0) ∧ ‖B‖₊ < 2)
    (z : E) (hz : f z = value) (hgz : 0 ≤ g z) (v : V) :
    ∃ y, f y = value ∧ 0 ≤ g y ∧ dist y z ≤ 2 * dist (π z) v ∧
      (π y = v ∨ g y = 0) := by
  apply exists_projection_target_or_gauss_boundary {y | f y = value}
    (isClosed_eq hf continuous_const) g hg π π.continuous _ z hz hgz v
  intro y hy hgy
  obtain ⟨A,B,hA,hrange,hAB,hπB,hinj,hB⟩ := hderiv y hy hgy
  obtain ⟨L,hBL,hL⟩ := exists_between hB
  obtain ⟨σ,r,hr,hσ,hLip,hsec⟩ := fixed_projection_positive_chart
    f A π y hA hrange (fixed_projection_kernel_complement A π B hAB hπB hinj)
    B hAB hπB L hBL g hg.continuousAt hgy
  refine ⟨r,L,σ,hr,?_,hσ,hLip,?_⟩
  · exact_mod_cast hL
  · intro a ha
    obtain ⟨hfa,hga,hpa⟩ := hsec a ha
    exact ⟨hfa.trans hy,le_of_lt hga,hpa⟩

/-- Whole-set capture from differential data, with no assumed local sections.
The selected endpoint is shared by all points of Q, so one actual successor
captures the entire cube. -/
theorem whole_set_fixed_projection_fiber_capture {E F V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [ProperSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (f : E → F) (hf : Continuous f) (value : F)
    (π : E →L[ℝ] V) (hπ : ‖π‖₊ ≤ 1) (g : E → ℝ) (hg : Continuous g)
    (hderiv : ∀ y, f y = value → 0 < g y →
      ∃ (A : E →L[ℝ] F) (B : V →L[ℝ] E),
        HasStrictFDerivAt f A y ∧ A.range = ⊤ ∧
        A.comp B = 0 ∧ π.comp B = ContinuousLinearMap.id ℝ V ∧
        (∀ x, A x = 0 → π x = 0 → x = 0) ∧ ‖B‖₊ < 2)
    (Q : Set E) (T : Set V) (z : E) (hz : f z = value) (hgz : 0 ≤ g z)
    (η r : ℝ) (hnear : ∀ x ∈ Q, dist x z < η)
    (hbad : ∃ x ∈ Q, π x ∈ thickening r T) :
    Q ⊆ thickening (η+2*(η+r)) ({y | f y = value} ∩ π ⁻¹' T) ∨
    Q ⊆ thickening (η+2*(η+r)) ({y | f y = value} ∩ {y | g y = 0}) := by
  obtain ⟨x,hx,hbad⟩ := hbad
  obtain ⟨v,hv,hxv⟩ := mem_thickening_iff.mp hbad
  have hproj : dist (π z) (π x) ≤ dist z x := by
    simpa using (π.lipschitzWith.weaken hπ).dist_le_mul z x
  have hnx : dist z x < η := by simpa only [dist_comm] using hnear x hx
  have hzv : dist (π z) v < η+r := by
    linarith [dist_triangle (π z) (π x) v]
  obtain ⟨y,hy,_,hyz,halt⟩ := exists_fixed_projection_fiber_capture
    f hf value π g hg hderiv z hz hgz v
  have hclose : ∀ q ∈ Q, dist q y < η+2*(η+r) := by
    intro q hq
    have hnq := hnear q hq
    have htri := dist_triangle q z y
    rw [dist_comm z y] at htri
    linarith
  rcases halt with ht | hg0
  · exact Or.inl (fun q hq => mem_thickening_iff.mpr
      ⟨y,⟨hy,by simpa only [mem_preimage,ht] using hv⟩,hclose q hq⟩)
  · exact Or.inr (fun q hq => mem_thickening_iff.mpr
      ⟨y,⟨hy,hg0⟩,hclose q hq⟩)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.exists_fixed_projection_fiber_capture

#print axioms KakeyaTwoScale.whole_set_fixed_projection_fiber_capture
