module
public import KakeyaTwoScale.OrthogonalRegularChart

@[expose] public section

open Set Filter Metric
open scoped Topology NNReal
noncomputable section
namespace KakeyaTwoScale

/-- Actual shrinking creates both core and buffered graph domains. No buffered
coverage hypothesis is assumed. The positive radius is not degree-uniform. -/
theorem orthogonal_regular_buffered_chart {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : E → F) (A : E →L[ℝ] F) (a : E)
    (hf : HasStrictFDerivAt f A a) (hA : A.range = ⊤) :
    ∃ π : E → A.ker, ∃ φ : A.ker → E, ∃ r : ℝ, 0 < r ∧
      LipschitzWith 1 π ∧ π a = 0 ∧ φ 0 = a ∧
      LipschitzOnWith 2 φ (ball 0 (2*r)) ∧
      (∀ y ∈ ball 0 (2*r), π (φ y) = y ∧ f (φ y) = f a) ∧
      (∃ U ∈ 𝓝 a, ∀ x ∈ U, π x ∈ ball 0 r ∧ (f x=f a ↔ φ (π x)=x)) ∧
      (∀ Z : Set A.ker, ∀ η ρ : ℝ, η+ρ ≤ r → ∀ x : E,
        x ∈ thickening η (φ '' ball 0 r) → π x ∈ thickening ρ Z →
        x ∈ thickening (3*η+2*ρ) ({z | f z=f a} ∩ π ⁻¹' Z)) := by
  obtain ⟨π,φ,V,hV,U,hU,hπ,hπa,hφa,hLip,hsection,hcover⟩ :=
    orthogonal_regular_chart f A a hf hA
  obtain ⟨R,hR,hRV⟩ := Metric.mem_nhds_iff.mp hV
  let r := R/2
  have hr : 0 < r := half_pos hR
  have hbig : ball (0 : A.ker) (2*r) ⊆ V := by
    simpa only [r,mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using hRV
  have hsmall : ball (0 : A.ker) r ⊆ ball 0 (2*r) := ball_subset_ball (by linarith)
  have hW : U ∩ π ⁻¹' ball (0 : A.ker) r ∈ 𝓝 a :=
    inter_mem hU (hπ.continuous.continuousAt.preimage_mem_nhds
      (by rw [hπa]; exact ball_mem_nhds _ hr))
  refine ⟨π,φ,r,hr,hπ,hπa,hφa,hLip.mono hbig,?_,?_,?_⟩
  · exact fun y hy => hsection y (hbig hy)
  · refine ⟨_,hW,?_⟩
    intro x hx
    refine ⟨hx.2,?_⟩
    constructor
    · intro heq
      obtain ⟨y,hy,hyx⟩ := (hcover x hx.1).mp heq
      have he := (hsection y hy).1
      rw [hyx] at he
      rw [he,hyx]
    · intro heq
      have hh := (hsection (π x) (hbig (hsmall hx.2))).2
      rwa [heq] at hh
  · intro Z η ρ hsum x hx hz
    have hbuf : ∀ y ∈ ball (0 : A.ker) r, ball y (η+ρ) ⊆ ball 0 (2*r) := by
      intro y hy z hz
      rw [mem_ball] at hy hz ⊢
      calc
        dist z 0 ≤ dist z y + dist y 0 := dist_triangle _ _ _
        _ < (η+ρ)+r := add_lt_add hz hy
        _ ≤ 2*r := by linarith
    have hh := graph_wall_bridge π φ (ball 0 r) (ball 0 (2*r)) Z
      {z | f z=f a} 2 hπ (hLip.mono hbig) hsmall
      (fun y hy => (hsection y (hbig hy)).1)
      (fun y hy => (hsection y (hbig hy)).2) η ρ hbuf hx hz
    have he : η + 2*(η+ρ) = 3*η+2*ρ := by ring
    simpa only [NNReal.coe_ofNat,he] using hh

end KakeyaTwoScale
#print axioms KakeyaTwoScale.orthogonal_regular_buffered_chart
