module
public import KakeyaTwoScale.SmoothInjectiveHypersurfaceChart
public import KakeyaTwoScale.EuclideanHypersurfaceCharts
public import KakeyaTwoScale.ChartDirectedArea

@[expose] public section

open MvPolynomial MeasureTheory Set
open scoped ENNReal ContDiff
noncomputable section
namespace KakeyaTwoScale

/-- A smooth injective coordinate chart with an explicitly measurable image. -/
structure SmoothCoordinateChart (n : ℕ) where
  map : (Fin n → ℝ) → (Fin (n+1) → ℝ)
  source : Set (Fin n → ℝ)
  isOpen_source : IsOpen source
  smooth : ContDiffOn ℝ ∞ map source
  injective : InjOn map source
  measurable_image : MeasurableSet (map '' source)

def SmoothCoordinateChart.empty (n : ℕ) : SmoothCoordinateChart n where
  map := fun _ => 0
  source := ∅
  isOpen_source := isOpen_empty
  smooth := contDiffOn_const
  injective := by simp
  measurable_image := by simp

/-- A regular polynomial zero has a genuine smooth coordinate chart. An arbitrary
linear coordinate equivalence suffices: later cofactor integrals use its actual derivative. -/
theorem polynomial_coordinate_chart {n : ℕ} (Q : MvPolynomial (Fin (n+1)) ℝ)
    (a : Fin (n+1) → ℝ) (ha : eval a Q = 0)
    (hr : ∃ j, eval a (pderiv j Q) ≠ 0) :
    ∃ C : SmoothCoordinateChart n, ∃ W : Set (Fin (n+1) → ℝ),
      IsOpen W ∧ a ∈ W ∧ C.map '' C.source = W ∩ {x | eval x Q = 0} := by
  let E := EuclideanSpace ℝ (Fin (n+1))
  let b : E ≃L[ℝ] (Fin (n+1) → ℝ) := PiLp.continuousLinearEquiv 2 ℝ (fun _ => ℝ)
  let aE : E := b.symm a
  let h : E → ℝ := fun x => eval x Q
  have hne : (fderiv ℝ h aE).toLinearMap ≠ 0 :=
    polynomial_euclidean_fderiv_ne_zero Q aE hr
  obtain ⟨φ,U,W,hU,h0,hW,haW,hφ0,hinj,hsm,himage,hdim⟩ :=
    smooth_local_level_set_chart h (polynomial_eval_contDiff Q ∞) aE hne
  let K := (fderiv ℝ h aE).ker
  have hdimK : Module.finrank ℝ K = n := by
    have he : Module.finrank ℝ K + 1 = n+1 := by simpa [E] using hdim
    omega
  let e : (Fin n → ℝ) ≃L[ℝ] K :=
    (LinearEquiv.ofFinrankEq (Fin n → ℝ) K (by simp [hdimK])).toContinuousLinearEquiv
  let ψ := fun x => b (φ (e x))
  let V := e ⁻¹' U
  let O := b.symm ⁻¹' W
  have hV : IsOpen V := hU.preimage e.continuous
  have hO : IsOpen O := hW.preimage b.symm.continuous
  have hψ : ContDiffOn ℝ ∞ ψ V :=
    b.contDiff.comp_contDiffOn (hsm.comp e.contDiff.contDiffOn (fun _ hx => hx))
  have hiψ : InjOn ψ V := by
    intro x hx y hy he
    exact e.injective (hinj hx hy (b.injective he))
  have hi : ψ '' V = O ∩ {x | eval x Q = 0} := by
    ext x
    constructor
    · rintro ⟨t,ht,rfl⟩
      have hm : φ (e t) ∈ {z | z ∈ W ∧ h z = h aE} := by
        rw [← himage]
        exact ⟨e t,ht,rfl⟩
      refine ⟨?_,?_⟩
      · change b.symm (b (φ (e t))) ∈ W
        simpa using hm.1
      · change h (φ (e t)) = 0
        exact hm.2.trans ha
    · rintro ⟨hx,hz⟩
      have hm : b.symm x ∈ φ '' U := by
        rw [himage]
        exact ⟨hx,hz.trans ha.symm⟩
      obtain ⟨t,ht,he⟩ := hm
      refine ⟨e.symm t,?_,?_⟩
      · change e (e.symm t) ∈ U
        simpa using ht
      · change b (φ (e (e.symm t))) = x
        simp only [e.apply_symm_apply,he,b.apply_symm_apply]
  have hm : MeasurableSet (ψ '' V) := by
    rw [hi]
    exact hO.measurableSet.inter (isClosed_eq Q.continuous_eval continuous_const).measurableSet
  exact ⟨⟨ψ,V,hV,hψ,hiψ,hm⟩,O,hO,haW,hi⟩

end KakeyaTwoScale
#print axioms KakeyaTwoScale.polynomial_coordinate_chart
