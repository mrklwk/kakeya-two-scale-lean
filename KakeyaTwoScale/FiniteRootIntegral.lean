module
public import KakeyaTwoScale.FiniteRootIncidence
public import KakeyaTwoScale.JointBandMassUpper

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
namespace KakeyaTwoScale
open Classical

/-- Continuous original tuple sums are dominated by their finite actual
cube-incidence bank. The bound uses exact half-open cube volume delta^d. -/
theorem tuple_lintegral_le_root_mass {d k N : ℕ} (hk : 0<k)
    (delta : ℝ) (hd : 0<delta) (cubes : Finset (Fin d→ℤ)) (F : Finset (Fin k→Fin N))
    (T : Fin N→Set (EuclideanSpace ℝ (Fin d)))
    (hbank : ∀o x, x∈T o → gridIndex delta (WithLp.ofLp x)∈cubes)
    (w : (Fin k→Fin N)→ℝ) (M p : ℝ) (hM : 0≤M) (hp : 0<p)
    (hw0 : ∀f∈F, 0≤w f) (hw : ∀f∈F, w f≤M) :
    (∫⁻x, ENNReal.ofReal ((∑f∈F, w f*∏j, (T (f j)).indicator (fun _ => (1:ℝ)) x)^p)) ≤
      ENNReal.ofReal (M^p*delta^d*
        tupleCubeMass (rootIncidenceTuples delta cubes F T) Prod.fst
          ((rootIncidenceTuples delta cubes F T).image Prod.fst) p) := by
  let Y := rootIncidenceTuples delta cubes F T
  let cap (z : Fin d→ℤ) : ℝ := ParentLevel.capacity Y Prod.fst z
  let f (x : EuclideanSpace ℝ (Fin d)) :=
    ∑a∈F, w a*∏j, (T (a j)).indicator (fun _ => (1:ℝ)) x
  let g (z : Fin d→ℤ) := (rootGridCube delta z).indicator (fun _ => ENNReal.ofReal ((M*cap z)^p))
  have hf0 (x) : 0≤f x := Finset.sum_nonneg (fun a ha => mul_nonneg (hw0 a ha)
    (Finset.prod_nonneg (fun j _ => Set.indicator_nonneg (fun _ _ => by norm_num) x)))
  have hpoint (x) : ENNReal.ofReal ((f x)^p)≤∑z∈cubes, g z x := by
    let z := gridIndex delta (WithLp.ofLp x)
    have hx : x∈rootGridCube delta z := mem_own_gridCell hd _
    by_cases hz : z∈cubes
    · have hh := tuple_sum_le_root_capacity delta cubes F T w M hM hw z hz x hx
      have hg : g z x=ENNReal.ofReal ((M*cap z)^p) := Set.indicator_of_mem hx _
      exact (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (hf0 x) hh hp.le)).trans
        (by rw [←hg]; exact Finset.single_le_sum (f:=fun z => g z x) (fun _ _ => zero_le) hz)
    · have he : f x=0 := by
        apply Finset.sum_eq_zero
        intro a ha
        have hnot : ¬∀j, x∈T (a j) := by
          intro hj
          exact hz (hbank (a ⟨0,hk⟩) x (hj ⟨0,hk⟩))
        rw [tuple_indicator_product,ite_eq_right hnot,mul_zero]
      rw [he,Real.zero_rpow hp.ne',ENNReal.ofReal_zero]
      exact zero_le
  have hmeas (z) : Measurable (g z) := measurable_const.indicator (rootGridCube_measurable delta z)
  have hlin : (∫⁻x, ENNReal.ofReal ((f x)^p))≤∑z∈cubes, ∫⁻x, g z x := by
    calc
      _ ≤ ∫⁻x, ∑z∈cubes, g z x := lintegral_mono hpoint
      _ = _ := lintegral_finsetSum _ (fun z _ => hmeas z)
  have hint (z) : (∫⁻x, g z x)=ENNReal.ofReal (M^p*delta^d*(cap z)^p) := by
    rw [show g z=(rootGridCube delta z).indicator (fun _ => ENNReal.ofReal ((M*cap z)^p)) from rfl,
      lintegral_indicator (rootGridCube_measurable delta z),lintegral_const,Measure.restrict_apply_univ,rootGridCube_volume]
    rw [Real.mul_rpow hM (Nat.cast_nonneg _),ENNReal.ofReal_mul (Real.rpow_nonneg hM _),
      ←ENNReal.ofReal_pow hd.le]
    rw [ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hM _) (pow_nonneg hd.le d)),
      ENNReal.ofReal_mul (Real.rpow_nonneg hM _)]
    ring
  have hs : Y.image Prod.fst⊆cubes := by
    intro z hz
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hz
    exact ((rootIncidenceTuples_mem delta cubes F T y).mp hy).1
  calc
    _ ≤ ∑z∈cubes, ENNReal.ofReal (M^p*delta^d*(cap z)^p) := by simpa only [hint] using hlin
    _ = ENNReal.ofReal (∑z∈cubes, M^p*delta^d*(cap z)^p) :=
      (ENNReal.ofReal_sum_of_nonneg (fun z _ => by dsimp only [cap]; positivity)).symm
    _ = _ := by
      rw [←Finset.mul_sum]
      change ENNReal.ofReal (M^p*delta^d*tupleCubeMass Y Prod.fst cubes p)=_
      rw [tupleCubeMass_image Y Prod.fst cubes p hp hs]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.tuple_lintegral_le_root_mass
