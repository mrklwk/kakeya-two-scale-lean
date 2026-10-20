module
public import KakeyaTwoScale.ModularRounding
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.Group.AddCircle
public import Mathlib.MeasureTheory.Measure.Haar.Unique

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical MeasureTheory MeasureTheory.Measure
open scoped ENNReal

def circleRepresentative (x : AddCircle (1:ℝ)) : ℝ := (AddCircle.equivIco (1:ℝ) 0 x).val

def circleBin (p : ℕ) (x : AddCircle (1:ℝ)) : ZMod p := (⌊(p:ℝ)*circleRepresentative x⌋:ℤ)

theorem circleRepresentative_range (x : AddCircle (1:ℝ)) :
    0 ≤ circleRepresentative x ∧ circleRepresentative x < 1 := by
  simpa only [zero_add,Set.mem_Ico,circleRepresentative] using (AddCircle.equivIco (1:ℝ) 0 x).property

theorem circleBin_collision_norm (p : ℕ) (hp : 0 < p) (x y : AddCircle (1:ℝ))
    (h : circleBin p x = circleBin p y) : ‖x-y‖ ≤ 1/(p:ℝ) := by
  have hpR : (0:ℝ) < p := by exact_mod_cast hp
  have hbound (z : AddCircle (1:ℝ)) :
      0 ≤ ⌊(p:ℝ)*circleRepresentative z⌋ ∧ ⌊(p:ℝ)*circleRepresentative z⌋ < (p:ℤ) := by
    refine ⟨Int.floor_nonneg.mpr (mul_nonneg hpR.le (circleRepresentative_range z).1),?_⟩
    apply Int.floor_lt.mpr
    push_cast
    nlinarith [(circleRepresentative_range z).2]
  have hf : ⌊(p:ℝ)*circleRepresentative x⌋ = ⌊(p:ℝ)*circleRepresentative y⌋ := by
    have hh := (ZMod.intCast_eq_intCast_iff' _ _ p).mp h
    rwa [Int.emod_eq_of_lt (hbound x).1 (hbound x).2,Int.emod_eq_of_lt (hbound y).1 (hbound y).2] at hh
  have hdist := Int.abs_sub_lt_one_of_floor_eq_floor hf
  have hreal : |circleRepresentative x-circleRepresentative y| ≤ 1/(p:ℝ) := by
    rw [← mul_sub,abs_mul,abs_of_pos hpR] at hdist
    apply (le_div_iff₀ hpR).mpr
    nlinarith
  have hx : (circleRepresentative x : AddCircle (1:ℝ)) = x := AddCircle.coe_equivIco
  have hy : (circleRepresentative y : AddCircle (1:ℝ)) = y := AddCircle.coe_equivIco
  have hn : ‖((circleRepresentative x-circleRepresentative y:ℝ) : AddCircle (1:ℝ))‖ ≤
      |circleRepresentative x-circleRepresentative y| := QuotientAddGroup.norm_mk_le_norm
  rw [QuotientAddGroup.mk_sub,hx,hy] at hn
  exact hn.trans hreal

/-- A genuinely proved collision probability bound for the circle quantizer.
The exceptional set is bounded by a pullback of a circle ball under a nonzero
integer multiplication, whose Haar measure is exactly known. -/
theorem circleBin_collision_measure (p : ℕ) (hp : 0 < p) (a b : ℤ) (hab : a ≠ b) :
    volume {θ : AddCircle (1:ℝ) | circleBin p (a • θ) = circleBin p (b • θ)} ≤
      ENNReal.ofReal (2/(p:ℝ)) := by
  have hsub : {θ : AddCircle (1:ℝ) | circleBin p (a • θ) = circleBin p (b • θ)} ⊆
      (fun θ : AddCircle (1:ℝ) => (a-b) • θ) ⁻¹' Metric.closedBall 0 (1/(p:ℝ)) := by
    intro θ hθ
    have h := circleBin_collision_norm p hp (a • θ) (b • θ) hθ
    simpa only [Set.mem_preimage,Metric.mem_closedBall,dist_zero_right,sub_smul] using h
  have hm := measurePreserving_zsmul (volume : Measure (AddCircle (1:ℝ))) (sub_ne_zero.mpr hab)
  calc
    _ ≤ volume ((fun θ : AddCircle (1:ℝ) => (a-b) • θ) ⁻¹' Metric.closedBall 0 (1/(p:ℝ))) := measure_mono hsub
    _ = volume (Metric.closedBall (0:AddCircle (1:ℝ)) (1/(p:ℝ))) :=
      hm.measure_preimage measurableSet_closedBall.nullMeasurableSet
    _ = ENNReal.ofReal (min 1 (2*(1/(p:ℝ)))) := AddCircle.volume_closedBall _ _
    _ ≤ ENNReal.ofReal (2/(p:ℝ)) := by
      apply ENNReal.ofReal_le_ofReal
      simpa only [mul_one_div] using min_le_right (1:ℝ) (2*(1/(p:ℝ)))

/-- The circle quantizer is exactly the modular floor map used in the
projection estimates, with the correct p-scaled real parameter. -/
theorem circleBin_zsmul_eq_modularRound (p : ℕ) (θ : AddCircle (1:ℝ)) (x : ℤ) :
    circleBin p (x • θ) = modularRound p ((p:ℝ)*circleRepresentative θ) x := by
  let u : ℝ := (x:ℝ)*circleRepresentative θ
  let v : ℝ := circleRepresentative (x • θ)
  have hu : (u : AddCircle (1:ℝ)) = x • θ := by
    dsimp only [u]
    rw [← zsmul_eq_mul,AddCircle.coe_zsmul]
    exact congrArg (fun z : AddCircle (1:ℝ) => x • z) AddCircle.coe_equivIco
  have hv : (v : AddCircle (1:ℝ)) = x • θ := AddCircle.coe_equivIco
  have hz : ((u-v:ℝ) : AddCircle (1:ℝ)) = 0 := by
    rw [QuotientAddGroup.mk_sub,hu,hv,sub_self]
  obtain ⟨z,hz⟩ := (AddCircle.coe_eq_zero_iff (1:ℝ)).mp hz
  have hzR : (z:ℝ) = u-v := by simpa only [zsmul_eq_mul,mul_one] using hz
  have he : ((p:ℝ)*circleRepresentative θ)*(x:ℝ) =
      (p:ℝ)*v+((p:ℤ)*z:ℤ) := by
    push_cast
    dsimp only [u] at hzR
    nlinarith
  unfold modularRound
  rw [he,Int.floor_add_intCast]
  simp only [Int.cast_add,Int.cast_mul,Int.cast_natCast,ZMod.natCast_self,zero_mul,add_zero]
  rfl

theorem measurable_circleRepresentative : Measurable circleRepresentative :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIco (1:ℝ) 0).measurable

theorem measurableSet_circleBin_collision (p : ℕ) (a b : ℤ) :
    MeasurableSet {θ : AddCircle (1:ℝ) | circleBin p (a • θ) = circleBin p (b • θ)} := by
  have hm (x : ℤ) : Measurable (fun θ : AddCircle (1:ℝ) =>
      ⌊(p:ℝ)*circleRepresentative (x • θ)⌋ % (p:ℤ)) := by
    exact (measurable_of_countable (f := fun n : ℤ => n % (p:ℤ))).comp
      (Int.measurable_floor.comp (measurable_const.mul
        (measurable_circleRepresentative.comp (continuous_const_smul x).measurable)))
  have h := measurableSet_eq_fun (hm a) (hm b)
  simpa only [circleBin,ZMod.intCast_eq_intCast_iff'] using h

end KakeyaTwoScale
#print axioms KakeyaTwoScale.circleRepresentative_range
#print axioms KakeyaTwoScale.circleBin_collision_norm
#print axioms KakeyaTwoScale.circleBin_collision_measure

#print axioms KakeyaTwoScale.circleBin_zsmul_eq_modularRound
#print axioms KakeyaTwoScale.measurable_circleRepresentative
#print axioms KakeyaTwoScale.measurableSet_circleBin_collision
