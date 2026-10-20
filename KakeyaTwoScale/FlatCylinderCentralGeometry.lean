module
public import KakeyaTwoScale.CapsuleCylinder
public import KakeyaTwoScale.CentralDilationExtension

@[expose] public section

open Set Metric
noncomputable section
namespace KakeyaTwoScale

theorem flatCylinder_convex {d : ℕ} (b u : EuclideanSpace ℝ (Fin d)) (L r : ℝ) :
    Convex ℝ (flatCylinder b u L r) := by
  intro x hx y hy a c ha hc hac
  obtain ⟨tx,htx0,htxL,hix,hrx⟩ := hx
  obtain ⟨ty,hty0,htyL,hiy,hry⟩ := hy
  have he : a • x+c • y-(b+(a*tx+c*ty) • u)=
      a • (x-(b+tx • u))+c • (y-(b+ty • u)) := by
    have hc' : c=1-a := by linarith
    rw [hc']
    module
  have ht : a*tx+c*ty∈Ioo (0:ℝ) L := by
    simpa only [smul_eq_mul] using (convex_Ioo (𝕜 := ℝ) 0 L)
      ⟨htx0,htxL⟩ ⟨hty0,htyL⟩ ha hc hac
  refine ⟨a*tx+c*ty,ht.1,ht.2,?_,?_⟩
  · rw [he,inner_add_right,inner_smul_right,inner_smul_right,hix,hiy]
    ring
  · have hm := (convex_ball (0 : EuclideanSpace ℝ (Fin d)) r)
        (show x-(b+tx • u)∈ball 0 r by simpa using hrx)
        (show y-(b+ty • u)∈ball 0 r by simpa using hry) ha hc hac
    simpa only [he,mem_ball,dist_zero_right] using hm

theorem flatCylinder_central_symmetry {d : ℕ}
    (b u : EuclideanSpace ℝ (Fin d)) (L r : ℝ) :
    ∀ x∈flatCylinder b u L r, (2:ℝ) • (b+(L/2) • u)-x∈flatCylinder b u L r := by
  rintro x ⟨t,ht0,htL,hi,hr⟩
  have he : (2:ℝ) • (b+(L/2) • u)-x-(b+(L-t) • u)=-(x-(b+t • u)) := by module
  refine ⟨L-t,by linarith,by linarith,?_,?_⟩
  · rw [he,inner_neg_right,hi,neg_zero]
  · simpa only [he,norm_neg] using hr

/-- Exact central dilation scales both the length and the transverse radius.
No unit-axis assumption or endpoint closure is hidden in this identity. -/
theorem flatCylinder_central_dilation {d : ℕ}
    (b u : EuclideanSpace ℝ (Fin d)) (L r a : ℝ) (ha : 0<a) :
    centralDilation a (b+(L/2) • u) (flatCylinder b u L r)=
      flatCylinder (b+((1-a)*L/2) • u) u (a*L) (a*r) := by
  ext x
  constructor
  · rintro ⟨y,⟨t,ht0,htL,hi,hr⟩,rfl⟩
    have he : b+(L/2) • u+a • (y-(b+(L/2) • u))-
        (b+((1-a)*L/2) • u+(a*t) • u)=a • (y-(b+t • u)) := by module
    refine ⟨a*t,mul_pos ha ht0,mul_lt_mul_of_pos_left htL ha,?_,?_⟩
    · rw [he,inner_smul_right,hi,mul_zero]
    · rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos ha]
      exact mul_lt_mul_of_pos_left hr ha
  · rintro ⟨t,ht0,htL,hi,hr⟩
    let y := b+(t/a) • u+a⁻¹ • (x-(b+((1-a)*L/2) • u+t • u))
    have he : y-(b+(t/a) • u)=a⁻¹ • (x-(b+((1-a)*L/2) • u+t • u)) := by dsimp [y]; module
    refine ⟨y,⟨t/a,div_pos ht0 ha,(div_lt_iff₀ ha).mpr (by nlinarith),?_,?_⟩,?_⟩
    · rw [he,inner_smul_right,hi,mul_zero]
    · rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ha)]
      calc a⁻¹*‖x-(b+((1-a)*L/2) • u+t • u)‖ < a⁻¹*(a*r) :=
            mul_lt_mul_of_pos_left hr (inv_pos.mpr ha)
           _ = r := by field_simp
    · dsimp [y]
      match_scalars <;> field_simp [ne_of_gt ha] <;> ring

end KakeyaTwoScale
#print axioms KakeyaTwoScale.flatCylinder_convex
#print axioms KakeyaTwoScale.flatCylinder_central_symmetry
#print axioms KakeyaTwoScale.flatCylinder_central_dilation
