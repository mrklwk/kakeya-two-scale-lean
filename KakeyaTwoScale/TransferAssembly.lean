module
public import KakeyaTwoScale.VolumeCertificate

@[expose] public section

noncomputable section
namespace KakeyaTwoScale

/-- Eliminate the common parent weight from the three actual-scale estimates.
A is the arithmetic lower factor, R the represented-parent factor, and G the
brush factor (including its scale power). No estimate is asserted here: each
is an explicit premise, with all constants and positivity retained. -/
theorem transfer_of_weight_and_brush
    (fine coarse u U S M eta loss A R G : ℝ)
    (hf : 0 ≤ fine) (hc : 0 < coarse) (hu : 0 < u) (hU : 0 ≤ U)
    (heta : 0 ≤ eta) (hA : 0 ≤ A) (hR : 0 ≤ R) (hG : 0 ≤ G)
    (weight : A ≤ coarse*u^theta)
    (represented : R*u^a*U ≤ S*fine)
    (brush : G*S*M ≤ coarse*loss)
    (threshold : M*coarse = eta*U) :
    G*R*eta*A^(a/theta)*U^2 ≤ fine*coarse^(2+a/theta)*loss := by
  have hratio : 0 ≤ a/theta := by norm_num [a,theta]
  have hcancel : theta*(a/theta) = a := by norm_num [a,theta]
  have hw := Real.rpow_le_rpow hA weight hratio
  rw [Real.mul_rpow hc.le (Real.rpow_nonneg hu.le _), ← Real.rpow_mul hu.le, hcancel] at hw
  have hbase : G*R*eta*u^a*U^2 ≤ fine*coarse^2*loss := by
    calc
      _ = (G*eta*U)*(R*u^a*U) := by ring
      _ ≤ (G*eta*U)*(S*fine) :=
        mul_le_mul_of_nonneg_left represented (by positivity)
      _ = (G*S*M)*(fine*coarse) := by
        calc
          _ = (G*S*fine)*(eta*U) := by ring
          _ = (G*S*fine)*(M*coarse) := by rw [threshold]
          _ = _ := by ring
      _ ≤ (coarse*loss)*(fine*coarse) :=
        mul_le_mul_of_nonneg_right brush (mul_nonneg hf hc.le)
      _ = _ := by ring
  calc
    _ = (G*R*eta*U^2)*A^(a/theta) := by ring
    _ ≤ (G*R*eta*U^2)*(coarse^(a/theta)*u^a) :=
      mul_le_mul_of_nonneg_left hw (by positivity)
    _ = (G*R*eta*u^a*U^2)*coarse^(a/theta) := by ring
    _ ≤ (fine*coarse^2*loss)*coarse^(a/theta) :=
      mul_le_mul_of_nonneg_right hbase (Real.rpow_nonneg hc.le _)
    _ = fine*(coarse^2*coarse^(a/theta))*loss := by ring
    _ = _ := by
      rw [show coarse^2 = coarse^(2:ℝ) by simp, ← Real.rpow_add hc]
end KakeyaTwoScale
#print axioms KakeyaTwoScale.transfer_of_weight_and_brush
