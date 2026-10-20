module
public import KakeyaTwoScale.WeightedFlatMultilinear
public import KakeyaTwoScale.FlatCylinderMassLower

@[expose] public section

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- In the zero-drop case k=ambient dimension, CV already supplies the exact
linear population bound, for arbitrary locations and finite cylinder lengths. -/
theorem top_dimensional_cylinder_norm (n : ℕ) (hn : 0<n) :
    ∃ C : ℝ, 0<C ∧ ∀ r : ℝ, 0<r → ∀ (N : ℕ)
      (b u : Fin N → EuclideanSpace ℝ (Fin (n+1))) (ell : Fin N → ℝ),
      (∀ j, ‖u j‖=1) →
      eLpNorm (multilinearKakeyaFunction (n+1) u
        (fun j => flatCylinder (b j) (u j) (ell j) r) (n+1))
        (ENNReal.ofReal ((n+1:ℝ)/n)) volume ≤
      ENNReal.ofReal (C*r^n*N) := by
  obtain ⟨C,hC,hbound⟩ := flatCylinder_multilinear_norm_power n (n+1) (by omega) le_rfl
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  let p : ℝ := (n+1:ℝ)/n
  have hp : 0<p := by dsimp [p]; positivity
  refine ⟨C^(1/p),by positivity,?_⟩
  intro r hr N b u ell hu
  have hh := hbound r hr N b u ell hu
  simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one,add_sub_cancel_right] at hh
  change eLpNorm _ (ENNReal.ofReal p) volume ^ p ≤ _ at hh
  have he : (C^(1/p)*r^n*(N:ℝ))^p =
      C*r^(n+1)*((N:ℝ)^(n+1))^(1/(n:ℝ)) := by
    rw [Real.mul_rpow (by positivity) (Nat.cast_nonneg N),
      Real.mul_rpow (by positivity) (by positivity),←Real.rpow_mul hC.le]
    rw [one_div_mul_cancel hp.ne',Real.rpow_one]
    have hrp : (r^n)^p=r^(n+1) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul hr.le]
      have he : (n:ℝ)*p=n+1 := by dsimp [p]; field_simp
      rw [he]
      exact_mod_cast (Real.rpow_natCast r (n+1))
    have hNp : ((N:ℝ)^(n+1))^(1/(n:ℝ))=(N:ℝ)^p := by
      rw [←Real.rpow_natCast,←Real.rpow_mul (Nat.cast_nonneg N)]
      congr 1
      simp [p,div_eq_mul_inv]
    rw [hrp,hNp]
  rw [←he,←ENNReal.ofReal_rpow_of_nonneg (by positivity) hp.le] at hh
  exact (ENNReal.rpow_le_rpow_iff hp).mp hh

/-- The published contract is dependency-closed when k equals ambient
 dimension. Direction separation is unnecessary in this zero-drop case. -/
theorem published_zahl_top_dimension (n : ℕ) (hn : 0<n) :
    PublishedZahlCylinderEstimate (n+1) (n+1) := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hB : zahlB (n+1) (n+1)=(n+1:ℝ) := by
    unfold zahlB
    field_simp
    ring
  obtain ⟨C,hC,hbound⟩ := top_dimensional_cylinder_norm n hn
  obtain ⟨c,hc,hvol⟩ := flatCylinder_volume_lower_unrestricted n
  refine ⟨by omega,le_rfl,?_⟩
  intro ε hε
  refine ⟨C/c,by positivity,?_⟩
  intro r hr hrhalf N b u hu _
  have hm : c*r^n*(N:ℝ)≤∑j,volume.real (flatCylinder (b j) (u j) 1 r) := by
    have hh := Finset.sum_le_sum (fun j (_ : j∈(Finset.univ : Finset (Fin N))) =>
      hvol r hr hrhalf.le (b j) (u j) (hu j))
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
      mul_comm (N:ℝ)] using hh
  simp only [hB,Nat.cast_add,Nat.cast_one,add_sub_cancel_right]
  rw [div_self (by positivity : (n+1:ℝ)≠0),sub_self,zero_sub]
  have hpower : (n+1:ℝ)*n/(n*(n+1))=1 := by field_simp
  rw [hpower,Real.rpow_one]
  apply (hbound r hr N b u (fun _ => 1) hu).trans
  apply ENNReal.ofReal_le_ofReal
  have hrpow : 1≤r^(-ε) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr (by linarith) (by linarith)
  have hmass : C*r^n*(N:ℝ)≤(C/c)*(∑j,volume.real (flatCylinder (b j) (u j) 1 r)) := by
    have hh := mul_le_mul_of_nonneg_left hm (div_nonneg hC.le hc.le)
    convert hh using 1; field_simp
  apply hmass.trans
  have hh := mul_le_mul_of_nonneg_left hrpow (div_nonneg hC.le hc.le)
  rw [mul_one] at hh
  exact mul_le_mul_of_nonneg_right hh (Finset.sum_nonneg (fun _ _ => measureReal_nonneg))

end KakeyaTwoScale
#print axioms KakeyaTwoScale.top_dimensional_cylinder_norm
#print axioms KakeyaTwoScale.published_zahl_top_dimension
