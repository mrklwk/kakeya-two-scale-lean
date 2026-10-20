module
public import KakeyaTwoScale.EuclideanTubes
public import Mathlib.Analysis.Normed.Module.Normalize

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical NormedSpace
open scoped BigOperators

/-- Quantitative normalization away from zero. -/
theorem normalize_dist_le {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (x y : X) (hx : 1 ≤ ‖x‖) (hy : 0 < ‖y‖) :
    dist (normalize x) (normalize y) ≤ 2*dist x y := by
  have hx0 : 0 < ‖x‖ := by linarith
  have hid : normalize x-normalize y =
      ‖x‖⁻¹ • (x-y)+(‖x‖⁻¹-‖y‖⁻¹) • y := by
    unfold NormedSpace.normalize; module
  rw [dist_eq_norm,hid]
  have hh := norm_add_le (‖x‖⁻¹ • (x-y)) ((‖x‖⁻¹-‖y‖⁻¹) • y)
  rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hx0)] at hh
  have he : |‖x‖⁻¹-‖y‖⁻¹| *‖y‖=‖x‖⁻¹*|‖y‖-‖x‖| := by
    rw [show ‖x‖⁻¹-‖y‖⁻¹=(‖y‖-‖x‖)/(‖x‖*‖y‖) by field_simp]
    rw [abs_div,abs_mul,abs_of_pos hx0,abs_of_pos hy]
    field_simp
  rw [he] at hh
  have hdiff := abs_norm_sub_norm_le y x
  rw [norm_sub_rev] at hdiff
  have hmul := mul_le_mul_of_nonneg_left hdiff (inv_nonneg.mpr hx0.le)
  have hinv : ‖x‖⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hx
  have hnorm := mul_le_mul_of_nonneg_right hinv (norm_nonneg (x-y))
  rw [dist_eq_norm]
  nlinarith

/-- A unit vector has a quantitatively nonzero coordinate. The deliberately
weaker rational bound avoids dimension-dependent square-root bookkeeping. -/
theorem unit_large_coordinate {n : ℕ} (u : EuclideanSpace ℝ (Fin (n+1))) (hu : ‖u‖=1) :
    ∃ i : Fin (n+1), 1/(n+2:ℝ) ≤ |u i| := by
  by_contra hh
  push Not at hh
  have hsq := EuclideanSpace.norm_sq_eq u
  rw [hu] at hsq
  have hs : ∑ i : Fin (n+1), (u i)^2 ≤ ∑ _i : Fin (n+1), (1/(n+2:ℝ))^2 := by
    apply Finset.sum_le_sum
    intro i _
    have h := hh i
    nlinarith [abs_nonneg (u i),sq_abs (u i)]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
  have he : ∑ i : Fin (n+1), (u i)^2=1 := by simpa [Real.norm_eq_abs,sq_abs] using hsq.symm
  rw [he] at hs
  have hp : (0:ℝ)<n+2 := by positivity
  have hpos := mul_le_mul_of_nonneg_right hs (sq_nonneg (n+2:ℝ))
  field_simp at hpos
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  push_cast at hpos
  nlinarith

def orientedDirection {n : ℕ} (reverse : Bool) (u : EuclideanSpace ℝ (Fin n)) :=
  if reverse then -u else u

def orientedBase {n : ℕ} (reverse : Bool) (b u : EuclideanSpace ℝ (Fin n)) :=
  if reverse then b+u else b

theorem orientedDirection_norm {n : ℕ} (reverse : Bool) (u : EuclideanSpace ℝ (Fin n)) :
    ‖orientedDirection reverse u‖=‖u‖ := by cases reverse <;> simp [orientedDirection]

theorem oriented_tube_eq {n : ℕ} (reverse : Bool) (b u : EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    euclideanTube (orientedBase reverse b u) (orientedDirection reverse u) r=euclideanTube b u r := by
  cases reverse <;> simp [orientedBase,orientedDirection,euclideanTube_reverse]

theorem oriented_angle_separation {n : ℕ} (reverse : Bool)
    (u v : EuclideanSpace ℝ (Fin n)) (r : ℝ)
    (h : r ≤ InnerProductGeometry.angle u v) :
    r ≤ InnerProductGeometry.angle (orientedDirection reverse u) (orientedDirection reverse v) := by
  cases reverse <;> simpa [orientedDirection] using h

end KakeyaTwoScale
#print axioms KakeyaTwoScale.normalize_dist_le
#print axioms KakeyaTwoScale.unit_large_coordinate
#print axioms KakeyaTwoScale.orientedDirection_norm
#print axioms KakeyaTwoScale.oriented_tube_eq
#print axioms KakeyaTwoScale.oriented_angle_separation
