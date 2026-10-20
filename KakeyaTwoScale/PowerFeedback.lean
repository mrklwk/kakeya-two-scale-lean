module
public import KakeyaTwoScale.VerticalSDFibers

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical
open scoped BigOperators

/-- Isolate the quantitative lower bound on a nonempty fiber after applying
SD. Both the exponent and the multiplicative constant are retained. -/
theorem power_feedback_lower (u C K β : ℝ) (hu : 0 < u) (hC : 0 < C)
    (hK : 0 < K) (hβ : 1 < β) (h : u ≤ C*(K*u)^β) :
    (C*K^β)^(-1/(β-1)) ≤ u := by
  have hb : 0 < β-1 := by linarith
  have hCK : 0 < C*K^β := mul_pos hC (Real.rpow_pos_of_pos hK β)
  apply (Real.log_le_log_iff (Real.rpow_pos_of_pos hCK _) hu).mp
  have hl := Real.log_le_log hu h
  rw [Real.log_mul (ne_of_gt hC) (ne_of_gt (Real.rpow_pos_of_pos (mul_pos hK hu) β)),
    Real.log_rpow (mul_pos hK hu),Real.log_mul (ne_of_gt hK) (ne_of_gt hu)] at hl
  rw [Real.log_rpow hCK,Real.log_mul (ne_of_gt hC) (ne_of_gt (Real.rpow_pos_of_pos hK β)),
    Real.log_rpow hK]
  have hh : -(Real.log C+β*Real.log K)/(β-1) ≤ Real.log u := by
    apply (div_le_iff₀ hb).mpr
    nlinarith
  convert hh using 1
  ring

/-- Sum disjoint actual fibers after obtaining their positive lower bound. -/
theorem image_bound_of_fiber_lower {A B : Type*} [DecidableEq B]
    (Q : Finset A) (g : A → B) (L : ℝ)
    (hL : ∀ z ∈ Q.image g, L ≤ ((Q.filter (fun x => g x = z)).card : ℝ)) :
    L*(Q.image g).card ≤ Q.card := by
  have hsum : (∑ z ∈ Q.image g, (Q.filter (fun x => g x = z)).card) = Q.card := by
    simpa using Finset.sum_fiberwise_of_maps_to
      (fun x hx => Finset.mem_image.mpr ⟨x,hx,rfl⟩ : ∀ x ∈ Q, g x ∈ Q.image g) (fun _ => (1:ℕ))
  calc
    _ = ∑ _z ∈ Q.image g, L := by simp [mul_comm]
    _ ≤ ∑ z ∈ Q.image g, ((Q.filter (fun x => g x = z)).card : ℝ) := Finset.sum_le_sum hL
    _ = _ := by exact_mod_cast hsum

/-- Derive the nu-image bound from the preceding SD estimate on each actual
fiber. No fiber-size lower bound or image estimate is assumed. -/
theorem FiniteSDBound.nu_image_bound {R : Finset ℚ} {β C : ℝ}
    (hSD : FiniteSDBound R β C) (hβ : 1 < β) (hC : 0 < C)
    (G : Finset ArithmeticPoint) (Q : Finset (ArithmeticPoint × ArithmeticPoint))
    (a p : ℚ) (dual : ℚ → ℚ) (K : ℝ) (hK : 0 < K)
    (hQ : Q ⊆ G.product G)
    (hdiff : Set.InjOn (arithmeticProjection (-1)) (↑G : Set ArithmeticPoint))
    (hproj : ∀ z ∈ Q.image (verticalNu a p), ∀ r ∈ R,
      (((Q.filter (fun v => verticalNu a p v = z)).image
        (fun v => (arithmeticProjection r v.1, arithmeticProjection (dual r) v.2))).card : ℝ) ≤
        K*(Q.filter (fun v => verticalNu a p v = z)).card) :
    (C*K^β)^(-1/(β-1))*(Q.image (verticalNu a p)).card ≤ Q.card := by
  apply image_bound_of_fiber_lower
  intro z hz
  let U := Q.filter (fun v => verticalNu a p v = z)
  have hU : U ⊆ G.product G := (Finset.filter_subset _ _).trans hQ
  have hnu : ∀ v ∈ U, verticalNu a p v = z := fun v hv => (Finset.mem_filter.mp hv).2
  have hu : 0 < (U.card : ℝ) := by
    obtain ⟨v,hv,hz⟩ := Finset.mem_image.mp hz
    have hn : U.Nonempty := ⟨v,Finset.mem_filter.mpr ⟨hv,hz⟩⟩
    exact_mod_cast Finset.card_pos.mpr hn
  apply power_feedback_lower _ C K β hu hC hK hβ
  exact hSD.vertical_fiber G U a p z dual K hK.le hU hdiff hnu (hproj z hz)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.power_feedback_lower
#print axioms KakeyaTwoScale.image_bound_of_fiber_lower
#print axioms KakeyaTwoScale.FiniteSDBound.nu_image_bound
