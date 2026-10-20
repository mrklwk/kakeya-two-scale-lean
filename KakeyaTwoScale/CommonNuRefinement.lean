module
public import KakeyaTwoScale.CornerFinal
public import KakeyaTwoScale.SelectedDataset

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical
open scoped BigOperators

/-- A single refinement simultaneously controls every outer nu map. All
incoming sets refine the same S, and all fiber bounds concern the same Q. -/
theorem exists_common_nu_refinement
    (G : Finset ArithmeticPoint) (S : Finset (ArithmeticPoint × ArithmeticPoint))
    (J : Finset ℚ) (P : ℚ → Finset ℚ) (a : ℚ → ℚ) (p s : ℚ)
    (β C : ℝ) (hβ : 1 < β) (hC : 0 < C)
    (hSD : ∀ j ∈ J, FiniteSDBound (P j) β C)
    (hS : S ⊆ G.product G)
    (hv : ∀ v ∈ S, arithmeticProjection s v.1 = arithmeticProjection s v.2)
    (hdiff : Set.InjOn (arithmeticProjection (-1)) (↑G : Set ArithmeticPoint))
    (hproper : ∀ j ∈ J, ∀ r ∈ P j, r ≠ s ∧ dualDenominator (a j) p s r ≠ 0)
    (R : (Σ _ : ℚ, ℚ) → Finset (ArithmeticPoint × ArithmeticPoint))
    (d L E : ℕ) (hd : 0 < d) (hL : 0 < L) (hJ : J.Nonempty)
    (hR : ∀ i ∈ J.sigma P, R i ⊆ S)
    (hloss : ∀ i ∈ J.sigma P, S.card-(R i).card ≤ E)
    (himage : ∀ i ∈ J.sigma P,
      L*((R i).image (fun v => (arithmeticProjection i.2 v.1,
        arithmeticProjection (dualSlope (a i.1) p s i.2) v.2))).card ≤ 2*S.card)
    (hbudget : 4*d*(J.sigma P).card*E+4*(J.sigma P).card*S.card ≤ d*S.card)
    (hne : S.Nonempty) :
    ∃ Q ⊆ S,
      d*(S.card-Q.card) ≤ 2*d*(J.sigma P).card*E+2*(J.sigma P).card*S.card ∧
      S.card ≤ 2*Q.card ∧
      ∀ j ∈ J,
        (C*((8*d*J.card:ℝ)/L)^β)^(-1/(β-1)) *
          (Q.image (verticalNu (a j) p)).card ≤ Q.card := by
  let F := J.sigma P
  let f := fun (i : Σ _ : ℚ, ℚ) (v : ArithmeticPoint × ArithmeticPoint) =>
    (arithmeticProjection i.2 v.1,arithmeticProjection (dualSlope (a i.1) p s i.2) v.2)
  obtain ⟨Q,hQ,hl,hproj⟩ := exists_intersected_projection_refinement S F R f d J
    (fun j => verticalNu (a j) p) hR
  have hQS : Q ⊆ S := hQ.trans (Finset.filter_subset _ _)
  have hsum : (∑ i ∈ F, (S.card-(R i).card)) ≤ F.card*E := by
    calc
      _ ≤ ∑ _i ∈ F, E := Finset.sum_le_sum hloss
      _ = _ := by simp
  have hl' : d*(S.card-Q.card) ≤ 2*d*F.card*E+2*F.card*S.card := by
    have hm := Nat.mul_le_mul_left (2*d) hsum
    nlinarith
  have hc := Finset.card_le_card hQS
  have he := Nat.sub_add_cancel hc
  have hh : S.card ≤ 2*Q.card := by
    have hb : 4*d*F.card*E+4*F.card*S.card ≤ d*S.card := hbudget
    have hx : d*S.card ≤ d*(2*Q.card) := by nlinarith
    exact Nat.le_of_mul_le_mul_left hx hd
  have hq : 0 < (Q.card:ℝ) := by
    have hs := Finset.card_pos.mpr hne
    have : 0 < Q.card := by omega
    exact_mod_cast this
  have hK : 0 < (8*d*J.card:ℝ)/L := by
    have hj : 0 < (J.card:ℝ) := by exact_mod_cast Finset.card_pos.mpr hJ
    have hd' : 0 < (d:ℝ) := by exact_mod_cast hd
    have hL' : 0 < (L:ℝ) := by exact_mod_cast hL
    positivity
  refine ⟨Q,hQS,hl',hh,?_⟩
  intro j hj
  apply (hSD j hj).nu_image_bound hβ hC G Q (a j) p
    (dualSlope (a j) p s) _ hK (hQS.trans hS) hdiff
  intro z _ r hr
  have hi : Sigma.mk j r ∈ F := Finset.mem_sigma.mpr ⟨hj,hr⟩
  have hp := hproper j hj r hr
  have hdet : ∀ x ∈ S, ∀ y ∈ S, f ⟨j,r⟩ x = f ⟨j,r⟩ y →
      verticalNu (a j) p x = verticalNu (a j) p y := by
    intro x hx y hy he
    exact dual_projections_determine_nu (a j) p s r hp.1 hp.2 x y
      (hv x hx) (hv y hy) (congrArg Prod.fst he) (congrArg Prod.snd he)
  have hb := hproj j hj ⟨j,r⟩ hi hdet z
  simp only [classical_image_card] at hb
  have him := himage ⟨j,r⟩ hi
  let U := Q.filter (fun v => verticalNu (a j) p v = z)
  have hx : L*Q.card*(U.image (f ⟨j,r⟩)).card ≤ 4*d*J.card*S.card*U.card := by
    have hm := Nat.mul_le_mul_left L hb
    have hn := Nat.mul_le_mul_right (d*(2*J.card)*U.card) him
    change Q.card*(U.image (f ⟨j,r⟩)).card ≤ _ at hb
    nlinarith
  have hx' : (L:ℝ)*Q.card*(U.image (f ⟨j,r⟩)).card ≤
      8*d*J.card*Q.card*U.card := by
    have hxR : (L:ℝ)*Q.card*(U.image (f ⟨j,r⟩)).card ≤
        4*d*J.card*S.card*U.card := by exact_mod_cast hx
    have hhR : (S.card:ℝ) ≤ 2*Q.card := by exact_mod_cast hh
    have hm := mul_le_mul_of_nonneg_left hhR (show (0:ℝ) ≤ 4*d*J.card*U.card by positivity)
    nlinarith
  have hL' : 0 < (L:ℝ) := by exact_mod_cast hL
  have hh' : (U.image (f ⟨j,r⟩)).card ≤ (8*d*J.card:ℝ)/L*U.card := by
    apply (mul_le_mul_iff_left₀ hq).mp
    apply (mul_le_mul_iff_left₀ hL').mp
    calc
      _ ≤ (8:ℝ)*d*J.card*Q.card*U.card := by nlinarith only [hx']
      _ = _ := by field_simp
  exact hh'

end KakeyaTwoScale
#print axioms KakeyaTwoScale.exists_common_nu_refinement
