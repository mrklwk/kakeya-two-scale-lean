module
public import KakeyaTwoScale.ScaledProgressionHits

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical
open scoped Pointwise

def coefficientWidth (a b : ℤ) : ℕ := a.natAbs+b.natAbs

def coefficientInterval (p m : ℕ) (a b : ℤ) : Finset (ZMod p) :=
  (Finset.Icc (-(coefficientWidth a b:ℤ)*(m:ℤ)) ((coefficientWidth a b:ℤ)*(m:ℤ))).image
    (fun z : ℤ => (z:ZMod p))

theorem coefficientInterval_card (p m : ℕ) (hm : 0 < m) (a b : ℤ) :
    (coefficientInterval p m a b).card ≤ (2*coefficientWidth a b+1)*m := by
  apply Finset.card_image_le.trans
  have he : (Finset.Icc (-(coefficientWidth a b:ℤ)*(m:ℤ))
      ((coefficientWidth a b:ℤ)*(m:ℤ))).card = 2*coefficientWidth a b*m+1 := by
    rw [Int.card_Icc]
    have h : (coefficientWidth a b:ℤ)*m+1-(-(coefficientWidth a b:ℤ)*m) =
        ((2*coefficientWidth a b*m+1:ℕ):ℤ) := by push_cast; ring
    rw [h,Int.toNat_natCast]
  rw [he]
  nlinarith

theorem linear_form_in_coefficientInterval (p m : ℕ) (a b : ℤ)
    (i j : ℕ) (hi : i ≤ m) (hj : j ≤ m) :
    (a:ZMod p)*(i:ZMod p)+(b:ZMod p)*(j:ZMod p) ∈ coefficientInterval p m a b := by
  have hiR : |(i:ℤ)| ≤ (m:ℤ) := by simpa only [abs_of_nonneg (Int.natCast_nonneg i)] using (show (i:ℤ) ≤ m by exact_mod_cast hi)
  have hjR : |(j:ℤ)| ≤ (m:ℤ) := by simpa only [abs_of_nonneg (Int.natCast_nonneg j)] using (show (j:ℤ) ≤ m by exact_mod_cast hj)
  have h1 := mul_le_mul_of_nonneg_left hiR (abs_nonneg a)
  have h2 := mul_le_mul_of_nonneg_left hjR (abs_nonneg b)
  have hsum := abs_add_le (a*(i:ℤ)) (b*(j:ℤ))
  rw [abs_mul,abs_mul] at hsum
  have hbound : |a*(i:ℤ)+b*(j:ℤ)| ≤ (coefficientWidth a b:ℤ)*(m:ℤ) := by
    simp only [coefficientWidth,Nat.cast_add,Int.natCast_natAbs]
    nlinarith
  refine Finset.mem_image.mpr ⟨a*(i:ℤ)+b*(j:ℤ),Finset.mem_Icc.mpr ?_,?_⟩
  · simpa only [neg_mul] using abs_le.mp hbound
  · push_cast
    rfl

end KakeyaTwoScale
#print axioms KakeyaTwoScale.coefficientInterval_card
#print axioms KakeyaTwoScale.linear_form_in_coefficientInterval
