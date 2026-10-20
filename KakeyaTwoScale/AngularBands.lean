module
public import KakeyaTwoScale.BrushSummation
public import KakeyaTwoScale.DyadicCover

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical
open scoped BigOperators

theorem dyadicRadius_pow_cancel (q : ℕ) : (2:ℝ)^q*dyadicRadius q = 1 := by
  have hp : (2:ℝ)^q = Real.exp ((q:ℝ)*Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ)<2)]
  rw [hp, dyadicRadius, ← Real.exp_add]
  have he : (q:ℝ)*Real.log 2 + -Real.log 2*q = 0 := by ring
  rw [he, Real.exp_zero]

def dyadicAngleBand (q : ℕ) (angle : ℝ) : ℕ :=
  if h : ∃ j : ℕ, angle ≤ (2:ℝ)^j*dyadicRadius q then Nat.find h else 0

/-- Concrete dyadic band assignment. Angles in radians lie below 2; the first
two bins together contain angles at most 2 rho. Higher bins have ratio two. -/
theorem dyadicAngleBand_spec (q : ℕ) (angle : ℝ) (ha : angle ≤ 2) :
    dyadicAngleBand q angle < q+2 ∧
    angle ≤ (2:ℝ)^(dyadicAngleBand q angle)*dyadicRadius q ∧
    (0 < dyadicAngleBand q angle →
      (2:ℝ)^(dyadicAngleBand q angle-1)*dyadicRadius q < angle) := by
  have htop : (2:ℝ)^(q+1)*dyadicRadius q = 2 := by
    rw [pow_succ]
    nlinarith [dyadicRadius_pow_cancel q]
  have hex : ∃ j : ℕ, angle ≤ (2:ℝ)^j*dyadicRadius q := ⟨q+1,by rwa [htop]⟩
  simp only [dyadicAngleBand, dite_eq_left hex]
  refine ⟨by have hh := Nat.find_min' hex (show angle ≤ (2:ℝ)^(q+1)*dyadicRadius q by rwa [htop]); omega,
    Nat.find_spec hex, ?_⟩
  intro hpos
  exact lt_of_not_ge (Nat.find_min hex (by omega : Nat.find hex-1 < Nat.find hex))

/-- Exact O(q) weighted band selection at rho=2^(-q), including boundary cases.
No angular band-count hypothesis is left to the geometric brush caller. -/
theorem weighted_angular_band {J : Type*} (family : Finset J) (angle w : J → ℝ)
    (q : ℕ) (hq : 1 ≤ q) (ha : ∀ j ∈ family, angle j ≤ 2)
    (hw : ∀ j ∈ family, 0 ≤ w j) :
    ∃ b < q+2, (∑ j ∈ family, w j) ≤ (3*(q:ℝ)) *
      ∑ j ∈ family.filter (fun j => dyadicAngleBand q (angle j) = b), w j := by
  obtain ⟨b,hb,hweight⟩ := weighted_band_pigeonhole family (Finset.range (q+2))
    (by simp) (fun j => dyadicAngleBand q (angle j)) w
    (fun j hj => Finset.mem_range.mpr (dyadicAngleBand_spec q (angle j) (ha j hj)).1)
  refine ⟨b,Finset.mem_range.mp hb,?_⟩
  have hcount : ((Finset.range (q+2)).card : ℝ) ≤ 3*(q:ℝ) := by
    simp only [Finset.card_range, Nat.cast_add, Nat.cast_ofNat]
    have hq' : (1:ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have hn : 0 ≤ ∑ j ∈ family.filter (fun j => dyadicAngleBand q (angle j) = b), w j :=
    Finset.sum_nonneg fun j hj => hw j (Finset.mem_filter.mp hj).1
  exact hweight.trans (mul_le_mul_of_nonneg_right hcount hn)
end KakeyaTwoScale
#print axioms KakeyaTwoScale.dyadicAngleBand_spec
#print axioms KakeyaTwoScale.weighted_angular_band
