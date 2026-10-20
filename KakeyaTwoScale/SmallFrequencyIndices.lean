module
public import KakeyaTwoScale.ExceptionalPrimeIndices
public import KakeyaTwoScale.CharacterSeparation

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical

def smallFrequencyIndices (p U : ℕ) [NeZero p] (J : Finset ℕ) (k : ZMod p) : Finset ℕ :=
  J.filter (fun j => frequencySize ((j:ZMod p)⁻¹*k) ≤ (U:ℝ))

theorem natCast_nonzero_of_prime_below (p j : ℕ) [NeZero p] (hj : j.Prime) (hjp : j < p) :
    (j:ZMod p) ≠ 0 := by
  intro h
  have he := congrArg ZMod.val h
  have : j = 0 := by simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt hjp,ZMod.val_zero] using he
  exact hj.ne_zero this

/-- Actual small Fourier frequencies are exceptional indices in the proved
integer wrap/divisor bound. -/
theorem smallFrequencyIndices_subset (p U : ℕ) [Fact p.Prime] (J : Finset ℕ) (k : ZMod p)
    (hJ : ∀ j ∈ J, (j:ZMod p) ≠ 0) :
    smallFrequencyIndices p U J k ⊆ exceptionalPrimeIndices p k.valMinAbs U J := by
  intro j hj
  obtain ⟨hj,hfreq⟩ := Finset.mem_filter.mp hj
  refine Finset.mem_filter.mpr ⟨hj,((j:ZMod p)⁻¹*k).valMinAbs,?_,?_⟩
  · unfold frequencySize at hfreq
    exact_mod_cast hfreq
  · simp only [Int.cast_mul,Int.cast_natCast,ZMod.coe_valMinAbs]
    field_simp [hJ j hj]

theorem smallFrequencyIndices_card_le (p m U K L B : ℕ) [Fact p.Prime]
    (hmp : m < p) (J : Finset ℕ) (hprime : ∀ j ∈ J, j.Prime)
    (hsize : ∀ j ∈ J, L ≤ j ∧ j ≤ m) (hL : 1 ≤ L)
    (hscale : U*m ≤ K*p) (hcut : (K+2)*p < L^(B+1))
    (k : ZMod p) (hk : k ≠ 0) : (smallFrequencyIndices p U J k).card ≤ (2*K+3)*B := by
  have hJ : ∀ j ∈ J, (j:ZMod p) ≠ 0 := fun j hj =>
    natCast_nonzero_of_prime_below p j (hprime j hj) ((hsize j hj).2.trans_lt hmp)
  have hξ : |k.valMinAbs| ≤ (p:ℤ) := by
    obtain ⟨hlo,hhi⟩ := k.valMinAbs_mem_Ioc
    apply abs_le.mpr
    constructor <;> omega
  have hξ0 : (k.valMinAbs:ZMod p) ≠ 0 := by simpa only [ZMod.coe_valMinAbs] using hk
  exact (Finset.card_le_card (smallFrequencyIndices_subset p U J k hJ)).trans
    (exceptionalPrimeIndices_card_le p m U K L B (NeZero.pos p) k.valMinAbs hξ hξ0
      J hprime hsize hL hscale hcut)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.natCast_nonzero_of_prime_below
#print axioms KakeyaTwoScale.smallFrequencyIndices_subset
#print axioms KakeyaTwoScale.smallFrequencyIndices_card_le
