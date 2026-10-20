module
public import KakeyaTwoScale.LargePrimeDivisors

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical
open scoped BigOperators

def exceptionalPrimeIndices (p : ℕ) (ξ : ℤ) (U : ℕ) (J : Finset ℕ) : Finset ℕ :=
  J.filter (fun j => ∃ i : ℤ, |i| ≤ (U:ℤ) ∧ ((i*(j:ℤ):ℤ):ZMod p) = (ξ:ZMod p))

/-- An exact exceptional-frequency bound, including the integer wrap count.
No unspecified O(1) number of wraps or prime-factor bound is used. -/
theorem exceptionalPrimeIndices_card_le (p m U K L B : ℕ) (hp : 0 < p)
    (ξ : ℤ) (hξ : |ξ| ≤ (p:ℤ)) (hξ0 : (ξ:ZMod p) ≠ 0)
    (J : Finset ℕ) (hprime : ∀ j ∈ J, j.Prime) (hsize : ∀ j ∈ J, L ≤ j ∧ j ≤ m)
    (hL : 1 ≤ L) (hscale : U*m ≤ K*p) (hcut : (K+2)*p < L^(B+1)) :
    (exceptionalPrimeIndices p ξ U J).card ≤ (2*K+3)*B := by
  let W := Finset.Icc (-(K+1:ℤ)) (K+1:ℤ)
  let F := fun k : ℤ => J.filter (fun j => j ∣ (ξ-k*(p:ℤ)).natAbs)
  have hn (k : ℤ) : ξ-k*(p:ℤ) ≠ 0 := by
    intro h
    apply hξ0
    have he : ξ = k*(p:ℤ) := by omega
    rw [he]
    simp
  have hbound (k : ℤ) (hk : k ∈ W) : (ξ-k*(p:ℤ)).natAbs ≤ (K+2)*p := by
    have hkp : |k| ≤ (K+1:ℤ) := abs_le.mpr (Finset.mem_Icc.mp hk)
    have h1 := abs_sub ξ (k*(p:ℤ))
    rw [abs_mul,abs_of_nonneg (Int.natCast_nonneg p)] at h1
    have hh : |ξ-k*(p:ℤ)| ≤ ((K+2)*p:ℕ) := by
      push_cast
      nlinarith
    have hh' : ((ξ-k*(p:ℤ)).natAbs:ℤ) ≤ ((K+2)*p:ℕ) := by
      simpa only [Int.natCast_natAbs] using hh
    exact_mod_cast hh'
  have hF (k : ℤ) (hk : k ∈ W) : (F k).card ≤ B := by
    apply large_prime_divisors_card_le (F k) L (ξ-k*(p:ℤ)).natAbs B hL
      (by exact Int.natAbs_ne_zero.mpr (hn k))
    · intro j hj
      exact hprime j (Finset.mem_filter.mp hj).1
    · intro j hj
      exact (hsize j (Finset.mem_filter.mp hj).1).1
    · intro j hj
      exact (Finset.mem_filter.mp hj).2
    · exact (hbound k hk).trans_lt hcut
  have hsub : exceptionalPrimeIndices p ξ U J ⊆ W.biUnion F := by
    intro j hj
    obtain ⟨hj,i,hi,hcong⟩ := Finset.mem_filter.mp hj
    obtain ⟨k,hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ p).mp hcong
    have he : ξ = i*(j:ℤ)+k*(p:ℤ) := by nlinarith [hk]
    have hjm : (j:ℤ) ≤ m := by exact_mod_cast (hsize j hj).2
    have hscaleZ : (U:ℤ)*m ≤ (K:ℤ)*p := by exact_mod_cast hscale
    have hab := abs_sub ξ (i*(j:ℤ))
    rw [abs_mul,abs_of_nonneg (Int.natCast_nonneg j),he] at hab
    have hkp : |k| ≤ (K+1:ℤ) := by
      have hmul : |k*(p:ℤ)| ≤ (K+1:ℤ)*(p:ℤ) := by
        have hξ' : |i*(j:ℤ)+k*(p:ℤ)| ≤ (p:ℤ) := by rwa [← he]
        have hc : i*(j:ℤ)+k*(p:ℤ)-i*(j:ℤ) = k*(p:ℤ) := by ring
        rw [hc] at hab
        have hip : |i| *(j:ℤ) ≤ (U:ℤ)*m := by nlinarith [abs_nonneg i]
        nlinarith
      rw [abs_mul,abs_of_nonneg (Int.natCast_nonneg p)] at hmul
      have hpZ : (0:ℤ) < p := by exact_mod_cast hp
      nlinarith
    have hd : (j:ℤ) ∣ ξ-k*(p:ℤ) := ⟨i,by rw [he]; ring⟩
    have hdN : j ∣ (ξ-k*(p:ℤ)).natAbs := by
      simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hd
    exact Finset.mem_biUnion.mpr ⟨k,Finset.mem_Icc.mpr (abs_le.mp hkp),
      Finset.mem_filter.mpr ⟨hj,hdN⟩⟩
  have hW : W.card = 2*K+3 := by
    simp only [W,Int.card_Icc]
    omega
  calc
    _ ≤ (W.biUnion F).card := Finset.card_le_card hsub
    _ ≤ ∑ k ∈ W, (F k).card := Finset.card_biUnion_le
    _ ≤ ∑ _k ∈ W, B := Finset.sum_le_sum hF
    _ = _ := by simp [hW]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.exceptionalPrimeIndices_card_le
