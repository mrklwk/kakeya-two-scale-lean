module
public import KakeyaTwoScale.ProgressionEnergyBudget
public import KakeyaTwoScale.ProgressionSumsetLower
public import KakeyaTwoScale.RealEnergySelection

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical
open scoped BigOperators Pointwise

def pzEnergyBracket (p m U K B D : ℕ) (J : Finset ℕ) : ℝ :=
  4*(J.card:ℝ)+2*(m:ℝ)*((2*K+3)*B:ℕ)+
    2*(m:ℝ)*(J.card:ℝ)/(1+(U:ℝ)*(m:ℝ)/(p:ℝ))^(2*D)

theorem selected_energy_card_lower (S D p e T N : ℝ)
    (hS : 0 ≤ S) (hD : 0 < D) (hp : 0 < p) (hT : 0 < T) (hN : 0 < N)
    (hprod : 1 ≤ S*(4*D^2*p*e)) (he : e ≤ 2*T/N) :
    N/(8*D^2*p*T) ≤ S := by
  have h : 1 ≤ S*(4*D^2*p*(2*T/N)) := hprod.trans
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he (by positivity)) hS)
  have hh : 1 ≤ (S*(8*D^2*p*T))/N := by convert h using 1; ring
  have hmul : N ≤ S*(8*D^2*p*T) := by simpa only [one_mul] using (le_div_iff₀ hN).mp hh
  exact (div_le_iff₀ (by positivity : 0 < 8*D^2*p*T)).mpr hmul

/-- The finite restricted-index estimate with every arithmetic parameter
explicit. The cutoff, Fourier energies and selected indices are constructed.
Only the displayed integer scale and prime-divisor inequalities remain to
be specialized to the asymptotic ε formulation. -/
theorem restricted_index_finite (p m U K L B d : ℕ) [Fact p.Prime]
    (hm0 : 0 < m) (hmp : m < p) (J : Finset ℕ) (hJne : J.Nonempty)
    (hprime : ∀ j ∈ J, j.Prime) (hsize : ∀ j ∈ J, L ≤ j ∧ j ≤ m)
    (hL : 1 ≤ L) (hscale : U*m ≤ K*p) (hcut : (K+2)*p < L^(B+1))
    (A : Finset (ZMod p)) (ha : (p:ℝ)/(m:ℝ) ≤ (A.card:ℝ))
    (haUpper : (A.card:ℝ) ≤ 2*(p:ℝ)/(m:ℝ)) :
    ∃ G : Finset ℕ, G ⊆ J ∧ (J.card:ℝ) ≤ 2*(G.card:ℝ) ∧
      ∀ j ∈ G, (p:ℝ)*(J.card:ℝ)/
        (8*((d:ℝ)+1)^2*(((d:ℝ)+2)^(d+1))^2*pzEnergyBracket p m U K B (d+1) J) ≤
          ((A+inverseProgression p m j).card:ℝ) := by
  have hp : 0 < (p:ℝ) := by exact_mod_cast NeZero.pos p
  have hJcard : 0 < (J.card:ℝ) := by exact_mod_cast Finset.card_pos.mpr hJne
  let C := ((d:ℝ)+2)^(d+1)
  let R := pzEnergyBracket p m U K B (d+1) J
  let T := C^2/(p:ℝ)^2*R
  have hC : 0 < C := by dsimp [C]; positivity
  have hR : 0 < R := by
    dsimp [R,pzEnergyBracket]
    positivity
  have hT : 0 < T := by dsimp [T]; positivity
  obtain ⟨ψ,hψ,hsupp,hmass,hdec⟩ := exists_interval_cutoff p m d hm0 hmp
  have hbudget : ∑ j ∈ J, progressionEnergy p A (fun x => (ψ x:ℂ)) j ≤ T :=
    progressionEnergy_prime_budget p m U K L B (d+1) hm0 hmp J hprime hsize hL hscale hcut
      A haUpper C hC.le (fun x => (ψ x:ℂ)) hdec
  obtain ⟨G,hG,hGcard,hGe⟩ := real_energy_half_selection J
    (progressionEnergy p A (fun x => (ψ x:ℂ))) T
    (fun j _ => progressionEnergy_nonneg p A _ j) hT.le hbudget
  refine ⟨G,hG,hGcard,?_⟩
  intro j hj
  have hjJ := hG hj
  have hj0 : (j:ZMod p) ≠ 0 := natCast_nonzero_of_prime_below p j
    (hprime j hjJ) ((hsize j hjJ).2.trans_lt hmp)
  have hprod := progression_sumset_energy_lower p m j hm0 hj0 A ha ((d:ℝ)+1) (by positivity)
    ψ (fun x => (hψ x).1) hsupp hmass
  have h := selected_energy_card_lower ((A+inverseProgression p m j).card:ℝ)
    ((d:ℝ)+1) p (progressionEnergy p A (fun x => (ψ x:ℂ)) j) T J.card
    (Nat.cast_nonneg _) (by positivity) hp hT hJcard hprod (hGe j hj)
  convert h using 1
  dsimp [T,C,R]
  field_simp

end KakeyaTwoScale
#print axioms KakeyaTwoScale.selected_energy_card_lower
#print axioms KakeyaTwoScale.restricted_index_finite
