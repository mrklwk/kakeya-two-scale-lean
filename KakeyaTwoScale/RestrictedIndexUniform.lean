module
public import KakeyaTwoScale.RestrictedIndexAbsorption

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical Filter
open scoped BigOperators Pointwise Topology

/-- Uniform ε specialization in the nonvacuous range m≥p^ε. -/
theorem restricted_index_uniform_nonvacuous (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ N : ℕ, ∀ p : ℕ, N ≤ p → p.Prime → ∀ m : ℕ,
      (p:ℝ)^ε ≤ (m:ℝ) → m < p → ∀ A : Finset (ZMod p),
      (p:ℝ)/(m:ℝ) ≤ (A.card:ℝ) →
      ∃ G : Finset ℕ, G ⊆ Finset.Icc ((m+1)/2) m ∧
        Nat.floor ((m:ℝ)*(p:ℝ)^(-ε)) ≤ G.card ∧
        ∀ j ∈ G, (p:ℝ)^(1-ε) ≤ ((A+(positiveFieldInterval p m).image
          (fun x => (j:ZMod p)⁻¹*x)).card:ℝ) := by
  obtain ⟨d,hd⟩ := exists_nat_gt (4/ε)
  have hdegree : 4 < ε*((d:ℝ)+1) := by
    have h := (div_lt_iff₀ hε).mp hd
    nlinarith
  let δ := ε/4
  let c := Real.log (4:ℝ)/18
  let C := ((d:ℝ)+2)^(d+1)
  let F := 8*((d:ℝ)+1)^2*C^2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδε : δ < ε := by dsimp [δ]; linarith
  have hc : 0 < c := by dsimp [c]; exact div_pos (Real.log_pos (by norm_num)) (by norm_num)
  have hC : 0 < C := by dsimp [C]; positivity
  have hF : 0 < F := by dsimp [F]; positivity
  obtain ⟨Nprime,hNprime⟩ := eventually_atTop.mp halfIntervalPrimes_log_density
  have hgap : 0 < ε*(((d+1:ℕ):ℝ)+1)-1-δ := by dsimp [δ]; push_cast; nlinarith
  have htailgap : 0 < 2*((d+1:ℕ):ℝ)*δ-1 := by dsimp [δ]; push_cast; nlinarith
  obtain ⟨N,hN⟩ := eventually_atTop.mp
    (pz_uniform_power_thresholds ε δ F c (d+1) (d+1) Nprime hε hδ hgap htailgap hδε hF hc (by omega))
  refine ⟨N,?_⟩
  intro p hpN hpPrime m hem hmp A ha
  let : Fact p.Prime := ⟨hpPrime⟩
  obtain ⟨hp2,hpδ,hpε,hdivgap,htail,hlog⟩ := hN p hpN
  have hp : 0 < (p:ℝ) := by exact_mod_cast hpPrime.pos
  have hpmε : 0 < (p:ℝ)^ε := Real.rpow_pos_of_pos hp ε
  have hpmδ : 0 < (p:ℝ)^δ := Real.rpow_pos_of_pos hp δ
  have hm2 : 2 ≤ m := by
    have h := (le_trans (le_trans (le_max_left 2 (Nprime:ℝ)) (le_max_left _ _)) hpε).trans hem
    exact_mod_cast h
  have hm0 : 0 < m := by omega
  have hm : 0 < (m:ℝ) := by exact_mod_cast hm0
  have hmN : Nprime ≤ m := by
    have h := (le_trans (le_trans (le_max_right 2 (Nprime:ℝ)) (le_max_left _ _)) hpε).trans hem
    exact_mod_cast h
  let J := halfIntervalPrimes m
  let K := Nat.floor ((p:ℝ)^δ)
  let U := K*p/m
  let L := (m+1)/2
  have hprimes : ∀ j ∈ J, j.Prime := fun j hj => (Finset.mem_filter.mp hj).2
  have hsizes : ∀ j ∈ J, L ≤ j ∧ j ≤ m := fun j hj => Finset.mem_Icc.mp (Finset.mem_filter.mp hj).1
  have hL : 1 ≤ L := (half_interval_parameters m hm0).1
  have hscale : U*m ≤ K*p := (frequency_floor_parameters p m K hm0 hmp.le).1
  have hU : (K:ℝ) ≤ 1+(U:ℝ)*(m:ℝ)/(p:ℝ) := (frequency_floor_parameters p m K hm0 hmp.le).2
  have hcut : (K+2)*p < L^((d+1)+1) := floor_divisor_cut p m (d+1) ε δ hpPrime.pos hpδ hem hdivgap
  have hdensity0 : c*(m:ℝ) ≤ (J.card:ℝ)*Real.log (m:ℝ) := hNprime m hmN
  have hlogmp : Real.log (m:ℝ) ≤ Real.log (p:ℝ) := Real.log_le_log hm (by exact_mod_cast hmp.le)
  have hdensity : c*(m:ℝ) ≤ (J.card:ℝ)*Real.log (p:ℝ) :=
    hdensity0.trans (mul_le_mul_of_nonneg_left hlogmp (Nat.cast_nonneg _))
  have hJne : J.Nonempty := by
    by_contra h
    have hzero : J.card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp h)
    rw [hzero,Nat.cast_zero,zero_mul] at hdensity
    exact (not_le_of_gt (mul_pos hc hm)) hdensity
  have hJpos : 0 < (J.card:ℝ) := by exact_mod_cast Finset.card_pos.mpr hJne
  have hKbounds : (p:ℝ)^δ/2 ≤ (K:ℝ) ∧ (K:ℝ) ≤ (p:ℝ)^δ := floor_power_bounds _ hpδ
  have hden : 0 < 1+(U:ℝ)*(m:ℝ)/(p:ℝ) := by positivity
  have htail' : 2*(m:ℝ)/(1+(U:ℝ)*(m:ℝ)/(p:ℝ))^(2*(d+1)) ≤ 1 := by
    have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ (p:ℝ)^δ/2) (hKbounds.1.trans hU) (2*(d+1))
    have hdom := tail_power_domination p δ (d+1) hp htail
    apply (div_le_iff₀ (pow_pos hden _)).mpr
    have hmpR : (m:ℝ) ≤ p := by exact_mod_cast hmp.le
    simpa only [one_mul] using (show 2*(m:ℝ) ≤ _ from (by linarith : 2*(m:ℝ) ≤ 2*(p:ℝ)).trans (hdom.trans hpow))
  have hE : (((2*K+3)*(d+1):ℕ):ℝ) ≤ 5*((d+1:ℕ):ℝ)*(p:ℝ)^δ := by
    have hK3 : 2*(K:ℝ)+3 ≤ 5*(p:ℝ)^δ := by linarith [hKbounds.2]
    have h := mul_le_mul_of_nonneg_right hK3 (Nat.cast_nonneg (d+1) : (0:ℝ) ≤ (d+1:ℕ))
    push_cast at h ⊢
    nlinarith
  have hlog1 : Real.log (p:ℝ) ≤ (c/2)*((p:ℝ)^ε/(p:ℝ)^δ) := by
    rw [← Real.rpow_sub hp]
    exact hlog.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.rpow_nonneg hp.le _))
  have hlog2 : Real.log (p:ℝ) ≤ (c/(20*F*((d+1:ℕ):ℝ)))*((p:ℝ)^ε/(p:ℝ)^δ) := by
    rw [← Real.rpow_sub hp]
    exact hlog.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.rpow_nonneg hp.le _))
  have hFY : 10*F ≤ (p:ℝ)^ε := (le_max_right _ _).trans hpε
  have hbudget : F*pzEnergyBracket p m U K (d+1) (d+1) J ≤ (p:ℝ)^ε*(J.card:ℝ) :=
    pz_budget_absorption m J.card (Real.log (p:ℝ)) (((2*K+3)*(d+1):ℕ):ℝ)
      ((1+(U:ℝ)*(m:ℝ)/(p:ℝ))^(2*(d+1))) F c ((d+1:ℕ):ℝ) ((p:ℝ)^δ) ((p:ℝ)^ε)
      hm.le hJpos (pow_pos hden _) hF hc (by positivity) hpmδ hdensity hE htail' hFY hlog2
  have hcount : 2*(m:ℝ) ≤ (p:ℝ)^ε*(J.card:ℝ) :=
    pz_count_absorption m J.card (Real.log (p:ℝ)) c ((p:ℝ)^δ) ((p:ℝ)^ε)
      hJpos.le hc (by linarith) hpmε.le hdensity hlog1
  obtain ⟨G,hG,hGcard,hGsum⟩ := restricted_index_counting p m U K L (d+1) d hm0 hmp J hJne
    hprimes hsizes hL hscale hcut A ha
  refine ⟨G,?_,?_,?_⟩
  · intro j hj
    exact (Finset.mem_filter.mp (hG hj)).1
  · have hreal : (m:ℝ)/(p:ℝ)^ε ≤ (G.card:ℝ) := by
      apply (div_le_iff₀ hpmε).mpr
      have h := mul_le_mul_of_nonneg_left hGcard hpmε.le
      nlinarith
    have hf := Nat.floor_le (by positivity : 0 ≤ (m:ℝ)*(p:ℝ)^(-ε))
    have he : (m:ℝ)*(p:ℝ)^(-ε) = (m:ℝ)/(p:ℝ)^ε := by rw [Real.rpow_neg hp.le]; rfl
    rw [he] at hf ⊢
    exact_mod_cast hf.trans hreal
  · intro j hj
    have hR : 0 < pzEnergyBracket p m U K (d+1) (d+1) J := by
      unfold pzEnergyBracket
      positivity
    have hbound := hGsum j hj
    apply le_trans _ hbound
    change (p:ℝ)^(1-ε) ≤ (p:ℝ)*(J.card:ℝ)/(F*pzEnergyBracket p m U K (d+1) (d+1) J)
    rw [Real.rpow_sub hp,Real.rpow_one]
    have h := div_le_div_of_nonneg_left (show 0 ≤ (p:ℝ)*(J.card:ℝ) by positivity)
      (mul_pos hF hR) hbudget
    have he : (p:ℝ)*(J.card:ℝ)/((p:ℝ)^ε*(J.card:ℝ)) = (p:ℝ)/(p:ℝ)^ε := by field_simp
    rw [he] at h
    exact h

end KakeyaTwoScale
#print axioms KakeyaTwoScale.restricted_index_uniform_nonvacuous
