module
public import KakeyaTwoScale.UnitWedgeBandIntegral
public import KakeyaTwoScale.BoundedScaleNormalization

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- Uniform positive-band bound on any radius interval separated from zero.
The constant precedes every family, translation and band; small scales cannot
be dismissed merely because their dyadic indices are finite. -/
theorem bounded_scale_wedge_bands (n k : ℕ) (hk : 0<k)
    (B gamma e eta : ℝ) (hB : 1<B) (hg : 1≤gamma) (he : e≤0)
    (heta : 0<eta) (heta1 : eta≤1) :
    ∃ C : ℝ, 0<C ∧ ∀ delta : ℝ, eta≤delta → delta≤1/2 →
      ∀ (N : ℕ) (b u : Fin N→EuclideanSpace ℝ (Fin (n+1))),
      (∀i, ‖u i‖=1) →
      (∀i j, i≠j → delta≤Real.arccos |inner ℝ (u i) (u j)|) →
      ∀ j : ℕ,
      (∫⁻x, ENNReal.ofReal ((originalWedgeBand k u
        (fun i => flatCylinder (b i) (u i) 1 delta) B j x)^(B/((k:ℝ)*(B-1)))))≤
      ENNReal.ofReal (C*delta^e*(∑i, volume.real (flatCylinder (b i) (u i) 1 delta))^gamma) := by
  classical
  obtain ⟨K,hK,hpack⟩ := projective_direction_count_sharp n
  obtain ⟨c,hc,hvol⟩ := flatCylinder_volume_lower_unrestricted n
  let M := K*eta^(1-(n+1:ℝ))
  let v := c*eta^n
  let p := B/(B-1)
  have hM : 0<M := by dsimp [M]; positivity
  have hv : 0<v := by dsimp [v]; positivity
  have hp : 1<p := (zahl_holder_conjugacy hB).1
  have hp0 : B/(B-1)-1≠0 := by dsimp [p] at hp; linarith
  refine ⟨M^(p-1)*v^(1-gamma),by positivity,?_⟩
  intro delta hlow hhigh N b u hu hsep j
  have hd : 0<delta := heta.trans_le hlow
  let T := fun i => flatCylinder (b i) (u i) 1 delta
  let V : ℝ := ∑i, volume.real (T i)
  have hbase := originalWedgeBand_lintegral_crude hk u hu T
    (fun i => (isOpen_flatCylinder _ _ _ _ (hu i)).measurableSet) volume hB j
  have hsum : (∑i, volume (T i))=ENNReal.ofReal V := by
    dsimp only [V]
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => measureReal_nonneg)]
    apply Finset.sum_congr rfl
    intro i _
    exact (ENNReal.ofReal_toReal (flatCylinder_unit_finite _ _ _)).symm
  rw [hsum,←ENNReal.ofReal_mul (by positivity)] at hbase
  by_cases hN : N=0
  · subst N
    simp only [Nat.cast_zero,Real.zero_rpow hp0,zero_mul,ENNReal.ofReal_zero] at hbase
    exact hbase.trans bot_le
  have hN1 : (1:ℝ)≤N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN
  have hcap : (N:ℝ)≤M := hpack eta heta heta1 N u hu (fun i j hij => hlow.trans (hsep i j hij))
  have hVlower : c*(N:ℝ)*delta^n≤V := by
    have hh := Finset.sum_le_sum (s:=(Finset.univ : Finset (Fin N)))
      (fun i _ => hvol delta hd hhigh (b i) (u i) (hu i))
    simpa [V,T,mul_comm,mul_left_comm,mul_assoc] using hh
  have hfloor : v≤V := by
    apply le_trans _ hVlower
    have hh := pow_le_pow_left₀ heta.le hlow n
    dsimp [v]
    have hcn : c≤c*(N:ℝ) := le_mul_of_one_le_right hc.le hN1
    exact mul_le_mul hcn hh (pow_nonneg heta.le _) (by positivity)
  have hV : 0<V := hv.trans_le hfloor
  have hh := bounded_scale_normalization hV hv hM (Nat.cast_nonneg N) hd (by linarith)
    hp.le hg he hcap hfloor
  exact hbase.trans (ENNReal.ofReal_le_ofReal hh)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.bounded_scale_wedge_bands
