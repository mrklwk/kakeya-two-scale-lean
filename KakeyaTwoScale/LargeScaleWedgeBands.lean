module
public import KakeyaTwoScale.GlobalRootMassEstimate
public import KakeyaTwoScale.WedgeBandRootScale
public import KakeyaTwoScale.EventualPositiveBandAssembly

@[expose] public section

open Filter MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
namespace KakeyaTwoScale
open Classical
set_option maxHeartbeats 1000000

/-- Uniform large-scale original wedge-band estimate. The actual archive,
root count band, finite incidence bank and coarse recombination are all
constructed; no analytic or geometric estimate remains as a premise. -/
theorem eventually_original_wedge_bands (n k : ℕ) (hk : 2≤k) (hkn : k≤n+1)
    (loss : ℝ) (hloss : 0<loss) :
    ∃ Cband : ℝ, 0<Cband ∧ ∀ᶠ q : ℕ in atTop, 1≤q →
      ∀ (N : ℕ) (b u : Fin N→EuclideanSpace ℝ (Fin (n+1))),
      (∀i, ‖u i‖=1) →
      (∀i j, i≠j → dyadicWeightCut q≤Real.arccos |inner ℝ (u i) (u j)|) →
      ∀j : ℕ,
      (∫⁻x, ENNReal.ofReal ((originalWedgeBand k u
        (fun i => flatCylinder (b i) (u i) 1 (dyadicWeightCut q)) (zahlB (n+1) k) j x)^
          (zahlB (n+1) k/((k:ℝ)*(zahlB (n+1) k-1))))) ≤
      ENNReal.ofReal (Cband*(dyadicWeightCut q)^((zahlB (n+1) k/(zahlB (n+1) k-1))*(1-(n+1:ℝ)/zahlB (n+1) k-loss))*
        (∑i, volume.real (flatCylinder (b i) (u i) 1 (dyadicWeightCut q)))^((n+1:ℝ)/n)) := by
  let B := zahlB (n+1) k
  let p : ℝ := 1/(B-1)
  let beta := B/((k:ℝ)*(B-1))
  let gamma : ℝ := (n+1:ℝ)/n
  let rate := B/(B-1)*loss
  have hB : 1<B := zahlB_gt_one (by positivity) (by exact_mod_cast hk) (by exact_mod_cast hkn)
  have hp : 0<p := by dsimp [p]; positivity
  have hb : 0<beta := by dsimp [beta]; positivity
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hg : 0<gamma := by dsimp [gamma]; positivity
  have hr : 0<rate := by dsimp [rate]; positivity
  obtain ⟨C,hC,hglobal⟩ := eventually_global_root_mass n k (n+1-k) hk (by omega) rate hr
  obtain ⟨c,hc,hvolume⟩ := flatCylinder_volume_lower_unrestricted n
  refine ⟨(2:ℝ)^p*C*(c⁻¹)^gamma,by positivity,?_⟩
  filter_upwards [hglobal] with q hglobal
  intro hq N b u hu hsep j
  let delta := dyadicWeightCut q
  let T := fun o => flatCylinder (b o) (u o) 1 delta
  let theta := dyadicWeightCut (j+1)
  let F : Finset (Fin k→Fin N) := Finset.univ.filter (fun f =>
    theta<tupleWedgeVolume (fun l => u (f l)) ∧ tupleWedgeVolume (fun l => u (f l))≤dyadicWeightCut j)
  let w := fun f : Fin k→Fin N => (tupleWedgeVolume (fun l => u (f l)))^((k:ℝ)/B)
  have hd : 0<delta := by dsimp [delta,dyadicWeightCut]; positivity
  have hdhalf : delta≤1/2 := by
    dsimp only [delta,dyadicWeightCut]
    rw [one_div]
    apply (inv_le_inv₀ (by positivity) (by norm_num)).mpr
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hq
  have htheta : 0<theta := by dsimp [theta,dyadicWeightCut]; positivity
  have hcut : dyadicWeightCut j=2*theta := by
    dsimp [theta,dyadicWeightCut]
    rw [pow_succ]
    field_simp
  obtain ⟨cubes,hbank⟩ := exists_finite_cylinder_grid_bank delta hd b u hu
  let Y := rootIncidenceTuples delta cubes F T
  have hinc : ∀y∈Y, ∀l, (rootGridCube delta y.1∩flatCylinder (b (y.2 l)) (u (y.2 l)) 1 delta).Nonempty := by
    intro y hy l
    exact ((rootIncidenceTuples_mem delta cubes F T y).mp hy).2.2 l
  have hwedge : ∀y∈Y, theta≤tupleWedgeVolume (fun l => u (y.2 l)) := by
    intro y hy
    exact (Finset.mem_filter.mp ((rootIncidenceTuples_mem delta cubes F T y).mp hy).2.1).2.1.le
  have hmass := hglobal.2 N Y b u hu hsep hinc theta htheta hwedge
  have hint := tuple_lintegral_le_root_mass (by omega : 0<k) delta hd cubes F T hbank w
    ((2*theta)^((k:ℝ)/B)) beta (by positivity) hb
    (fun f _ => Real.rpow_nonneg (tupleWedgeVolume_nonneg _) _)
    (fun f hf => Real.rpow_le_rpow (tupleWedgeVolume_nonneg _)
      (by rw [←hcut]; exact (Finset.mem_filter.mp hf).2.2) (by positivity))
  rw [wedge_band_root_weight (by omega : 0<k) hB htheta] at hint
  have hnorm : (∫⁻x, ENNReal.ofReal ((originalWedgeBand k u T B j x)^beta)) ≤
      ENNReal.ofReal ((2:ℝ)^p*(C*(2:ℝ)^(rate*(q:ℝ))*delta^((B-(n+1))/(B-1))*(delta^n*N)^gamma)) := by
    apply hint.trans
    apply ENNReal.ofReal_le_ofReal
    have hh := mul_le_mul_of_nonneg_left hmass (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) p)
    dsimp only [B,p,beta,gamma,delta,dyadicWeightCut,Y] at hh ⊢
    convert hh using 1
    ring
  let V : ℝ := ∑i, volume.real (T i)
  have hv : 0≤V := Finset.sum_nonneg (fun _ _ => measureReal_nonneg)
  have hvol : c*(delta^n*N)≤V := by
    have hh := Finset.sum_le_sum (s:=(Finset.univ : Finset (Fin N)))
      (fun i _ => hvolume delta hd hdhalf (b i) (u i) (hu i))
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
    convert hh using 1
    ring
  have hpop : delta^n*N≤c⁻¹*V := by
    have hh : delta^n*N≤V/c := (le_div_iff₀ hc).mpr (by nlinarith only [hvol])
    simpa only [div_eq_mul_inv,mul_comm] using hh
  have hpow := Real.rpow_le_rpow (mul_nonneg (pow_nonneg hd.le n) (Nat.cast_nonneg N)) hpop hg.le
  rw [Real.mul_rpow (inv_nonneg.mpr hc.le) hv] at hpow
  apply hnorm.trans
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ (2:ℝ)^p*(C*(2:ℝ)^(rate*(q:ℝ))*delta^((B-(n+1))/(B-1))*((c⁻¹)^gamma*V^gamma)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow (by positivity)) (by positivity)
    _ = ((2:ℝ)^p*C*(c⁻¹)^gamma)*
        ((2:ℝ)^(rate*(q:ℝ))*delta^((B-(n+1))/(B-1)))*V^gamma := by ring
    _ = _ := by
      have hs := dyadic_rate_scale q rate ((B-(n+1))/(B-1))
      change (2:ℝ)^(rate*(q:ℝ))*delta^((B-(n+1))/(B-1))=delta^((B-(n+1))/(B-1)-rate) at hs
      rw [hs]
      have he := published_band_scale_exponent (d:=(n+1:ℝ)) (loss:=loss) hB
      change (B-(n+1))/(B-1)-rate=B/(B-1)*(1-(n+1)/B-loss) at he
      rw [he]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.eventually_original_wedge_bands
