module
public import KakeyaTwoScale.CoarseRootMassEstimate
public import KakeyaTwoScale.CoarsePopulationRecombination

@[expose] public section

open Filter
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2000000
namespace KakeyaTwoScale

/-- Global finite original-relation mass. Exact whole-fiber splitting and
bounded original-tube visits remove dependence on the occupied coarse blocks. -/
theorem eventually_global_root_mass (n k m : ℕ) (hk : 2≤k) (hn : n+1=m+k)
    (rate : ℝ) (hrate : 0<rate) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ q : ℕ in atTop, 1≤q ∧
      ∀ (N : ℕ) (Y : Finset (RootTuple (n+1) k (Fin N)))
      (b u : Fin N→EuclideanSpace ℝ (Fin (n+1))),
      (∀ o, ‖u o‖=1) →
      (∀ o p, o≠p → ((2:ℝ)^q)⁻¹≤Real.arccos |inner ℝ (u o) (u p)|) →
      (∀ y∈Y, ∀ j, (rootGridCube ((2:ℝ)^q)⁻¹ y.1 ∩
        flatCylinder (b (y.2 j)) (u (y.2 j)) 1 ((2:ℝ)^q)⁻¹).Nonempty) →
      ∀ theta : ℝ, 0<theta →
      (∀y∈Y, theta≤tupleWedgeVolume (fun j => u (y.2 j))) →
      theta^(1/(zahlB (n+1) k-1))*(((2:ℝ)^q)⁻¹)^(n+1)*
        tupleCubeMass Y Prod.fst (Y.image Prod.fst) (zahlB (n+1) k/((k:ℝ)*(zahlB (n+1) k-1))) ≤
      C*(2:ℝ)^(rate*(q:ℝ))*
        (((2:ℝ)^q)⁻¹)^((zahlB (n+1) k-(n+1))/(zahlB (n+1) k-1))*
          ((((2:ℝ)^q)⁻¹)^n*N)^((n+1:ℝ)/n) := by
  classical
  obtain ⟨C,hC,hroot⟩ := eventually_coarse_root_mass n k m hk hn rate hrate
  let gamma : ℝ := (n+1:ℝ)/n
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hg : 1≤gamma := by dsimp [gamma]; apply (le_div_iff₀ hn0).mpr; linarith
  let K : ℝ := (13:ℝ)^(n+1)*k
  have hK : 0<K := by
    dsimp [K]
    have : 0<k := by omega
    positivity
  refine ⟨C*K^gamma,by positivity,?_⟩
  filter_upwards [hroot] with q hroot
  refine ⟨hroot.1,?_⟩
  intro N Y b u hu hsep hinc theta htheta hwedge
  let delta := ((2:ℝ)^q)⁻¹
  let beta := zahlB (n+1) k/((k:ℝ)*(zahlB (n+1) k-1))
  have hB : 1<zahlB (n+1) k := zahlB_gt_one (by positivity) (by exact_mod_cast hk)
    (by exact_mod_cast (show k≤n+1 by omega))
  have hb : 0<beta := by dsimp [beta]; positivity
  have hd : 0<delta := by dsimp [delta]; positivity
  have hd1 : delta≤1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  let domains := (Y.image Prod.fst).image (rootCoarseOwner delta)
  let pop (a : Fin (n+1)→ℤ) : ℝ :=
    delta^n*∑j : Fin k, (((coarseRootTuples Y delta a).image (fun y => y.2 j)).card:ℝ)
  have hpop (a) : 0≤pop a :=
    mul_nonneg (pow_nonneg hd.le n) (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _))
  have hlocal (a) :
      theta^(1/(zahlB (n+1) k-1))*delta^(n+1)*
        tupleCubeMass (coarseRootTuples Y delta a) Prod.fst (Y.image Prod.fst) beta ≤
      C*(2:ℝ)^(rate*(q:ℝ))*delta^((zahlB (n+1) k-(n+1))/(zahlB (n+1) k-1))*(pop a)^gamma := by
    let Z := coarseRootTuples Y delta a
    have hsub : Z⊆Y := Finset.filter_subset _ _
    rw [tupleCubeMass_image Z Prod.fst (Y.image Prod.fst) beta hb (Finset.image_subset_image hsub)]
    by_cases hne : Z.Nonempty
    · have hpos : 0<pop a := by
        let j : Fin k := ⟨0,by omega⟩
        have hj : (0:ℝ)<(Z.image (fun y => y.2 j)).card := by
          exact_mod_cast Finset.card_pos.mpr (hne.image (fun y => y.2 j))
        have hs : (0:ℝ)<∑j : Fin k, ((Z.image (fun y => y.2 j)).card:ℝ) :=
          lt_of_lt_of_le hj (Finset.single_le_sum (f:=fun l : Fin k => ((Z.image (fun y => y.2 l)).card:ℝ)) (fun _ _ => Nat.cast_nonneg _) (Finset.mem_univ j))
        exact mul_pos (pow_pos hd n) hs
      exact hroot.2 N Z hne a b u hu hsep
        (fun y hy => (Finset.mem_filter.mp hy).2) (fun y hy j => hinc y (hsub hy) j)
        theta (pop a) htheta hpos
        (fun j => mul_le_mul_of_nonneg_left
          (Finset.single_le_sum (f:=fun l : Fin k => ((Z.image (fun y => y.2 l)).card:ℝ)) (fun _ _ => Nat.cast_nonneg _) (Finset.mem_univ j)) (pow_nonneg hd.le n))
        (fun y hy => hwedge y (hsub hy))
    · have he : Z=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      rw [he]
      simp only [tupleCubeMass,Finset.image_empty,Finset.sum_empty,mul_zero]
      exact mul_nonneg (by positivity) (Real.rpow_nonneg (hpop a) _)
  have hsum := Finset.sum_le_sum (s:=domains) (fun a _ => hlocal a)
  rw [←Finset.mul_sum,coarseRootTuples_mass_sum Y delta (Y.image Prod.fst) hb,←Finset.mul_sum] at hsum
  have hpopSum := coarse_population_sum_le Y hd hd1 b u hu hinc domains n
  have hpower : (∑a∈domains, (pop a)^gamma)≤(K*(delta^n*N))^gamma :=
    (sum_rpow_le_rpow_sum domains pop hg (fun a _ => hpop a)).trans
      (Real.rpow_le_rpow (Finset.sum_nonneg (fun a _ => hpop a)) hpopSum (by linarith))
  have hfinal := hsum.trans (mul_le_mul_of_nonneg_left hpower
    (show 0≤C*(2:ℝ)^(rate*(q:ℝ))*delta^((zahlB (n+1) k-(n+1))/(zahlB (n+1) k-1)) by positivity))
  rw [Real.mul_rpow hK.le (mul_nonneg (pow_nonneg hd.le n) (Nat.cast_nonneg N))] at hfinal
  convert hfinal using 1
  ring

end KakeyaTwoScale
#print axioms KakeyaTwoScale.eventually_global_root_mass
