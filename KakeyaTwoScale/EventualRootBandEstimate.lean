module
public import KakeyaTwoScale.EventualConcreteStopping
public import KakeyaTwoScale.ActualRootBandBound
public import KakeyaTwoScale.RootLossPower

@[expose] public section

open Filter
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- A normalized positive joint root band, with the archive constructed and
all degree constraints discharged. The displayed loss rate is uniform in the
scale, original cylinders, coarse block and band. -/
theorem eventually_root_band_estimate (n k m : ℕ) (hk : 2≤k) (hn : n+1=m+k)
    (epsilon : ℝ) (he : 0<epsilon) :
    ∃ eta : ℝ, 0<eta ∧ eta≤epsilon/2 ∧ ∃ C : ℝ, 0<C ∧
    ∀ᶠ q : ℕ in atTop,
      ∀ (_hq : 1≤q) (N : ℕ) (Y : Finset (RootTuple (n+1) k (Fin N))) (a : Fin (n+1)→ℤ)
      (b u : Fin N→EuclideanSpace ℝ (Fin (n+1))) (_hu : ∀ o, ‖u o‖=1)
      (_hsep : ∀ o p, o≠p → ((2:ℝ)^q)⁻¹≤Real.arccos |inner ℝ (u o) (u p)|)
      (_hinc : ∀ y∈Y, ∀ j, (rootGridCube ((2:ℝ)^q)⁻¹ y.1 ∩
        flatCylinder (b (y.2 j)) (u (y.2 j)) 1 ((2:ℝ)^q)⁻¹).Nonempty)
      (_hne : (coarseRootTuples Y ((2:ℝ)^q)⁻¹ a).Nonempty)
      (normN : Fin k→ℝ),
    let W := concreteRootState Y q a b u
    let delta := ((2:ℝ)^q)⁻¹
    (∀j, 0<normN j) → (∀j, normN j≤N) → (∀j, (W.count j:ℝ)≤normN j) →
    ∀ theta mu Qmax : ℝ, 0<theta → 0 < mu → 0<Qmax →
    (∀j, delta^n*normN j≤Qmax) →
    (∀y∈W.tuples, theta≤tupleWedgeVolume (fun j => u (y.2 j))) →
    (∀z∈W.tuples.image Prod.fst, mu^k≤(ParentLevel.capacity W.tuples Prod.fst z:ℝ)) →
    (∀z∈W.tuples.image Prod.fst, (ParentLevel.capacity W.tuples Prod.fst z:ℝ)≤2*mu^k) →
    theta^(1/(zahlB (n+1) k-1))*mu^(zahlB (n+1) k/(zahlB (n+1) k-1))*
      ((W.tuples.image Prod.fst).card:ℝ)*delta^(n+1) ≤
    (C*(2:ℝ)^((k:ℝ)*eta*(q:ℝ))*
      Real.exp (zahlOptimizerWeight (n+1) k*((n+1:ℝ)+m+2)*(epsilon*(q:ℝ)*Real.log 2)))^(1/(zahlB (n+1) k-1))*
      delta^((zahlB (n+1) k-(n+1))/(zahlB (n+1) k-1))*Qmax^((n+1:ℝ)/n) := by
  classical
  let alpha : ℝ := 1/((k-1:ℕ):ℝ)
  have hkm : 0<((k-1:ℕ):ℝ) := by exact_mod_cast (show 0<k-1 by omega)
  have hp : 0<alpha := by dsimp [alpha]; positivity
  have hp1 : alpha≤1 := by
    dsimp [alpha]
    exact (div_le_one hkm).mpr (by exact_mod_cast (show 1≤k-1 by omega))
  have hα : 1/(k:ℝ)≤alpha := by
    apply one_div_le_one_div_of_le hkm
    exact_mod_cast (show k-1≤k by omega)
  obtain ⟨eta,heta,hetale,tau,htau,t,ht,hstop⟩ :=
    eventually_concrete_stopped_optimization n k m hk hn alpha 2 epsilon hp hp1 hα (by norm_num) he
  obtain ⟨C,hC,hroot⟩ := ActualBufferedArchive.exists_normalized_root_band_bound n k hk (by omega)
  obtain ⟨Q,hQ⟩ := exists_nat_gt (2/tau)
  refine ⟨eta,heta,hetale,C,hC,?_⟩
  filter_upwards [hstop,eventually_ge_atTop Q] with q hstop hqQ
  intro hq N Y a b u hu hsep hinc hne normN
  dsimp only
  intro hN hNbound hcount theta mu Qmax htheta hmu hQmax hmax hwedge rlo rhi
  let I := concreteRootAmbient (by omega : 0<n+1) (by omega : 0<k) hq ht Y a b u hu hsep hinc hne alpha hp hp1
  have hIW : I.W=concreteRootState Y q a b u := rfl
  have hIcubes : I.cubes=(concreteRootState Y q a b u).tuples.image Prod.fst := rfl
  have hId : I.δ=((2:ℝ)^q)⁻¹ := rfl
  have hcountI : ∀j, (I.W.count j:ℝ)≤normN j := by rw [hIW]; exact hcount
  have hd := I.width_pos
  have hqR : (Q:ℝ)≤q := by exact_mod_cast hqQ
  have ha : 0<⌊tau*(q:ℝ)⌋₊ := (floor_drop_bounds (by
    have hh := (div_lt_iff₀ htau).mp (hQ.trans_le hqR)
    linarith)).1
  obtain ⟨H⟩ := I.exists_actual_archive normN 1 1 ha ht (fun j => (hN j).le)
    (by norm_num) (by norm_num) (by simpa only [one_mul,mul_one] using hcountI) m (by omega)
  have hpop (j : Fin k) : 0<I.δ^n*normN j := mul_pos (pow_pos hd n) (hN j)
  obtain ⟨j,hj,hmin⟩ := Finset.exists_min_image Finset.univ (fun j : Fin k => I.δ^n*normN j)
    ⟨⟨0,by omega⟩,Finset.mem_univ _⟩
  let w := I.δ^n*normN j
  have hw : 0<w := hpop j
  have hlogmin (l : Fin k) : Real.log w≤Real.log (normN l*I.δ^n) := by
    simpa only [mul_comm] using Real.log_le_log hw (hmin l (Finset.mem_univ l))
  obtain ⟨hloss,hproducts,r,hr,hrm,hobj⟩ := hstop hq N Y a b u hu hsep hinc hne normN H
    hN hNbound hcount mu hmu rlo rhi (Real.log w) hlogmin
  have hgrain : (I.W.grains I.cube).card=1 := by
    change ((concreteRootState Y q a b u).grains Prod.fst).card=1
    rw [concreteRootState_grains Y q a b u hne]
    rfl
  have han := hroot H rfl HEq.rfl (by intro y _ z _ hc htube; exact Prod.ext hc htube)
    rfl hgrain (fun j => (hN j).le) (by norm_num) (by simpa only [one_mul,mul_one] using hcountI)
    theta htheta.le hwedge m hn r hr hrm mu hmu rlo
  have hcubes : (0:ℝ)<I.cubes.card := by
    have hc : I.cubes.Nonempty := hne.image Prod.fst
    exact_mod_cast Finset.card_pos.mpr hc
  have hupper := (H.countLedger_positive (by norm_num : (0:ℝ)<1) (by norm_num) _ (H.entryAt_mem r hr)).2
  have hupperpos : 0<(H.entryAt r hr).upper := by linarith
  have hF : 0<C*H.loss^(k-1)*(H.entryAt r hr).upper^k := by have := H.loss_pos; positivity
  have hlength := root_band_effective_length n k (by omega) I.cubes.card mu I.δ normN hd hN
  have hobj' : (m:ℝ)*(m+1)/(2*(n+1:ℕ))*
      Real.log ((((I.cubes.card:ℝ)*I.δ^(n+1))*mu/(∏j, I.δ^n*normN j)^(1/(k:ℝ)))/I.δ)+
      (1/2-(((n+1:ℕ):ℝ)-m)*(((n+1:ℕ):ℝ)-m-1)/(2*(n+1:ℕ)*(((n+1:ℕ):ℝ)-1)))*
        (Real.log w-((n+1:ℝ)+m+2)*(epsilon*(q:ℝ)*Real.log 2)) ≤
      degreeObjectiveLog m r (fun i => Real.log (H.stageDegrees[i]?.getD 1)) := by
    rw [hlength]
    simpa only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right] using hobj
  have hmass := optimized_zahl_band_of_objective (n:=n+1) (m:=m) (k:=k) (r:=r)
    (by omega) hk hn (fun i => Real.log (H.stageDegrees[i]?.getD 1))
    theta mu ((I.cubes.card:ℝ)*I.δ^(n+1)) I.δ (∏j, I.δ^n*normN j) w Qmax
    (C*H.loss^(k-1)*(H.entryAt r hr).upper^k)
    (((n+1:ℝ)+m+2)*(epsilon*(q:ℝ)*Real.log 2)) htheta hmu (by positivity) hd
    (Finset.prod_pos (fun j _ => hpop j)) hw hQmax hF (by simpa only [Nat.cast_add,Nat.cast_one] using han) hobj'
    (finite_population_product_le _ j Qmax (fun j => (hpop j).le) hmax) (hmax j)
  have hpower := root_loss_power_le (by omega : 1≤k) H.loss_one_le hupperpos.le
    (hproducts _ (H.entryAt_mem r hr))
  have hpowers : ((2:ℝ)^(eta*(q:ℝ)))^k=(2:ℝ)^((k:ℝ)*eta*(q:ℝ)) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
    congr 1
    ring
  rw [hpowers] at hpower
  have hb : 1<zahlB (n+1:ℕ) k := zahlB_gt_one (by positivity) (by exact_mod_cast hk)
    (by exact_mod_cast (show k≤n+1 by omega))
  have hfactor : C*H.loss^(k-1)*(H.entryAt r hr).upper^k≤C*(2:ℝ)^((k:ℝ)*eta*(q:ℝ)) := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hpower hC.le
  have heexp : zahlOptimizerWeight (n+1:ℕ) k*(((n+1:ℝ)+m+2)*(epsilon*(q:ℝ)*Real.log 2))=
      zahlOptimizerWeight (n+1:ℕ) k*((n+1:ℝ)+m+2)*(epsilon*(q:ℝ)*Real.log 2) := by ring
  rw [heexp] at hmass
  have hfinal := hmass.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (by positivity) (mul_le_mul_of_nonneg_right hfactor (Real.exp_pos _).le)
        (by positivity : 0≤1/(zahlB (n+1:ℕ) k-1))) (Real.rpow_nonneg hd.le _)) (Real.rpow_nonneg hQmax.le _))
  rw [hIcubes,hId] at hfinal
  simpa only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right,mul_assoc] using hfinal

end KakeyaTwoScale
#print axioms KakeyaTwoScale.eventually_root_band_estimate
