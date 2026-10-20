module
public import KakeyaTwoScale.RootBandEpsilonEstimate
public import KakeyaTwoScale.JointBandMassUpper

@[expose] public section

open Filter
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- Every nonempty localized original relation satisfies the root mass estimate;
its joint count band and actual archive are constructed inside the proof. -/
theorem eventually_coarse_root_mass (n k m : ℕ) (hk : 2≤k) (hn : n+1=m+k)
    (rate : ℝ) (hrate : 0<rate) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ q : ℕ in atTop, 1≤q ∧
      ∀ (N : ℕ) (Y : Finset (RootTuple (n+1) k (Fin N))), Y.Nonempty →
      ∀ (a : Fin (n+1)→ℤ) (b u : Fin N→EuclideanSpace ℝ (Fin (n+1))),
      (∀ o, ‖u o‖=1) →
      (∀ o p, o≠p → ((2:ℝ)^q)⁻¹≤Real.arccos |inner ℝ (u o) (u p)|) →
      (∀y∈Y, rootCoarseOwner ((2:ℝ)^q)⁻¹ y.1=a) →
      (∀ y∈Y, ∀ j, (rootGridCube ((2:ℝ)^q)⁻¹ y.1 ∩
        flatCylinder (b (y.2 j)) (u (y.2 j)) 1 ((2:ℝ)^q)⁻¹).Nonempty) →
      ∀ theta Qmax : ℝ, 0<theta → 0<Qmax →
      (∀j, (((2:ℝ)^q)⁻¹)^n*((Y.image (fun y => y.2 j)).card:ℝ)≤Qmax) →
      (∀y∈Y, theta≤tupleWedgeVolume (fun j => u (y.2 j))) →
      theta^(1/(zahlB (n+1) k-1))*(((2:ℝ)^q)⁻¹)^(n+1)*
        tupleCubeMass Y Prod.fst (Y.image Prod.fst) (zahlB (n+1) k/((k:ℝ)*(zahlB (n+1) k-1))) ≤
      C*(2:ℝ)^(rate*(q:ℝ))*
        (((2:ℝ)^q)⁻¹)^((zahlB (n+1) k-(n+1))/(zahlB (n+1) k-1))*Qmax^((n+1:ℝ)/n) := by
  classical
  have hk0 : 0<k := by omega
  have hB : 1<zahlB (n+1) k := zahlB_gt_one (by positivity) (by exact_mod_cast hk)
    (by exact_mod_cast (show k≤n+1 by omega))
  let beta := zahlB (n+1) k/((k:ℝ)*(zahlB (n+1) k-1))
  have hb : 0<beta := by dsimp [beta]; positivity
  obtain ⟨C,hC,hroot⟩ := eventually_root_band_epsilon n k m hk hn (rate/2) (by positivity)
  have hselect := eventually_exists_concrete_joint_band_root (n+1) k hk0 beta hb (show 0<rate/2 by positivity)
  refine ⟨(2:ℝ)^beta*C,by positivity,?_⟩
  filter_upwards [hroot,hselect] with q hroot hselect
  refine ⟨hselect.1,?_⟩
  intro N Y hne a b u hu hsep hloc hinc theta Qmax htheta hQmax hmax hwedge
  obtain ⟨j,hj,mu,Z,hmu,hpow,hZ,hneZ,hsub,hfiber,hband,hmass,_,hstate⟩ :=
    hselect.2 N Y hne a b u hu hsep hloc hinc
  let normN : Fin k→ℝ := fun l => (Y.image (fun y => y.2 l)).card
  have hN (l : Fin k) : 0<normN l := by
    dsimp only [normN]
    exact_mod_cast Finset.card_pos.mpr (hne.image (fun y => y.2 l))
  have hNbound (l : Fin k) : normN l≤N := by
    dsimp only [normN]
    exact_mod_cast (show (Y.image (fun y => y.2 l)).card≤N from (Finset.card_le_univ _).trans_eq (Fintype.card_fin N))
  have hcoarse : coarseRootTuples Z ((2:ℝ)^q)⁻¹ a=Z :=
    Finset.filter_eq_self.mpr (fun y hy => hloc y (hsub hy))
  have hnecoarse : (coarseRootTuples Z ((2:ℝ)^q)⁻¹ a).Nonempty := by rw [hcoarse]; exact hneZ
  have htuples : (concreteRootState Z q a b u).tuples=Z := hstate.1
  have hcounts (l : Fin k) : ((concreteRootState Z q a b u).count l:ℝ)≤normN l := by
    dsimp only [normN]
    exact_mod_cast hstate.2.2.2.2.2.1 l
  have hbandlo : ∀z∈(concreteRootState Z q a b u).tuples.image Prod.fst,
      mu^k≤(ParentLevel.capacity (concreteRootState Z q a b u).tuples Prod.fst z:ℝ) := by
    rw [htuples]
    exact fun z hz => (hband z hz).1
  have hbandhi : ∀z∈(concreteRootState Z q a b u).tuples.image Prod.fst,
      (ParentLevel.capacity (concreteRootState Z q a b u).tuples Prod.fst z:ℝ)≤2*mu^k := by
    rw [htuples]
    exact fun z hz => (hband z hz).2.le
  have hh := hroot hselect.1 N Z a b u hu hsep (fun y hy l => hinc y (hsub hy) l)
    hnecoarse normN hN hNbound hcounts theta mu Qmax htheta hmu hQmax hmax
    (by rw [htuples]; exact fun y hy => hwedge y (hsub hy)) hbandlo hbandhi
  rw [htuples] at hh
  have hmassZ := joint_band_mass_upper Z Prod.fst (Y.image Prod.fst) beta (2*mu^k) hb
    (Finset.image_subset_image hsub) (fun z hz => (hband z hz).2.le)
  rw [joint_band_power hk0 hB hmu] at hmassZ
  have hmass' := hmass.trans (mul_le_mul_of_nonneg_left hmassZ (by positivity))
  have hweighted := mul_le_mul_of_nonneg_left hmass'
    (show 0≤theta^(1/(zahlB (n+1) k-1))*(((2:ℝ)^q)⁻¹)^(n+1) by positivity)
  have hfinal := mul_le_mul_of_nonneg_left hh
    (show 0≤(2:ℝ)^(rate/2*(q:ℝ))*(2:ℝ)^beta by positivity)
  have hexp : (2:ℝ)^(rate/2*(q:ℝ))*(2:ℝ)^(rate/2*(q:ℝ))=(2:ℝ)^(rate*(q:ℝ)) := by
    rw [←Real.rpow_add (by norm_num : (0:ℝ)<2)]
    congr 1
    ring
  calc
    _ ≤ ((2:ℝ)^(rate/2*(q:ℝ))*(2:ℝ)^beta)*
        (theta^(1/(zahlB (n+1) k-1))*mu^(zahlB (n+1) k/(zahlB (n+1) k-1))*
          ((Z.image Prod.fst).card:ℝ)*(((2:ℝ)^q)⁻¹)^(n+1)) := by
      dsimp only [beta] at hweighted ⊢
      convert hweighted using 1
      ring
    _ ≤ ((2:ℝ)^(rate/2*(q:ℝ))*(2:ℝ)^beta)*
        (C*(2:ℝ)^(rate/2*(q:ℝ))*
          (((2:ℝ)^q)⁻¹)^((zahlB (n+1) k-(n+1))/(zahlB (n+1) k-1))*Qmax^((n+1:ℝ)/n)) := hfinal
    _ = _ := by
      calc
        _ = ((2:ℝ)^beta*C)*((2:ℝ)^(rate/2*(q:ℝ))*(2:ℝ)^(rate/2*(q:ℝ)))*
          (((2:ℝ)^q)⁻¹)^((zahlB (n+1) k-(n+1))/(zahlB (n+1) k-1))*Qmax^((n+1:ℝ)/n) := by ring
        _ = _ := by rw [hexp]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.eventually_coarse_root_mass
