module
public import KakeyaTwoScale.EventualRootBandEstimate
public import KakeyaTwoScale.RootBandEpsilonFactor

@[expose] public section

open Filter
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- Any positive scale loss is available for an actual normalized root band. -/
theorem eventually_root_band_epsilon (n k m : ℕ) (hk : 2≤k) (hn : n+1=m+k)
    (rate : ℝ) (hrate : 0<rate) :
    ∃ C : ℝ, 0<C ∧
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
    C*(2:ℝ)^(rate*(q:ℝ))*
      delta^((zahlB (n+1) k-(n+1))/(zahlB (n+1) k-1))*Qmax^((n+1:ℝ)/n) := by
  have hnR : 1<(n+1:ℝ) := by
    exact_mod_cast (show 1<n+1 by omega)
  have hkR : (2:ℝ)≤k := by exact_mod_cast hk
  have hknR : (k:ℝ)≤n+1 := by exact_mod_cast (show k≤n+1 by omega)
  have hB : 1<zahlB (n+1) k := zahlB_gt_one (by linarith) hkR hknR
  have ha := (zahl_optimizer_population_signs hnR hkR hknR).1
  let L : ℝ := (n+1:ℝ)+m+2
  have hL : 0<L := by dsimp [L]; positivity
  let eps := rate*(zahlB (n+1) k-1)/((k:ℝ)+zahlOptimizerWeight (n+1) k*L+1)
  have heps : 0<eps := by dsimp [eps]; positivity
  obtain ⟨eta,heta,hetale,C,hC,hroot⟩ := eventually_root_band_estimate n k m hk hn eps heps
  refine ⟨C^(1/(zahlB (n+1) k-1)),Real.rpow_pos_of_pos hC _,?_⟩
  filter_upwards [hroot] with q hroot
  intro hq N Y a b u hu hsep hinc hne normN
  dsimp only
  intro hN hNbound hcount theta mu Qmax htheta hmu hQmax hmax hwedge rlo rhi
  have hh := hroot hq N Y a b u hu hsep hinc hne normN hN hNbound hcount
    theta mu Qmax htheta hmu hQmax hmax hwedge rlo rhi
  have hden : 0<(k:ℝ)+zahlOptimizerWeight (n+1) k*L+1 := by positivity
  have heq : ((k:ℝ)+zahlOptimizerWeight (n+1) k*L+1)*eps=rate*(zahlB (n+1) k-1) := by
    dsimp [eps]
    field_simp
  have hbudget : (k:ℝ)*eta+zahlOptimizerWeight (n+1) k*L*eps≤rate*(zahlB (n+1) k-1) := by
    have hh := mul_le_mul_of_nonneg_left (show eta≤eps by linarith) (by positivity : (0:ℝ)≤k)
    nlinarith only [hh,heq,heps]
  have hf := root_band_epsilon_factor hB hC (Nat.cast_nonneg (α:=ℝ) q) hbudget
  exact hh.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hf (Real.rpow_nonneg (by positivity) _)) (Real.rpow_nonneg hQmax.le _))

end KakeyaTwoScale
#print axioms KakeyaTwoScale.eventually_root_band_epsilon
