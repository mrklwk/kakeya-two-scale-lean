module
public import KakeyaTwoScale.FiniteBroadIntegral
public import KakeyaTwoScale.VariableZahl
public import KakeyaTwoScale.SharpBallPacking

@[expose] public section

open MeasureTheory
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
open Classical

theorem bounded_graph_angular_separation (n : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ η : ℝ, 0<η ∧ η≤1 ∧ ∀ (i : Fin (n+1)) (v w : Fin n → ℝ),
      ‖v‖≤R → ‖w‖≤R → ∀ δ : ℝ, δ≤dist v w →
      η*δ≤Real.arccos |inner ℝ (graphUnitDirection i v) (graphUnitDirection i w)| := by
  let h : ℝ := 1/((n+2:ℝ)*(R+1))
  let Q : ℝ := 1+1/h+1/(h*h)
  have hh : 0<h := by dsimp [h]; positivity
  have hQ : 0<Q := by dsimp [Q]; positivity
  refine ⟨1/Q,by positivity,?_,?_⟩
  · apply (div_le_one hQ).mpr
    dsimp [Q]
    have : 0≤1/h+1/(h*h) := by positivity
    linarith
  intro i v w hv hw δ hδ
  let u := graphUnitDirection i v
  let e := graphUnitDirection i w
  let θ := Real.arccos |inner ℝ u e|
  have hu : ‖u‖=1 := graphUnitDirection_norm i v
  have he : ‖e‖=1 := graphUnitDirection_norm i w
  have hui : h≤|u i| := (graphUnitDirection_height i v R hR hv).trans (le_abs_self _)
  have hei : h≤|e i| := (graphUnitDirection_height i w R hR hw).trans (le_abs_self _)
  have ht : 0≤θ := Real.arccos_nonneg _
  have hc : dist v w ≤ (1/h+1/(h*h))*θ := by
    rcases source_cap_chord_choice u e hu he θ le_rfl with hp | hm
    · have hc := (chartSlope_dist_le i u e he h hh hui hei).trans
        (mul_le_mul_of_nonneg_left hp (by positivity))
      simpa only [u,e,graphUnitDirection_chart] using hc
    · have hne : h≤|(-e) i| := by simpa using hei
      have hc := (chartSlope_dist_le i u (-e) (by simpa using he) h hh hui hne).trans
        (mul_le_mul_of_nonneg_left hm (by positivity))
      simpa only [chartSlope_neg,u,e,graphUnitDirection_chart] using hc
  change 1/Q*δ≤θ
  rw [one_div,mul_comm,← div_eq_mul_inv]
  apply (div_le_iff₀ hQ).mpr
  dsimp [Q]
  nlinarith

/-- Constants precede the scale and family; bounded separated graph slopes
supply the projective separation required by the sole deep Zahl input. -/
theorem finite_graph_zahl_norm (n k : ℕ) (Z : ZahlCapsuleEstimate (n+1) k)
    (R D : ℝ) (hR : 0≤R) (hD : 0<D) :
    ∀ ε : ℝ, 0<ε → ∃ K : ℝ, 0<K ∧ ∀ δ : ℝ, 0<δ → δ<1/2 →
    ∀ {J : Type*} (G : Finset J) (b v : J → Fin n → ℝ) (i : Fin (n+1)),
    (∀ j∈G, ‖v j‖≤R) →
    (∀ j∈G, ∀ l∈G, j≠l → δ≤dist (v j) (v l)) →
    eLpNorm (multilinearKakeyaFunction k
      (fun a => graphUnitDirection i (v (finiteFamilyIndex G a)))
      (fun a => euclideanTube (euclideanUnsplit i (0,b (finiteFamilyIndex G a)))
        (euclideanUnsplit i (1,v (finiteFamilyIndex G a))) (D*δ)) (zahlB (n+1) k))
      (ENNReal.ofReal (zahlB (n+1) k/(zahlB (n+1) k-1))) volume ≤
    ENNReal.ofReal (K*δ^(1-(n+1:ℝ)/zahlB (n+1) k-ε)*
      (δ^n*(G.card:ℝ))^(zahlMassExponent (n+1) k)) := by
  obtain ⟨η,hη,hηone,hangle⟩ := bounded_graph_angular_separation n R hR
  let L : ℝ := D/η+(n+2:ℝ)*(R+1)+1
  have hDL : D/η≤L := by
    dsimp [L]
    have : 0≤(n+2:ℝ)*(R+1) := by positivity
    linarith
  have hLone : 1≤L := by
    dsimp [L]
    have : 0≤D/η+(n+2:ℝ)*(R+1) := by positivity
    linarith
  have hklo := Z.1
  have hkhi := Z.2.1
  have hB : 1<zahlB (n+1) k := zahlB_gt_one (by positivity)
    (by exact_mod_cast hklo) (by exact_mod_cast hkhi)
  have hn1 : (1:ℝ)<n+1 := by have : 2≤n+1 := hklo.trans hkhi; exact_mod_cast this
  have hα : 0≤zahlMassExponent (n+1) k := by unfold zahlMassExponent; positivity
  intro ε hε
  obtain ⟨K,hK,hbound⟩ := variable_capsule_zahl_estimate n k Z (D/η) L (div_pos hD hη) hDL hLone ε hε
  let A : ℝ := 3*(2*(n+3:ℝ))^n
  let a : ℝ := 1-(n+1:ℝ)/zahlB (n+1) k-ε
  refine ⟨K*η^a*A^(zahlMassExponent (n+1) k),by dsimp [A]; positivity,?_⟩
  intro δ hδ hδhalf J G b v i hv hsep
  let e := finiteFamilyIndex G
  have hem (a : Fin G.card) : e a∈G := (G.equivFin.symm a).property
  have heinj : Function.Injective e := by
    intro a b hab
    apply G.equivFin.symm.injective
    exact Subtype.ext hab
  have hs : η*δ≤δ := mul_le_of_le_one_left hδ.le hηone
  have hn := hbound (η*δ) (mul_pos hη hδ) (hs.trans_lt hδhalf) G.card
    (fun a => euclideanUnsplit i (0,b (e a))) (fun a => graphUnitDirection i (v (e a)))
    (fun a => ‖euclideanUnsplit i (1,v (e a))‖)
    (fun a => graphUnitDirection_norm i _) (fun a => ⟨norm_nonneg _,
      (graph_axis_length i (v (e a)) R hR (hv _ (hem a))).2.1.trans
        (by
          dsimp [L]
          have : 0≤D/η := by positivity
          linarith)⟩)
    (fun a b hab => hangle i (v (e a)) (v (e b)) (hv _ (hem a)) (hv _ (hem b)) δ
      (hsep _ (hem a) _ (hem b) (fun he => hab (heinj he))))
  have haxis (a : Fin G.card) : ‖euclideanUnsplit i (1,v (e a))‖ • graphUnitDirection i (v (e a)) =
      euclideanUnsplit i (1,v (e a)) := (graph_axis_length i _ R hR (hv _ (hem a))).2.2.symm
  simp only [haxis,show D/η*(η*δ)=D*δ by field_simp] at hn
  have hmass : (∑ a : Fin G.card,volume.real (euclideanTube (euclideanUnsplit i (0,b (e a)))
      (graphUnitDirection i (v (e a))) (η*δ))) ≤ A*(δ^n*(G.card:ℝ)) := by
    calc
      _ ≤ ∑ a : Fin G.card, A*δ^n := Finset.sum_le_sum (fun a _ =>
        (euclideanTube_volume_upper _ _ (mul_pos hη hδ) (hs.trans hδhalf.le)
          (graphUnitDirection_norm i _)).trans (by dsimp [A]; gcongr))
      _ = _ := by simp; ring
  have hpow := Real.rpow_le_rpow (Finset.sum_nonneg (fun _ _ => measureReal_nonneg)) hmass hα
  apply hn.trans
  apply ENNReal.ofReal_le_ofReal
  have hm := mul_le_mul_of_nonneg_left hpow (show 0≤K*(η*δ)^a by positivity)
  convert hm using 1
  rw [Real.mul_rpow hη.le hδ.le,Real.mul_rpow (show 0≤A by dsimp [A]; positivity) (by positivity)]
  ring

/-- Exact scalar inversion of the broad Holder inequality. -/
theorem broad_scalar_power (U V δ rho K c B a α t : ℝ)
    (hU : 0<U) (hV : 0≤V) (hδ : 0<δ) (hrho : 0<rho)
    (hK : 0<K) (hc : 0<c) (hB : 0<B)
    (h : U/4 ≤ K*δ^a*U^α*V^(1/B)/(c*rho^t)) :
    (c/(4*K))^B*δ^(-a*B)*rho^(t*B)*U^((1-α)*B) ≤ V := by
  let Y := c/(4*K)*δ^(-a)*rho^t*U^(1-α)
  have hid : Y=(U/4*(c*rho^t))/(K*δ^a*U^α) := by
    dsimp [Y]
    rw [Real.rpow_sub hU,Real.rpow_one,Real.rpow_neg hδ.le]
    field_simp
  have h1 := (le_div_iff₀ (show 0<c*rho^t by positivity)).mp h
  have h2 : Y≤V^(1/B) := by
    rw [hid]
    apply (div_le_iff₀ (show 0<K*δ^a*U^α by positivity)).mpr
    nlinarith only [h1]
  have hp := Real.rpow_le_rpow (show 0≤Y by dsimp [Y]; positivity) h2 hB.le
  rw [one_div,Real.rpow_inv_rpow hV hB.ne'] at hp
  convert hp using 1
  dsimp [Y]
  rw [Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_mul hδ.le,← Real.rpow_mul hrho.le,← Real.rpow_mul hU.le]

/-- Actual finite broad volume bound, conditional only on Zahl. The retained
mass exponent is kept explicit for subsequent logarithmic level selection. -/
theorem finite_graph_broad_volume (n k : ℕ) (Z : ZahlCapsuleEstimate (n+1) k)
    (R D : ℝ) (hR : 0≤R) (hD : 4*(n+2:ℝ)+1≤D) :
    ∀ ε : ℝ, 0<ε → ∃ c : ℝ, 0<c ∧ ∀ δ rho : ℝ, 0<δ → δ<1/2 → 0<rho →
    ∀ {J : Type*} [Countable J] (G : Finset J), G.Nonempty →
    ∀ (b v : J → Fin n → ℝ) (i : Fin (n+1)),
    (∀ j∈G, ‖v j‖≤R) →
    (∀ j∈G, ∀ l∈G, j≠l → δ≤dist (v j) (v l)) →
    let S := finiteGridBroadRegion G b v (fun j => graphUnitDirection i (v j)) (k-1) δ rho
    let U := δ^n*(G.card:ℝ)
    U/4 ≤ (∫ x in S,gridMultiplicity G b v δ x) →
    c*δ^((n+1:ℝ)-zahlB (n+1) k+zahlB (n+1) k*ε)*rho^((k:ℝ)-1)*
      U^(((n+1:ℝ)-zahlB (n+1) k)/n) ≤ volume.real S := by
  have hDpos : 0<D := by
    have : 0<(4*(n+2:ℝ)+1) := by positivity
    linarith
  have hklo := Z.1
  have hkhi := Z.2.1
  have hnpos : (0:ℝ)<n := by have : 2≤n+1 := hklo.trans hkhi; exact_mod_cast (by omega : 0<n)
  have hB : 1<zahlB (n+1) k := zahlB_gt_one (by positivity)
    (by exact_mod_cast hklo) (by exact_mod_cast hkhi)
  intro ε hε
  obtain ⟨K,hK,hbound⟩ := finite_graph_zahl_norm n k Z R D hR hDpos ε hε
  let B := zahlB (n+1) k
  let c0 := broadCoefficient (k-1) B
  have hc0 : 0<c0 := broadCoefficient_pos _ _
  refine ⟨(c0/(4*K))^B,by positivity,?_⟩
  intro δ rho hδ hδhalf hrho J inst G hG b v i hv hsep
  dsimp only
  intro hmass
  have hh := finite_grid_broad_integral_of_norm_bound G b v i δ rho D B
    (K*δ^(1-(n+1:ℝ)/B-ε)*(δ^n*(G.card:ℝ))^(zahlMassExponent (n+1) k))
    hδ hrho hD hB (by positivity) (by omega) hkhi
    (hbound δ hδ hδhalf G b v i hv hsep)
  have hU : 0<δ^n*(G.card:ℝ) := mul_pos (pow_pos hδ n) (by exact_mod_cast G.card_pos.mpr hG)
  have hp := broad_scalar_power (δ^n*(G.card:ℝ)) _ δ rho K c0 B
    (1-(n+1:ℝ)/B-ε) (zahlMassExponent (n+1) k) (((k:ℝ)-1)/B)
    hU measureReal_nonneg hδ hrho hK hc0 (by linarith) (hmass.trans hh.2)
  have hBne : B≠0 := by dsimp [B]; linarith
  have he1 : -(1-(n+1:ℝ)/B-ε)*B=(n+1:ℝ)-B+B*ε := by field_simp [hBne]; ring
  have he2 : (((k:ℝ)-1)/B)*B=(k:ℝ)-1 := div_mul_cancel₀ _ (by linarith)
  have he3 : (1-zahlMassExponent (n+1) k)*B=((n+1:ℝ)-B)/n := by
    change (1-((n+1:ℝ)*(B-1)/(((n+1:ℝ)-1)*B)))*B=((n+1:ℝ)-B)/n
    rw [add_sub_cancel_right]
    field_simp [hBne,hnpos.ne']
    ring
  simpa only [he1,he2,he3] using hp

theorem finiteGridBroadRegion_subset_occupied {J : Type*} [Countable J] {n k : ℕ}
    (G : Finset J) (b v : J → Fin n → ℝ) (u : J → EuclideanSpace ℝ (Fin (n+1)))
    (δ rho : ℝ) (hk : k≤n+1) :
    finiteGridBroadRegion G b v u k δ rho ⊆
      occupiedGridRegion G b v δ (fun _ => Set.Icc (0:ℝ) 1) := by
  intro x hx
  by_contra hno
  have he : finiteIncidentPattern G
      (fun j => gridPortion (b j) (v j) δ (Set.Icc (0:ℝ) 1)) x=∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro j hj
    obtain ⟨hj,hxj⟩ := Finset.mem_filter.mp hj
    exact hno (Set.mem_iUnion₂.mpr ⟨j,hj,hxj⟩)
  obtain ⟨H,_,hH⟩ := subspace_extend_finrank
    (⊥ : Submodule ℝ (EuclideanSpace ℝ (Fin (n+1)))) k (by simp) hk
  apply hx
  refine ⟨H,hH,?_⟩
  rw [he]
  simp

/-- Literal lattice broad alternative, with ambient epsilon loss already
normalized. No separation, norm, mass comparison or Holder contract remains
beyond the named Zahl estimate. -/
theorem finite_lattice_broad_transfer (n k : ℕ) (Z : ZahlCapsuleEstimate (n+1) k)
    (R : ℝ) (hR : 0≤R) :
    ∀ ε : ℝ, 0<ε → ∃ c : ℝ, 0<c ∧ ∀ δ rho : ℝ, 0<δ → δ<1/2 → 0<rho →
    ∀ G : Finset ((Fin n → ℤ) × (Fin n → ℤ)), G.Nonempty →
    Set.InjOn Prod.snd (↑G : Set ((Fin n → ℤ) × (Fin n → ℤ))) →
    ∀ (z w : Fin n → ℝ) (i : Fin (n+1)),
    let b := fun j : (Fin n → ℤ) × (Fin n → ℤ) => latticePoint δ j.1+z
    let v := fun j : (Fin n → ℤ) × (Fin n → ℤ) => latticePoint δ j.2+w
    let U := δ^n*(G.card:ℝ)
    (∀ j∈G, ‖v j‖≤R) →
    U/4 ≤ (∫ x in finiteGridBroadRegion G b v (fun j => graphUnitDirection i (v j))
      (k-1) δ rho,gridMultiplicity G b v δ x) →
    c*δ^((n+1:ℝ)-zahlB (n+1) k+ε)*rho^((k:ℝ)-1)*
      U^(((n+1:ℝ)-zahlB (n+1) k)/n) ≤
      volume.real (occupiedGridRegion G b v δ (fun _ => Set.Icc (0:ℝ) 1)) := by
  have hklo := Z.1
  have hkhi := Z.2.1
  have hB : 0<zahlB (n+1) k := lt_trans (by norm_num) (zahlB_gt_one (by positivity)
    (by exact_mod_cast hklo) (by exact_mod_cast hkhi))
  intro ε hε
  obtain ⟨c,hc,hbound⟩ := finite_graph_broad_volume n k Z R (4*(n+2:ℝ)+1)
    hR le_rfl (ε/zahlB (n+1) k) (div_pos hε hB)
  refine ⟨c,hc,?_⟩
  intro δ rho hδ hδhalf hrho G hG hinj z w i
  dsimp only
  intro hv hmass
  let b := fun j : (Fin n → ℤ) × (Fin n → ℤ) => latticePoint δ j.1+z
  let v := fun j : (Fin n → ℤ) × (Fin n → ℤ) => latticePoint δ j.2+w
  have hsep : ∀ j∈G, ∀ l∈G, j≠l → δ≤dist (v j) (v l) := by
    intro j hj l hl hjl
    have hne : j.2≠l.2 := fun he => hjl (hinj hj hl he)
    simpa only [v,dist_add_right] using latticePoint_separated hδ hne
  have hb := hbound δ rho hδ hδhalf hrho G hG b v i hv hsep hmass
  rw [mul_div_cancel₀ ε hB.ne'] at hb
  exact hb.trans (measureReal_mono
    (finiteGridBroadRegion_subset_occupied G b v _ δ rho (by omega : k-1≤n+1))
    (occupiedGridRegion_finite_volume G b v hδ _
      (fun _ _ => measurableSet_Icc) (fun _ _ => Set.Subset.refl _)))

/-- The retained-mass loss has a nonnegative exponent in the actual Zahl range. -/
theorem broad_retained_mass_exponent_nonneg (n k : ℕ) (Z : ZahlCapsuleEstimate (n+1) k) :
    0≤((n+1:ℝ)-zahlB (n+1) k)/n := by
  apply div_nonneg _ (Nat.cast_nonneg _)
  apply sub_nonneg.mpr
  exact zahlB_le_n (by positivity) (by have := Z.1; exact_mod_cast (by omega : 1≤k))
    (by exact_mod_cast Z.2.1)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.bounded_graph_angular_separation
#print axioms KakeyaTwoScale.finite_graph_zahl_norm

#print axioms KakeyaTwoScale.broad_scalar_power
#print axioms KakeyaTwoScale.finite_graph_broad_volume

#print axioms KakeyaTwoScale.finite_lattice_broad_transfer
#print axioms KakeyaTwoScale.broad_retained_mass_exponent_nonneg
