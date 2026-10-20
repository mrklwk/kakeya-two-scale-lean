module
public import KakeyaTwoScale.DyadicPublishedAssembly

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- A lower dyadic radius within a factor two, with a strictly positive index. -/
theorem exists_lower_dyadicWeightCut {r : ℝ} (hr : 0<r) (hrhalf : r<1/2) :
    ∃ q : ℕ, 1≤q ∧ dyadicWeightCut q≤r ∧ r≤2*dyadicWeightCut q := by
  obtain ⟨m,hm,h'm⟩ := exists_nat_pow_near_of_lt_one hr (by linarith : r≤1)
    (by norm_num : (0:ℝ)<(2:ℝ)⁻¹) (by norm_num : (2:ℝ)⁻¹<1)
  refine ⟨m+1,by omega,?_,?_⟩
  · simpa only [dyadicWeightCut,inv_pow] using hm.le
  · have he : 2*dyadicWeightCut (m+1)=((2:ℝ)⁻¹)^m := by
      simp [dyadicWeightCut,pow_succ,inv_pow,mul_inv_rev]
    rwa [he]

/-- Moving the base does not change the actual flat-cylinder volume. -/
theorem flatCylinder_volume_translate {d : ℕ}
    (b u : EuclideanSpace ℝ (Fin d)) (L r : ℝ) :
    volume (flatCylinder b u L r)=volume (flatCylinder 0 u L r) := by
  have he : (fun x => b+x) ⁻¹' flatCylinder b u L r=flatCylinder 0 u L r := by
    ext x
    simp only [Set.mem_preimage,flatCylinder,Set.mem_ofPred_eq]
    constructor <;> rintro ⟨t,ht,hL,hi,hn⟩ <;> refine ⟨t,ht,hL,?_,?_⟩
    · simpa only [zero_add,add_sub_add_left_eq_sub] using hi
    · simpa only [zero_add,add_sub_add_left_eq_sub] using hn
    · simpa only [zero_add,add_sub_add_left_eq_sub] using hi
    · simpa only [zero_add,add_sub_add_left_eq_sub] using hn
  rw [←he,measure_preimage_add]

/-- Shrinking radius and moving the base can only decrease cylinder mass. -/
theorem flatCylinder_unit_mass_le {d : ℕ}
    (b b' u : EuclideanSpace ℝ (Fin d)) {s r : ℝ} (hsr : s≤r) :
    volume.real (flatCylinder b' u 1 s)≤volume.real (flatCylinder b u 1 r) := by
  simp only [Measure.real,flatCylinder_volume_translate]
  apply measureReal_mono _ (flatCylinder_unit_finite 0 u r)
  rintro x ⟨t,ht,hL,hi,hn⟩
  exact ⟨t,ht,hL,hi,hn.trans_le hsr⟩

/-- Inverse dilation followed by extending only the shortened longitudinal
interval gives a unit cylinder at the smaller radius. -/
theorem flatCylinder_inverse_dilate_unit {d : ℕ}
    (b u x : EuclideanSpace ℝ (Fin d)) (L r : ℝ) (hL : 1≤L)
    (hx : x∈flatCylinder b u 1 r) :
    L⁻¹ • x∈flatCylinder (L⁻¹ • b) u 1 (r/L) := by
  have hLp : 0<L := lt_of_lt_of_le zero_lt_one hL
  obtain ⟨t,ht0,ht1,hi,hn⟩ := hx
  have he : L⁻¹ • x-(L⁻¹ • b+(t/L) • u)=L⁻¹ • (x-(b+t • u)) := by
    simp only [div_eq_mul_inv]
    module
  refine ⟨t/L,div_pos ht0 hLp,(div_lt_one hLp).mpr (ht1.trans_le hL),?_,?_⟩
  · rw [he,inner_smul_right,hi,mul_zero]
  · rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hLp)]
    simpa only [div_eq_mul_inv,mul_comm] using mul_lt_mul_of_pos_left hn (inv_pos.mpr hLp)

/-- Genuine extended-real norm transport for the preceding cylinder inclusion. -/
theorem flatCylinder_multilinear_norm_dilate_le {d N : ℕ} (k : ℕ)
    (b u : Fin N → EuclideanSpace ℝ (Fin d)) (B L r : ℝ)
    (hu : ∀j, ‖u j‖=1) (hL : 1≤L) (p : ENNReal) :
    eLpNorm (multilinearKakeyaFunction k u (fun j=>flatCylinder (b j) (u j) 1 r) B) p volume ≤
      ENNReal.ofReal (L^((d:ℝ)/p.toReal))*
        eLpNorm (multilinearKakeyaFunction k u
          (fun j=>flatCylinder (L⁻¹ • b j) (u j) 1 (r/L)) B) p volume := by
  let T := fun j=>flatCylinder (b j) (u j) 1 r
  let S := fun j=>flatCylinder (L⁻¹ • b j) (u j) 1 (r/L)
  let F := multilinearKakeyaFunction k u S B
  have hF : Measurable F := measurable_multilinearKakeyaFunction k u S B
    (fun j=>(isOpen_flatCylinder _ _ _ _ (hu j)).measurableSet)
  have hh : eLpNorm (multilinearKakeyaFunction k u T B) p volume≤
      eLpNorm (fun x=>F (L⁻¹ • x)) p volume := by
    apply eLpNorm_mono_ae (measurable_multilinearKakeyaFunction k u T B
      (fun j=>(isOpen_flatCylinder _ _ _ _ (hu j)).measurableSet)).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro x
    simp only [F,Real.norm_eq_abs,abs_of_nonneg (multilinearKakeyaFunction_nonneg k u T B x),
      abs_of_nonneg (multilinearKakeyaFunction_nonneg k u S B (L⁻¹ • x))]
    apply multilinearKakeyaFunction_le_of_membership
    intro j hj
    exact flatCylinder_inverse_dilate_unit (b j) (u j) x L r hL hj
  exact hh.trans_eq (eLpNorm_inverse_dilation_rpow F hF p (lt_of_lt_of_le zero_lt_one hL))

/-- A uniform dyadic unit-cylinder norm bound implies its all-radius counterpart.
The original family, ordered tuple function and actual volume sum are preserved. -/
theorem all_radius_norm_of_dyadic (d k : ℕ) (hd : 1<d) (B ε : ℝ)
    (hB : 1<B) (hε : 0<ε) (Cd : ℝ) (hCd : 0<Cd)
    (H : ∀ q : ℕ, 1≤q →
      ∀ (N : ℕ) (b u : Fin N → EuclideanSpace ℝ (Fin d)),
      (∀j, ‖u j‖=1) →
      (∀i j, i≠j → dyadicWeightCut q≤Real.arccos |inner ℝ (u i) (u j)|) →
      eLpNorm (multilinearKakeyaFunction k u
        (fun j=>flatCylinder (b j) (u j) 1 (dyadicWeightCut q)) B)
        (ENNReal.ofReal (B/(B-1))) volume ≤
      ENNReal.ofReal (Cd*(dyadicWeightCut q)^(1-(d:ℝ)/B-ε)*
        (∑j,volume.real (flatCylinder (b j) (u j) 1 (dyadicWeightCut q)))^
          ((d:ℝ)*(B-1)/(((d:ℝ)-1)*B)))) :
    ∀ r : ℝ, 0<r → r<1/2 →
      ∀ (N : ℕ) (b u : Fin N → EuclideanSpace ℝ (Fin d)),
      (∀j, ‖u j‖=1) →
      (∀i j, i≠j → r≤Real.arccos |inner ℝ (u i) (u j)|) →
      eLpNorm (multilinearKakeyaFunction k u
        (fun j=>flatCylinder (b j) (u j) 1 r) B)
        (ENNReal.ofReal (B/(B-1))) volume ≤
      ENNReal.ofReal ((2:ℝ)^((d:ℝ)-1+ε)*Cd*r^(1-(d:ℝ)/B-ε)*
        (∑j,volume.real (flatCylinder (b j) (u j) 1 r))^
          ((d:ℝ)*(B-1)/(((d:ℝ)-1)*B))) := by
  intro r hr hrhalf N b u hu hsep
  obtain ⟨q,hq,hsr,hrs⟩ := exists_lower_dyadicWeightCut hr hrhalf
  let s := dyadicWeightCut q
  have hs : 0<s := by dsimp [s,dyadicWeightCut]; positivity
  let L := r/s
  have hL : 1≤L := (one_le_div hs).mpr hsr
  have hLtwo : L≤2 := (div_le_iff₀ hs).mpr (by simpa [mul_comm] using hrs)
  have hLp : 0<L := lt_of_lt_of_le zero_lt_one hL
  have heqr : r/L=s := by dsimp [L]; field_simp
  let p : ENNReal := ENNReal.ofReal (B/(B-1))
  let α : ℝ := (d:ℝ)*(B-1)/(((d:ℝ)-1)*B)
  let e : ℝ := 1-(d:ℝ)/B-ε
  let V := ∑j,volume.real (flatCylinder (b j) (u j) 1 r)
  have hdR : (1:ℝ)<d := by exact_mod_cast hd
  have hα : 0≤α := by dsimp [α]; positivity
  have hV : 0≤V := Finset.sum_nonneg (fun _ _=>measureReal_nonneg)
  have hp : p.toReal=B/(B-1) := ENNReal.toReal_ofReal (by positivity)
  have hmass : (∑j,volume.real (flatCylinder (L⁻¹ • b j) (u j) 1 s))≤V :=
    Finset.sum_le_sum (fun j _=>flatCylinder_unit_mass_le (b j) (L⁻¹ • b j) (u j) hsr)
  have hdil := flatCylinder_multilinear_norm_dilate_le k b u B L r hu hL p
  rw [heqr] at hdil
  have hz := H q hq N (fun j=>L⁻¹ • b j) u hu (fun i j hij=>hsr.trans (hsep i j hij))
  have hz' : eLpNorm (multilinearKakeyaFunction k u
      (fun j=>flatCylinder (L⁻¹ • b j) (u j) 1 s) B) p volume ≤
      ENNReal.ofReal (Cd*s^e*V^α) := by
    apply hz.trans
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Finset.sum_nonneg (fun _ _=>measureReal_nonneg)) hmass hα) (by positivity)
  have hfactor : L^((d:ℝ)/p.toReal)*s^e=L^((d:ℝ)-1+ε)*r^e := by
    rw [←heqr,show r/L=r*L⁻¹ by ring,Real.mul_rpow hr.le (inv_nonneg.mpr hLp.le),
      Real.inv_rpow hLp.le,←Real.rpow_neg hLp.le]
    calc
      _ = (L^((d:ℝ)/p.toReal)*L^(-e))*r^e := by ring
      _ = _ := by
        rw [←Real.rpow_add hLp]
        congr 2
        rw [hp]
        dsimp [e]
        field_simp
        ring
  have hfacBound : L^((d:ℝ)-1+ε)≤(2:ℝ)^((d:ℝ)-1+ε) :=
    Real.rpow_le_rpow hLp.le hLtwo (by linarith)
  apply hdil.trans
  have hm := mul_le_mul (le_refl (ENNReal.ofReal (L^((d:ℝ)/p.toReal)))) hz' zero_le zero_le
  rw [←ENNReal.ofReal_mul (Real.rpow_nonneg hLp.le _)] at hm
  apply hm.trans
  apply ENNReal.ofReal_le_ofReal
  calc
    L^((d:ℝ)/p.toReal)*(Cd*s^e*V^α) = (L^((d:ℝ)/p.toReal)*s^e)*Cd*V^α := by ring
    _ = L^((d:ℝ)-1+ε)*Cd*r^e*V^α := by rw [hfactor]; ring
    _ ≤ (2:ℝ)^((d:ℝ)-1+ε)*Cd*r^e*V^α := by gcongr

/-- The explicit uniform non-tiny band hypothesis supplies the published
all-radius cylinder contract after the proved dyadic and geometric adapters. -/
theorem published_zahl_of_positive_bands (n k : ℕ) (hk : 2≤k) (hkn : k≤n+1)
    (H : ∀ ε : ℝ, 0<ε → DyadicPositiveBandEstimate n k (zahlB (n+1) k) (ε/2)) :
    PublishedZahlCylinderEstimate (n+1) k := by
  refine ⟨hk,hkn,?_⟩
  intro ε hε
  obtain ⟨Cd,hCd,hdyadic⟩ := dyadic_zahl_norm_of_positive_bands n k hk hkn ε hε (H ε hε)
  refine ⟨(2:ℝ)^((n+1:ℝ)-1+ε)*Cd,by positivity,?_⟩
  have hd : 1<n+1 := by omega
  have hB : 1<zahlB (n+1) k := zahlB_gt_one (by positivity)
    (by exact_mod_cast hk) (by exact_mod_cast hkn)
  simpa only [Nat.cast_add,Nat.cast_one] using
    all_radius_norm_of_dyadic (n+1) k hd (zahlB (n+1) k) ε hB hε Cd hCd
      (by simpa only [Nat.cast_add,Nat.cast_one] using hdyadic)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.exists_lower_dyadicWeightCut
#print axioms KakeyaTwoScale.flatCylinder_volume_translate
#print axioms KakeyaTwoScale.flatCylinder_unit_mass_le
#print axioms KakeyaTwoScale.flatCylinder_inverse_dilate_unit
#print axioms KakeyaTwoScale.flatCylinder_multilinear_norm_dilate_le
#print axioms KakeyaTwoScale.all_radius_norm_of_dyadic
#print axioms KakeyaTwoScale.published_zahl_of_positive_bands
