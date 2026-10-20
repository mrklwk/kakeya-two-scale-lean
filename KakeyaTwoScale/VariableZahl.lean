module
public import KakeyaTwoScale.VariableMultilinearScale
public import KakeyaTwoScale.MultilinearMass

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
namespace KakeyaTwoScale
open Classical

/-- Smaller-radius unit capsules at arbitrary translated basepoints have
uniformly comparable mass. The bound depends only on dimension. -/
theorem normalized_unit_capsule_mass_le (n : ℕ) :
    ∃ K : ℝ, 0<K ∧ ∀ δ r : ℝ, 0<δ → δ≤1/2 → r≤δ →
      ∀ b b' u : EuclideanSpace ℝ (Fin (n+1)), ‖u‖=1 →
      volume.real (euclideanTube b' u r)≤K*volume.real (euclideanTube b u δ) := by
  obtain ⟨c,hc,hvol⟩ := euclideanTube_volume_lower_unrestricted n
  let A : ℝ := 3*(2*(n+3:ℝ))^n
  refine ⟨A/c,by dsimp [A]; positivity,?_⟩
  intro δ r hδ hδhalf hr b b' u hu
  have hs : euclideanTube b' u r⊆euclideanTube b' u δ := by
    rintro x ⟨t,ht,hx⟩
    exact ⟨t,ht,hx.trans_le hr⟩
  have hv := (measureReal_mono hs (euclideanTube_finite b' u δ)).trans
    (euclideanTube_volume_upper b' u hδ hδhalf hu)
  have hh := mul_le_mul_of_nonneg_left (hvol δ hδ b u hu)
    (show 0≤A/c by dsimp [A]; positivity)
  have he : A/c*(c*δ^n)=A*δ^n := by field_simp
  rw [he] at hh
  exact hv.trans hh

def zahlMassExponent (d k : ℝ) : ℝ :=
  d*(zahlB d k-1)/((d-1)*zahlB d k)

/-- Conditional only on the existing sole Zahl estimate. This proves all
variable-length, scale, radius, separation and mass adaptations explicitly. -/
theorem variable_capsule_zahl_estimate (n k : ℕ)
    (Z : ZahlCapsuleEstimate (n+1) k) (C L : ℝ)
    (hC : 0<C) (hCL : C≤L) (hLone : 1≤L) :
    ∀ ε : ℝ, 0<ε → ∃ K : ℝ, 0<K ∧ ∀ δ : ℝ, 0<δ → δ<1/2 →
      ∀ (N : ℕ) (b u : Fin N → EuclideanSpace ℝ (Fin (n+1))) (ell : Fin N → ℝ),
      (∀ j, ‖u j‖=1) → (∀ j, 0≤ell j ∧ ell j≤L) →
      (∀ i j, i≠j → δ≤Real.arccos |inner ℝ (u i) (u j)|) →
      eLpNorm (multilinearKakeyaFunction k u
        (fun j => euclideanTube (b j) (ell j • u j) (C*δ)) (zahlB (n+1) k))
        (ENNReal.ofReal (zahlB (n+1) k/(zahlB (n+1) k-1))) volume ≤
      ENNReal.ofReal (K*δ^(1-(n+1:ℝ)/zahlB (n+1) k-ε)*
        (∑ j,volume.real (euclideanTube (b j) (u j) δ))^(zahlMassExponent (n+1) k)) := by
  obtain ⟨hklo,hkhi,hZ⟩ := Z
  have hL : 0<L := by linarith
  have hn : (0:ℝ)<n+1 := by positivity
  have hklo' : (2:ℝ)≤k := by exact_mod_cast hklo
  have hkhi' : (k:ℝ)≤n+1 := by exact_mod_cast hkhi
  have hB : 1<zahlB (n+1) k := zahlB_gt_one hn hklo' hkhi'
  have hn1 : (1:ℝ)<n+1 := by have : 2≤n+1 := hklo.trans hkhi; exact_mod_cast this
  have halpha : 0≤zahlMassExponent (n+1) k := by
    unfold zahlMassExponent
    apply div_nonneg <;> positivity
  obtain ⟨K0,hK0,hmass⟩ := normalized_unit_capsule_mass_le n
  intro ε hε
  obtain ⟨CZ,hCZ,hCZbound⟩ := hZ ε hε
  let B := zahlB (n+1) k
  let p := ENNReal.ofReal (B/(B-1))
  let α := zahlMassExponent (n+1) k
  let a : ℝ := 1-(n+1:ℝ)/B-ε
  let D : ℝ := L^((n+1:ℝ)/p.toReal)
  let K : ℝ := D*CZ*(C/L)^a*K0^α
  refine ⟨K,by dsimp [K,D]; positivity,?_⟩
  intro δ hδ hδhalf N b u ell hu hell hsep
  have hscale : C*δ/L≤δ := (div_le_iff₀ hL).mpr (by nlinarith)
  have hr : 0<C*δ/L := by positivity
  have hsum0 : 0≤∑ j,volume.real (euclideanTube (b j) (u j) δ) :=
    Finset.sum_nonneg (fun j _ => measureReal_nonneg)
  have hsum : (∑ j,volume.real (euclideanTube (L⁻¹ • b j) (u j) (C*δ/L)))≤
      K0*∑ j,volume.real (euclideanTube (b j) (u j) δ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun j _ => hmass δ (C*δ/L) hδ hδhalf.le hscale (b j) (L⁻¹ • b j) (u j) (hu j))
  have hz := hCZbound (C*δ/L) hr (hscale.trans_lt hδhalf) N
    (fun j => L⁻¹ • b j) u hu (fun i j hij => hscale.trans (hsep i j hij))
  simp only [Nat.cast_add, Nat.cast_one] at hz
  have hdil := variable_capsule_multilinear_norm_dilate_le k b u ell B L (C*δ) hL hell p
  apply hdil.trans
  have hα : 0≤α := halpha
  have hpw := Real.rpow_le_rpow (Finset.sum_nonneg (fun j _ => measureReal_nonneg)) hsum hα
  have hcoeff : 0≤CZ*(C*δ/L)^a := by positivity
  have hz' : eLpNorm (multilinearKakeyaFunction k u
      (fun j => euclideanTube (L⁻¹ • b j) (u j) (C*δ/L)) B) p volume ≤
      ENNReal.ofReal (CZ*(C*δ/L)^a*(K0*∑ j,volume.real (euclideanTube (b j) (u j) δ))^α) := by
    apply hz.trans
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_left hpw hcoeff
  have hmul := mul_le_mul (le_refl (ENNReal.ofReal D)) hz' zero_le zero_le
  have he : D*(CZ*(C*δ/L)^a*(K0*∑ j,volume.real (euclideanTube (b j) (u j) δ))^α)=
      K*δ^a*(∑ j,volume.real (euclideanTube (b j) (u j) δ))^α := by
    rw [show C*δ/L=(C/L)*δ by ring,Real.mul_rpow (div_nonneg hC.le hL.le) hδ.le,
      Real.mul_rpow hK0.le hsum0]
    dsimp [K]
    ring
  rw [← ENNReal.ofReal_mul (by dsimp [D]; positivity),he] at hmul
  simpa only [D, Nat.cast_add, Nat.cast_one] using hmul

end KakeyaTwoScale
#print axioms KakeyaTwoScale.normalized_unit_capsule_mass_le
#print axioms KakeyaTwoScale.variable_capsule_zahl_estimate
