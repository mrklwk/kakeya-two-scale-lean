module
public import KakeyaTwoScale.MultilinearMass

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
namespace KakeyaTwoScale
open Classical

/-- Published direction-separated multilinear estimate for open flat cylinders
of length one. This is an explicit analytic premise, not an asserted theorem.
The tuple/root/wedge, norm, radius and total-volume exponents are those of
Zahl, arXiv:1908.05314v4, Theorem 1.3. -/
def PublishedZahlCylinderEstimate (n k : ℕ) : Prop :=
  2 ≤ k ∧ k ≤ n ∧ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r → r < 1/2 →
    ∀ (N : ℕ) (b u : Fin N → EuclideanSpace ℝ (Fin n)),
    (∀ j, ‖u j‖=1) →
    (∀ i j, i ≠ j → r ≤ Real.arccos |inner ℝ (u i) (u j)|) →
    eLpNorm (multilinearKakeyaFunction k u (fun j => flatCylinder (b j) (u j) 1 r) (zahlB n k))
      (ENNReal.ofReal (zahlB n k/(zahlB n k-1))) volume ≤
      ENNReal.ofReal (C*r^(1-(n:ℝ)/zahlB n k-ε)*
        (∑ j, volume.real (flatCylinder (b j) (u j) 1 r))^
          ((n:ℝ)*(zahlB n k-1)/(((n:ℝ)-1)*zahlB n k)))


/-- Fixed normalization of the published flat-cylinder estimate includes both
endpoint caps. The multiplicative loss is independent of radius and family. -/
theorem published_zahl_implies_capsule_succ (n k : ℕ)
    (Z : PublishedZahlCylinderEstimate (n+1) k) : ZahlCapsuleEstimate (n+1) k := by
  obtain ⟨hklo,hkhi,hZ⟩ := Z
  have hn : (0:ℝ)<n+1 := by positivity
  have hn1 : (1:ℝ)<n+1 := by have : 2≤n+1 := hklo.trans hkhi; exact_mod_cast this
  have hB : 1<zahlB (n+1) k := zahlB_gt_one hn (by exact_mod_cast hklo) (by exact_mod_cast hkhi)
  obtain ⟨Km,hKm,hmass⟩ := normalized_cylinder_mass_sum_le n
  refine ⟨hklo,hkhi,?_⟩
  intro ε hε
  obtain ⟨CZ,hCZ,hestimate⟩ := hZ ε hε
  let B := zahlB (n+1) k
  let p := ENNReal.ofReal (B/(B-1))
  let α := (n+1:ℝ)*(B-1)/(((n+1:ℝ)-1)*B)
  let e : ℝ := 1-(n+1:ℝ)/B-ε
  let D : ℝ := (5:ℝ)^((n+1:ℝ)/p.toReal)
  let C : ℝ := (5:ℝ)^((n+1:ℝ)-1+ε)*CZ*Km^α
  have hα : 0≤α := by dsimp [α,B]; apply div_nonneg <;> positivity
  have hp : p.toReal=B/(B-1) := ENNReal.toReal_ofReal (by dsimp [B]; positivity)
  have hfactor : D*(1/5:ℝ)^e=(5:ℝ)^((n+1:ℝ)-1+ε) := by
    dsimp [D]
    rw [one_div,Real.inv_rpow (by norm_num),← Real.rpow_neg (by norm_num),← Real.rpow_add (by norm_num)]
    congr 1
    rw [hp]
    dsimp [e]
    have hB0 : B≠0 := (lt_trans (by norm_num) hB).ne'
    have hB1 : B-1≠0 := (sub_pos.mpr hB).ne'
    field_simp
    ring
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro r hr hrhalf N b u hu hsep
  simp only [Nat.cast_add,Nat.cast_one]
  have hsmall : r/5≤r := by linarith
  have hsum0 : 0≤∑ j,volume.real (euclideanTube (b j) (u j) r) :=
    Finset.sum_nonneg (fun j _ => measureReal_nonneg)
  have hsum := hmass 1 r (by norm_num) hr hrhalf.le Finset.univ b u (fun j _ => hu j)
  norm_num only [one_mul,show (2:ℝ)*1+3=5 by norm_num] at hsum
  have hz := hestimate (r/5) (by positivity) (hsmall.trans_lt hrhalf) N
    (fun j => (5:ℝ)⁻¹ • (b j-r • u j)) u hu (fun i j hij => hsmall.trans (hsep i j hij))
  simp only [Nat.cast_add,Nat.cast_one] at hz
  have hdil := capsule_multilinear_norm_dilate_le k b u B 1 r p hu (by norm_num) (by linarith : r≤1)
  norm_num only [one_mul,show (2:ℝ)*1+3=5 by norm_num] at hdil
  simp only [Nat.cast_add,Nat.cast_one,one_div] at hdil hsum
  apply hdil.trans
  have hpw := Real.rpow_le_rpow (Finset.sum_nonneg (fun j _ => measureReal_nonneg)) hsum hα
  have hz' : eLpNorm (multilinearKakeyaFunction k u
      (fun j => flatCylinder ((5:ℝ)⁻¹ • (b j-r • u j)) (u j) 1 (r/5)) B) p volume ≤
      ENNReal.ofReal (CZ*(r/5)^e*(Km*∑ j,volume.real (euclideanTube (b j) (u j) r))^α) := by
    apply hz.trans
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_left hpw (by positivity)
  have hmul := mul_le_mul (le_refl (ENNReal.ofReal D)) hz' zero_le zero_le
  have he : D*(CZ*(r/5)^e*(Km*∑ j,volume.real (euclideanTube (b j) (u j) r))^α)=
      C*r^e*(∑ j,volume.real (euclideanTube (b j) (u j) r))^α := by
    rw [show r/5=(1/5:ℝ)*r by ring,Real.mul_rpow (by norm_num) hr.le,
      Real.mul_rpow hKm.le hsum0]
    calc
      _ = (D*(1/5:ℝ)^e)*CZ*Km^α*r^e*(∑ j,volume.real (euclideanTube (b j) (u j) r))^α := by ring
      _ = _ := by rw [hfactor]
  rw [← ENNReal.ofReal_mul (by dsimp [D]; positivity),he] at hmul
  simpa only [D,α,Nat.cast_add,Nat.cast_one] using hmul

/-- The published flat-cylinder contract suffices for the existing capsule
contract in every permitted ambient dimension. -/
theorem published_zahl_implies_capsule (n k : ℕ)
    (Z : PublishedZahlCylinderEstimate n k) : ZahlCapsuleEstimate n k := by
  cases n with
  | zero => have := Z.1.trans Z.2.1; omega
  | succ n => exact published_zahl_implies_capsule_succ n k Z

end KakeyaTwoScale
#print axioms KakeyaTwoScale.published_zahl_implies_capsule_succ
#print axioms KakeyaTwoScale.published_zahl_implies_capsule
