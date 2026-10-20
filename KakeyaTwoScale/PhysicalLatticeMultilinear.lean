module
public import KakeyaTwoScale.RetainedLatticeMultilinear
public import KakeyaTwoScale.FlatCylinderMultilinear
public import KakeyaTwoScale.NestedGrid

@[expose] public section

open Set Metric
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
open Classical

/-- Half-open physical cells normalize into the closed visibility lattice.
The half-unit translation is essential: both lattices then have the same
integer label without rounding or a dimension-dependent overlap loss. -/
theorem gridCell_normalize_visibility {d : ℕ} (δ : ℝ) (hδ : 0<δ)
    (z : Fin d → ℤ) (x : Fin d → ℝ) (hx : x∈gridCell δ z) :
    (fun i => δ⁻¹*x i-1/2)∈visibilityCube (fun i => (z i:ℝ)) := by
  change dist (fun i => δ⁻¹*x i-1/2) (fun i => (z i:ℝ))≤1/2
  rw [dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1/2)).mpr
  intro i
  change |δ⁻¹*x i-1/2-(z i:ℝ)|≤1/2
  apply abs_le.mpr
  have hlo : (z i:ℝ)≤x i/δ := (le_div_iff₀ hδ).mpr (by simpa [mul_comm] using (hx i).1)
  have hhi : x i/δ<(z i:ℝ)+1 := (div_lt_iff₀ hδ).mpr (by simpa [mul_comm] using (hx i).2)
  rw [div_eq_mul_inv] at hlo hhi
  constructor <;> nlinarith

/-- Literal physical cube/cylinder incidence transports to unit infinite-tube
incidence, with the same direction and the same integer cube label. -/
theorem grid_cylinder_normalized_incidence {d : ℕ} (δ : ℝ) (hδ : 0<δ)
    (z : Fin d → ℤ) (b u : EuclideanSpace ℝ (Fin d)) (ell : ℝ)
    (hi : ((WithLp.ofLp ⁻¹' gridCell δ z) ∩ flatCylinder b u ell δ).Nonempty) :
    (visibilityCube (fun i => (z i:ℝ)) ∩
      infiniteLineTube (fun i => δ⁻¹*b i-1/2) (WithLp.ofLp u) 1).Nonempty := by
  obtain ⟨x,hx,⟨t,_,_,_,ht⟩⟩ := hi
  refine ⟨(fun i => δ⁻¹*x i-1/2),gridCell_normalize_visibility δ hδ z _ hx,t/δ,?_⟩
  have he : (WithLp.toLp 2 ((fun i => δ⁻¹*x i-1/2)-
      ((fun i => δ⁻¹*b i-1/2)+(t/δ) • WithLp.ofLp u)) : EuclideanSpace ℝ (Fin d))=
      δ⁻¹ • (x-(b+t • u)) := by
    ext i
    simp only [Pi.sub_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    change δ⁻¹*x i-1/2-(δ⁻¹*b i-1/2+(t/δ)*u i)=δ⁻¹*(x i-(b i+t*u i))
    ring
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hδ)]
  apply (inv_mul_le_iff₀ hδ).mpr
  simpa only [mul_one] using ht.le

/-- Actual physical retained tuples in arbitrary finite cube banks. This is
the scale-free terminal mass input, with no Cartesian saturation assumption.
Empty fibers and zero wedge thresholds are included. -/
theorem physical_retained_lattice_multilinear (n k : ℕ) (hk : 2≤k) (hkn : k≤n+1) :
    ∃ C : ℝ, 0≤C ∧ ∀ δ : ℝ, 0<δ → ∀ (J : ℕ) (z : Fin J → Fin (n+1) → ℤ),
      Function.Injective z → ∀ (L : Fin k → ℕ)
      (b u : (j : Fin k) → Fin (L j) → EuclideanSpace ℝ (Fin (n+1)))
      (ell : (j : Fin k) → Fin (L j) → ℝ)
      (R : Fin J → Finset ((j : Fin k) → Fin (L j))) (θ : ℝ),
      (∀j t, ‖u j t‖=1) → 0≤θ →
      (∀q, ∀f∈R q, θ≤tupleWedgeVolume (fun j => u j (f j))) →
      (∀q, ∀f∈R q, ∀j,
        ((WithLp.ofLp ⁻¹' gridCell δ (z q)) ∩
          flatCylinder (b j (f j)) (u j (f j)) (ell j (f j)) δ).Nonempty) →
      θ^(1/((k-1:ℕ):ℝ))*(∑q, ((R q).card:ℝ)^(1/((k-1:ℕ):ℝ))) ≤
        C*(∏j, (L j:ℝ))^(1/((k-1:ℕ):ℝ)) := by
  obtain ⟨C,hC,hmain⟩ := retained_lattice_multilinear n k hk hkn
  refine ⟨C,hC,?_⟩
  intro δ hδ J z hz L b u ell R θ hu hθ hw hi
  exact hmain J z hz L (fun j t i => δ⁻¹*b j t i-1/2) u R θ hu hθ hw
    (fun q f hf j => grid_cylinder_normalized_incidence δ hδ (z q) _ _ _ (hi q f hf j))

end KakeyaTwoScale
#print axioms KakeyaTwoScale.gridCell_normalize_visibility
#print axioms KakeyaTwoScale.grid_cylinder_normalized_incidence
#print axioms KakeyaTwoScale.physical_retained_lattice_multilinear
