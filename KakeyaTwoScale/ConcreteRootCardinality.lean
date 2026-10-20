module
public import KakeyaTwoScale.ConcreteRootState

@[expose] public section

open Set Metric
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- Crude root-scale direction count; half-width chord separation suffices. -/
theorem root_direction_card_bound {n N q : ℕ}
    (u : Fin N → EuclideanSpace ℝ (Fin n)) (hu : ∀ o, ‖u o‖=1)
    (hsep : ∀ o p, o≠p → ((2:ℝ)^q)⁻¹/2 ≤ dist (u o) (u p)) :
    (N:ℝ) ≤ (2:ℝ)^((q+3)*n) := by
  have hδ : 0 < ((2:ℝ)^q)⁻¹ := by positivity
  have hδ1 : ((2:ℝ)^q)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hp := sharp_ball_packing Finset.univ u 0 (((2:ℝ)^q)⁻¹/2) 1
    (by positivity) (by norm_num) (fun o _ => by simp [hu]) (fun o _ p _ => hsep o p)
  have hd : Module.finrank ℝ (EuclideanSpace ℝ (Fin n))=n := by simp
  rw [hd] at hp
  simp only [Finset.card_univ, Fintype.card_fin] at hp
  have hb : (3*1+((2:ℝ)^q)⁻¹/2)^n ≤ (4:ℝ)^n := by gcongr; linarith
  have hh := hp.trans hb
  have hd' : (((2:ℝ)^q)⁻¹/2)^n = ((2:ℝ)^(q+1))⁻¹^n := by
    congr 1
    simp [pow_succ, mul_inv_rev, div_eq_mul_inv, mul_comm]
  rw [hd', inv_pow, ← div_eq_mul_inv] at hh
  have hfinal := (div_le_iff₀ (by positivity : (0:ℝ)<((2:ℝ)^(q+1))^n)).mp hh
  calc
    (N:ℝ) ≤ (4:ℝ)^n * ((2:ℝ)^(q+1))^n := hfinal
    _ = (2:ℝ)^((q+3)*n) := by
      rw [← mul_pow, show (4:ℝ)*2^(q+1)=2^(q+3) by ring_nf, ← pow_mul]

/-- Local fine-grid packing is uniform over the coarse cell's translation. -/
theorem root_cube_card_bound {n q : ℕ} (cubes : Finset (Fin n → ℤ))
    (a : Fin n → ℤ) (ha : ∀ z ∈ cubes, rootCoarseOwner ((2:ℝ)^q)⁻¹ z=a) :
    (cubes.card:ℝ) ≤ (2:ℝ)^((q+2)*n) := by
  have hδ : 0 < ((2:ℝ)^q)⁻¹ := by positivity
  have hδ1 : ((2:ℝ)^q)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hb : ∀ z ∈ cubes, dist (latticePoint ((2:ℝ)^q)⁻¹ z) (latticePoint 1 a) ≤ 1 := by
    intro z hz
    have h := dist_gridRound_le (by norm_num : (0:ℝ)<1) (latticePoint ((2:ℝ)^q)⁻¹ z)
    change dist _ (latticePoint 1 (rootCoarseOwner ((2:ℝ)^q)⁻¹ z)) ≤ 1 at h
    rwa [ha z hz] at h
  have hp := sharp_ball_packing cubes (latticePoint ((2:ℝ)^q)⁻¹) (latticePoint 1 a)
    ((2:ℝ)^q)⁻¹ 1 hδ (by norm_num) hb
    (fun z _ w _ hne => latticePoint_separated hδ hne)
  have hd : Module.finrank ℝ (Fin n → ℝ)=n := by simp
  rw [hd] at hp
  have hh := hp.trans (show (3*1+((2:ℝ)^q)⁻¹)^n ≤ (4:ℝ)^n by gcongr; linarith)
  rw [inv_pow, ← div_eq_mul_inv] at hh
  have hfinal := (div_le_iff₀ (by positivity : (0:ℝ)<((2:ℝ)^q)^n)).mp hh
  calc
    (cubes.card:ℝ) ≤ (4:ℝ)^n * ((2:ℝ)^q)^n := hfinal
    _ = (2:ℝ)^((q+2)*n) := by
      rw [← mul_pow, show (4:ℝ)*2^q=2^(q+2) by ring_nf, ← pow_mul]

/-- The required initial tuple calendar is proved from separated original
unit directions and literal coarse-cell tuples, not assumed. -/
theorem coarseRootTuples_card_bound {n k N q : ℕ} (hq : 1 ≤ q)
    (Y : Finset (RootTuple n k (Fin N))) (a : Fin n → ℤ)
    (u : Fin N → EuclideanSpace ℝ (Fin n)) (hu : ∀ o, ‖u o‖=1)
    (hsep : ∀ o p, o≠p → ((2:ℝ)^q)⁻¹/2 ≤ dist (u o) (u p)) :
    ((coarseRootTuples Y ((2:ℝ)^q)⁻¹ a).card:ℝ) ≤
      (2:ℝ)^(((4*k+3)*n)*q) := by
  classical
  let Z := coarseRootTuples Y ((2:ℝ)^q)⁻¹ a
  have hc := root_cube_card_bound (Z.image Prod.fst) a (by
    intro z hz
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hz
    exact (Finset.mem_filter.mp hy).2)
  have hN := root_direction_card_bound u hu hsep
  have hsub : Z ⊆ (Z.image Prod.fst) ×ˢ (Finset.univ : Finset (Fin k → Fin N)) := by
    intro y hy
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hy, Finset.mem_univ _⟩
  have hcard : (Z.card:ℝ) ≤ (Z.image Prod.fst).card * (N:ℝ)^k := by
    exact_mod_cast (by simpa using Finset.card_le_card hsub : Z.card ≤ (Z.image Prod.fst).card*N^k)
  calc
    (Z.card:ℝ) ≤ (Z.image Prod.fst).card * (N:ℝ)^k := hcard
    _ ≤ (2:ℝ)^((q+2)*n) * ((2:ℝ)^((q+3)*n))^k := by gcongr
    _ = (2:ℝ)^(((q+2)*n)+((q+3)*n)*k) := by rw [← pow_mul, ← pow_add]
    _ ≤ (2:ℝ)^(((4*k+3)*n)*q) := by
      apply pow_le_pow_right₀ (by norm_num)
      have hk := Nat.mul_le_mul_left (3*k+2) hq
      nlinarith

end KakeyaTwoScale
#print axioms KakeyaTwoScale.root_direction_card_bound
#print axioms KakeyaTwoScale.root_cube_card_bound
#print axioms KakeyaTwoScale.coarseRootTuples_card_bound
