module
public import KakeyaTwoScale.IterationSizeCases
public import KakeyaTwoScale.SlopeTree

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical

/-- W≥N² discharges BOTH ceiling-size conditions at every level. -/
theorem large_family_rounding_inputs (N V : ℝ) (M k : ℕ)
    (hN : 1 ≤ N) (hV : N^2 ≤ V) (hM : 2 ≤ M) (hk : k ≤ M) :
    1 ≤ iterationEpsilon N M k*V ∧ 1 ≤ V*N^(iterationRho M k-2) := by
  have hn : 0 < N := by linarith
  have hm : (0:ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hm2 : (2:ℝ) ≤ M := by exact_mod_cast hM
  have hv : 0 ≤ V := le_trans (sq_nonneg N) hV
  have hb := (iterationLossExponent_bounds M k (by omega) hk).1
  have hdiv : 2/(M:ℝ) ≤ 1 := (div_le_one hm).mpr hm2
  simp only [neg_div] at hb
  have hl : (-1:ℝ) ≤ iterationLossExponent M k := by linarith
  have heps := Real.rpow_le_rpow_of_exponent_le hN hl
  have hrho := iterationRho_nonneg M k (by omega) hk
  have hpow := Real.rpow_le_rpow_of_exponent_le hN (by linarith : (-2:ℝ) ≤ iterationRho M k-2)
  constructor
  · calc
      1 ≤ N := hN
      _ = N^(-1:ℝ)*N^2 := by rw [← Real.rpow_two,← Real.rpow_add hn]; norm_num
      _ ≤ N^(-1:ℝ)*V := mul_le_mul_of_nonneg_left hV (Real.rpow_nonneg hn.le _)
      _ ≤ iterationEpsilon N M k*V := mul_le_mul_of_nonneg_right heps hv
  · calc
      1 = N^2*N^(-2:ℝ) := by rw [← Real.rpow_two,← Real.rpow_add hn]; norm_num
      _ ≤ V*N^(-2:ℝ) := mul_le_mul_of_nonneg_right hV (Real.rpow_nonneg hn.le _)
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow hv

/-- The actual rounded root thresholds satisfy the required endpoint. -/
theorem rounded_root_bounds (N V M : ℕ) (hN : 2 ≤ N) (hV : N^2 ≤ V) (hM : 2 ≤ M) :
    iterationMassThreshold N V M 0 ≤ V ∧ V < iterationFiberThreshold N V M 0 := by
  have hn : (1:ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  have hm : (0:ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hv : (0:ℝ) < V := by exact_mod_cast (by nlinarith : 0 < V)
  have hExp : iterationLossExponent M 0 ≤ 0 := by
    simp only [iterationLossExponent,Nat.cast_zero,zero_div,sub_zero,neg_div]
    exact neg_nonpos.mpr (by positivity)
  have heps : iterationEpsilon N M 0 ≤ 1 := by
    simpa [iterationEpsilon] using Real.rpow_le_rpow_of_exponent_le hn.le hExp
  constructor
  · apply Nat.ceil_le.mpr
    simpa using mul_le_mul_of_nonneg_right heps hv.le
  · have hp : (N:ℝ) ≤ (N:ℝ)^(98:ℝ) := by
      simpa using Real.rpow_le_rpow_of_exponent_le hn.le (by norm_num : (1:ℝ) ≤ 98)
    have ht : (V:ℝ) < (V:ℝ)*(N:ℝ)^(98:ℝ) := by nlinarith
    have hc := Nat.le_ceil ((V:ℝ)*(N:ℝ)^(iterationRho M 0-2))
    have hr : iterationRho M 0-2 = (98:ℝ) := by norm_num [iterationRho]
    rw [hr] at hc
    change V < Nat.ceil ((V:ℝ)*(N:ℝ)^(iterationRho M 0-2))
    rw [hr]
    exact_mod_cast ht.trans_le hc

/-- Terminal chunkiness follows from the actual projection-target bound.
The rounding costs factor 2; the terminal threshold is NOT replaced by 1. -/
theorem rounded_terminal_image_bound (N V B M : ℕ) (hN : 2 ≤ N)
    (hV : N^2 ≤ V) (hB : B ≤ N^2) (hM : 2 ≤ M) :
    iterationFiberThreshold N V M M * B ≤ 2*V ∧ 0 < iterationMassThreshold N V M M := by
  have hn : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN' : (1:ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hV' : (N:ℝ)^2 ≤ V := by exact_mod_cast hV
  have hin := large_family_rounding_inputs (N:ℝ) V M M hN' hV' hM (le_refl _)
  have hround := (iterationFiberThreshold_bounds (N:ℝ) V M M hin.2).2
  have hr := (iterationRho_endpoints M (by omega)).2
  rw [hr] at hround
  norm_num only [zero_sub] at hround
  have hB' : (B:ℝ) ≤ (N:ℝ)^2 := by exact_mod_cast hB
  have hmul := mul_le_mul hround hB' (Nat.cast_nonneg B)
    (by positivity : 0 ≤ 2*((V:ℝ)*(N:ℝ)^(-2:ℝ)))
  have he : (2*((V:ℝ)*(N:ℝ)^(-2:ℝ)))*(N:ℝ)^2 = 2*V := by
    rw [Real.rpow_neg hn.le,Real.rpow_two]
    field_simp
  rw [he] at hmul
  constructor
  · exact_mod_cast hmul
  · apply Nat.ceil_pos.mpr
    linarith [hin.1]

/-- Actual rounded-threshold level selection, with terminal chunkiness
proved from projection cardinalities and the large-family regime. -/
theorem select_rounded_projection_level {A B I : Type*} [DecidableEq B]
    (levels : ℕ → Finset I) (S : I → Finset A) (f : I → A → B)
    (N M : ℕ) (hN : 2 ≤ N) (hM : 2 ≤ M)
    (hroot : (levels 0).Nonempty)
    (hsize : ∀ k ≤ M, ∀ i ∈ levels k, N^2 ≤ (S i).card)
    (himage : ∀ i ∈ levels M, ((S i).image (f i)).card ≤ N^2) :
    ∃ k < M, ∃ i ∈ levels k,
      iterationMassThreshold N (S i).card M k ≤
        ((S i).filter (fun x => ((S i).filter (fun y => f i y = f i x)).card <
          iterationFiberThreshold N (S i).card M k)).card ∧
      ∀ j ∈ levels (k+1), ∃ Q ⊆ S j,
        (S j).card-Q.card < iterationMassThreshold N (S j).card M (k+1) ∧
        iterationFiberThreshold N (S j).card M (k+1)*(Q.image (f j)).card ≤ 2*(S j).card := by
  let L := fun k i => iterationFiberThreshold N (S i).card M k
  let E := fun k i => iterationMassThreshold N (S i).card M k
  let U := fun k i => E k i ≤ ((S i).filter (fun x =>
    ((S i).filter (fun y => f i y = f i x)).card < L k i)).card
  let C := fun k i => ∃ Q ⊆ S i, (S i).card-Q.card < E k i ∧ L k i*(Q.image (f i)).card ≤ 2*(S i).card
  apply exists_uniform_before_chunky levels U C M (by omega)
  · obtain ⟨i,hi⟩ := hroot
    have hb := rounded_root_bounds N (S i).card M hN (hsize 0 (by omega) i hi) hM
    refine ⟨i,hi,?_⟩
    have he : (S i).filter (fun x => ((S i).filter (fun y => f i y = f i x)).card < L 0 i) = S i := by
      apply Finset.filter_eq_self.mpr
      intro x _
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_lt hb.2
    dsimp [U]
    rw [he]
    exact hb.1
  · intro i hi
    have hb := rounded_terminal_image_bound N (S i).card ((S i).image (f i)).card M hN
      (hsize M (le_refl _) i hi) (himage i hi) hM
    exact ⟨S i,Finset.Subset.refl _,by simpa using hb.2,hb.1⟩
  · intro k _ i _ hn
    obtain ⟨Q,hQ,hE,hL⟩ := (projection_uniform_or_chunky (S i) (f i) (L k i) (E k i)).resolve_left hn
    exact ⟨Q,hQ,hE,by omega⟩

end KakeyaTwoScale
#print axioms KakeyaTwoScale.large_family_rounding_inputs
#print axioms KakeyaTwoScale.rounded_root_bounds
#print axioms KakeyaTwoScale.rounded_terminal_image_bound
#print axioms KakeyaTwoScale.select_rounded_projection_level
