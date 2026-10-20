module
public import KakeyaTwoScale.RootBandPhysicalNormalization

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
namespace ActualBufferedArchive

/-- The actual terminal theorem normalized at the original root joint band.
The dimension-only constant is strictly positive and precedes the archive. -/
theorem exists_normalized_root_band_bound (n k : ℕ) (hk : 2≤k) (hkn : k≤n+1) :
    ∃ C : ℝ, 0<C ∧
    ∀ {A B Lh a t b c J s : ℕ} {T O : Type} [DecidableEq T] [DecidableEq O]
      {N : Fin k→ℝ} {I : AmbientBufferedStageData b c k A B Lh J s T (Fin (n+1)→ℤ) O}
      {U : ℝ} {fuel : ℕ},
    ∀ (H : ActualBufferedArchive k A B Lh a t T (Fin (n+1)→ℤ) O N I 1 U fuel),
      b+c=n+1 →
      HEq I.Q (fun z : Fin (n+1)→ℤ =>
        (WithLp.ofLp ⁻¹' gridCell I.δ z : Set (EuclideanSpace ℝ (Fin (n+1))))) →
      (∀y∈I.Y₀, ∀y'∈I.Y₀, I.cube y=I.cube y' → I.tube y=I.tube y' → y=y') →
      I.alpha=1/((k-1:ℕ):ℝ) → (I.W.grains I.cube).card=1 →
      (∀j, 0≤N j) → 1≤U → (∀j, (I.W.count j:ℝ)≤U*(N j*1)) →
      ∀ θ : ℝ, 0≤θ →
      (∀y∈I.W.tuples, θ≤tupleWedgeVolume (fun j => I.W.axis j (I.W.parent y j))) →
      ∀ (m : ℕ), b=m+k → ∀ (r : ℕ) (hr : r≤H.drops), r ≤ m →
      ∀ μ : ℝ, 0<μ →
      (∀q∈I.cubes, μ^k≤(ParentLevel.capacity I.W.tuples I.cube q:ℝ)) →
      θ*μ^(k:ℝ)*((I.cubes.card:ℝ)*I.δ^(n+1))^((k:ℝ)-1) ≤
        (C*H.loss^(k-1)*(H.entryAt r hr).upper^k)*
          I.δ^((k:ℝ)-(n+1))*(∏j, I.δ^n*N j)/
            Real.exp (degreeObjectiveLog m r (fun i => Real.log (H.stageDegrees[i]?.getD 1))) := by
  classical
  obtain ⟨C,hC,hmain⟩ := exists_terminal_degree_objective n k hk hkn
  refine ⟨max 1 C,lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro A B Lh a t b c J s T O _ _ N I U fuel H hn hQ hinj hα hgrain hN hU hcount θ hθ hw m hb r hr hrm μ hμ hband
  have hlower : (I.cubes.card:ℝ)*(μ^k)^(1/((k-1:ℕ):ℝ)) ≤
      tupleCubeMass I.W.tuples I.cube I.cubes I.alpha := by
    unfold tupleCubeMass
    rw [hα]
    calc
      _ = ∑ _q ∈ I.cubes, (μ^k)^(1/((k-1:ℕ):ℝ)) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun q hq =>
        Real.rpow_le_rpow (pow_nonneg hμ.le _) (hband q hq) (by positivity))
  have hraw := hmain H hn hQ hinj hα hgrain hN hU hcount θ hθ hw m hb r hr hrm
  have hlarge : θ*(tupleCubeMass I.W.tuples I.cube I.cubes I.alpha/H.loss)^(k-1) ≤
      max 1 C*(H.entryAt r hr).upper^k*(∏j, N j)*
        Real.exp (-degreeObjectiveLog m r (fun i => Real.log (H.stageDegrees[i]?.getD 1))) := by
    apply hraw.trans
    have hup := (H.countLedger_positive (by norm_num : (0:ℝ)<1) hU _ (H.entryAt_mem r hr)).2
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right (1:ℝ) C)
          (pow_nonneg (le_trans (by norm_num) hup) k))
        (Finset.prod_nonneg (fun j _ => hN j))) (Real.exp_pos _).le
  have hp := root_band_mass_power hk hθ (Nat.cast_nonneg _) hμ H.loss_pos hlower hlarge
  apply root_band_physical_normalization n k (by omega) θ μ I.cubes.card I.δ
    (max 1 C*H.loss^(k-1)*(H.entryAt r hr).upper^k) _ N I.width_pos
  convert hp using 1
  rw [Real.exp_neg]
  ring

end ActualBufferedArchive
end KakeyaTwoScale
#print axioms KakeyaTwoScale.ActualBufferedArchive.exists_normalized_root_band_bound
