module
public import KakeyaTwoScale.TinyWedgeScale
public import KakeyaTwoScale.FlatCylinderMassLower
public import KakeyaTwoScale.SharpProjectiveCount

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- The complete tiny-wedge contribution obeys the precise published
pth-power radius and cylinder-volume exponents, even with epsilon=0.
The dimensional constant precedes radius, population, positions and directions.
This theorem estimates only the literal tail with wedge≤δ^d. -/
theorem tiny_wedge_cylinder_estimate (n k : ℕ) (hn : 0 < n) (hk : 0 < k)
    (B : ℝ) (hB : 1 < B) (hBd : B ≤ n + 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 →
      ∀ (N : ℕ) (b u : Fin N → EuclideanSpace ℝ (Fin (n + 1))),
      (∀ j, ‖u j‖ = 1) →
      (∀ i j, i ≠ j → δ ≤ Real.arccos |inner ℝ (u i) (u j)|) →
      (∫⁻ x, ENNReal.ofReal ((tinyWedgeSum k u
        (fun j => flatCylinder (b j) (u j) 1 δ) B (δ ^ (n + 1)) x) ^
        (B / ((k : ℝ) * (B - 1))))) ≤
      ENNReal.ofReal (C * δ ^ ((B / (B - 1)) * (1 - (n + 1 : ℝ) / B)) *
        (∑ j, volume.real (flatCylinder (b j) (u j) 1 δ)) ^ ((n + 1 : ℝ) / n)) := by
  classical
  obtain ⟨K, hK, hpack⟩ := projective_direction_count_sharp n
  obtain ⟨c, hc, hvolume⟩ := flatCylinder_volume_lower_unrestricted n
  let C := K ^ (((n + 1 : ℝ) - B) / ((B - 1) * n)) * c ^ (-(1 / (n : ℝ)))
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro δ hδ hδhalf N b u hu hsep
  let T := fun j => flatCylinder (b j) (u j) 1 δ
  let V : ℝ := ∑ j, volume.real (T j)
  have hBm : 0 < B - 1 := by linarith
  have hβ : 0 < B / (B - 1) - 1 := by
    have hh := (zahl_holder_conjugacy hB).1
    linarith
  have hbase := tinyWedgeSum_lintegral_le hk u T
    (fun j => (isOpen_flatCylinder _ _ _ _ (hu j)).measurableSet) volume hB
    (show 0 ≤ δ ^ (n + 1) by positivity)
  have hsum : (∑ j, volume (T j)) = ENNReal.ofReal V := by
    dsimp only [V]
    rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => measureReal_nonneg)]
    apply Finset.sum_congr rfl
    intro j _
    exact (ENNReal.ofReal_toReal (flatCylinder_unit_finite _ _ _)).symm
  rw [hsum, ← ENNReal.ofReal_mul (by positivity)] at hbase
  have hpow : (δ ^ (n + 1)) ^ (1 / (B - 1)) = δ ^ ((n + 1 : ℝ) / (B - 1)) := by
    rw [← Real.rpow_natCast_mul hδ.le]
    congr 1
    push_cast
    ring
  rw [hpow] at hbase
  by_cases hN : N = 0
  · subst N
    simp only [Nat.cast_zero, Real.zero_rpow hβ.ne', mul_zero, zero_mul, ENNReal.ofReal_zero] at hbase
    exact hbase.trans bot_le
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hVlower : c * (N : ℝ) * δ ^ n ≤ V := by
    have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin N)))
      (fun j _ => hvolume δ hδ hδhalf (b j) (u j) (hu j))
    simpa [V, T, mul_comm, mul_left_comm, mul_assoc] using hh
  have hV : 0 < V := (by positivity : 0 < c * (N : ℝ) * δ ^ n).trans_le hVlower
  have hd : (1 : ℝ) < n + 1 := by exact_mod_cast Nat.succ_lt_succ hn
  have hnormal := tiny_wedge_scale_normalization hd hB hBd hδ (by linarith)
    hNpos hV hK hc (hpack δ hδ (by linarith) N u hu hsep)
    (by simpa only [add_sub_cancel_right, Real.rpow_natCast] using hVlower)
  apply hbase.trans
  apply ENNReal.ofReal_le_ofReal
  simpa only [C, V, T, add_sub_cancel_right] using hnormal

end KakeyaTwoScale
#print axioms KakeyaTwoScale.tiny_wedge_cylinder_estimate
