module
public import KakeyaTwoScale.RetainedTupleMarginalMass
public import KakeyaTwoScale.DyadicCylinderGridCount
public import KakeyaTwoScale.ShortComponentTerminal
public import KakeyaTwoScale.FrozenGeometryState

@[expose] public section

open Set Metric
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
attribute [local instance] Classical.propDecidable

/-- Actual retained original incidences are bounded by physical record
incidences. Repeated records of one original only enlarge the right side. -/
theorem actual_retained_marginal_le_record_incidence {n k : ℕ} {T O : Type}
    [DecidableEq T] [DecidableEq O]
    (S : FrozenGeometryState n k T (Fin n → ℤ) O)
    (Y₀ : Finset T) (cube : T → Fin n → ℤ) (tube : T → Fin k → O)
    (δ : ℝ)
    (hv : S.Valid Y₀ cube tube (fun z => WithLp.ofLp ⁻¹' gridCell δ z) δ)
    (j : Fin k) (q : Fin n → ℤ) :
    (retainedCubeMarginal S.tuples cube tube j q).card ≤
      ((S.records j).filter fun t =>
        ((WithLp.ofLp ⁻¹' gridCell δ q) ∩ S.geometry δ j t).Nonempty).card := by
  classical
  let R := (S.records j).filter fun t =>
    ((WithLp.ofLp ⁻¹' gridCell δ q) ∩ S.geometry δ j t).Nonempty
  have hs : retainedCubeMarginal S.tuples cube tube j q ⊆ R.image (S.original j) := by
    intro o ho
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp ho
    obtain ⟨hy, hyq⟩ := Finset.mem_filter.mp hy
    apply Finset.mem_image.mpr
    refine ⟨S.parent y j, Finset.mem_filter.mpr ⟨?_, ?_⟩, hv.2.2.1 y hy j⟩
    · exact Finset.mem_image.mpr ⟨y, hy, rfl⟩
    · exact hyq ▸ hv.2.2.2.2.1 y hy j
  exact (Finset.card_le_card hs).trans (Finset.card_image_le)

/-- Dimension-only linear incidence bound on every actual valid dyadic state.
No disjointness or uniform count estimate is required. -/
theorem exists_actual_marginal_incidence_bound (n : ℕ) :
    ∃ B : ℕ, 0 < B ∧ ∀ {k : ℕ} {T O : Type} [DecidableEq T] [DecidableEq O],
      ∀ (S : FrozenGeometryState n k T (Fin n → ℤ) O)
        (Y₀ : Finset T) (cube : T → Fin n → ℤ) (tube : T → Fin k → O)
        (δ : ℝ), 0 < δ →
      S.Valid Y₀ cube tube (fun z => WithLp.ofLp ⁻¹' gridCell δ z) δ →
      ∀ (cubes : Finset (Fin n → ℤ)) (j : Fin k),
      (∑ q ∈ cubes, ((retainedCubeMarginal S.tuples cube tube j q).card : ℝ)) ≤
        (B:ℝ) * (S.length δ j / δ) * (S.count j : ℝ) := by
  classical
  obtain ⟨B, hB, hgrid⟩ := exists_dyadicCylinder_grid_count n
  refine ⟨B, hB, ?_⟩
  intro k T O _ _ S Y₀ cube tube δ hδ hv cubes j
  let incident : S.Piece → (Fin n → ℤ) → Prop := fun t q =>
    ((WithLp.ofLp ⁻¹' gridCell δ q) ∩ S.geometry δ j t).Nonempty
  have hb (t : S.Piece) :
      ((cubes.filter fun q => incident t q).card : ℝ) ≤ (2:ℝ)^(S.height j) * B := by
    have hh := hgrid δ hδ (2^(S.height j)) (S.base j t) (S.axis j t) (hv.2.1 j t)
      (cubes.filter fun q => incident t q) (by
        intro z hz
        simpa [incident, FrozenGeometryState.geometry, FrozenGeometryState.length,
          Nat.cast_pow, Nat.cast_ofNat, mul_comm] using (Finset.mem_filter.mp hz).2)
    exact_mod_cast hh
  calc
    _ ≤ ∑ q ∈ cubes, (((S.records j).filter fun t => incident t q).card : ℝ) := by
      apply Finset.sum_le_sum
      intro q _
      exact_mod_cast actual_retained_marginal_le_record_incidence S Y₀ cube tube δ hv j q
    _ = ∑ t ∈ S.records j, ((cubes.filter fun q => incident t q).card : ℝ) :=
      sum_incident_piece_cards cubes (S.records j) incident
    _ ≤ ∑ _t ∈ S.records j, (2:ℝ)^(S.height j)*B := Finset.sum_le_sum (fun t _ => hb t)
    _ = _ := by
      simp [FrozenGeometryState.length, FrozenGeometryState.count, hδ.ne']
      ring

/-- The physical mass-to-length inequality for the ACTUAL retained tuple
relation. μ bounds original per-cube marginals; η is measured against the
normalized full-box mass. No multilinear or coverage premise is present. -/
theorem exists_actual_mass_to_length (n : ℕ) :
    ∃ B : ℕ, 0 < B ∧ ∀ {k : ℕ} {T O : Type} [DecidableEq T] [DecidableEq O],
      ∀ (S : FrozenGeometryState n k T (Fin n → ℤ) O)
        (Y₀ : Finset T) (cube : T → Fin n → ℤ) (tube : T → Fin k → O)
        (δ : ℝ), 0 < δ →
      S.Valid Y₀ cube tube (fun z => WithLp.ofLp ⁻¹' gridCell δ z) δ →
      ∀ (cubes : Finset (Fin n → ℤ)), cubes.Nonempty →
      ∀ (available : Fin k → (Fin n → ℤ) → Finset O),
      (∀ y ∈ Y₀, ∀ l, tube y l ∈ available l (cube y)) →
      (∀ y ∈ Y₀, ∀ z ∈ Y₀, cube y = cube z → tube y = tube z → y = z) →
      ∀ (μ : Fin k → ℝ), (∀ l, 0 < μ l) →
      (∀ q ∈ cubes, ∀ l, ((available l q).card : ℝ) ≤ μ l) →
      ∀ (p η : ℝ), 0 < p → p ≤ 1 → 0 ≤ η →
      η * (cubes.card : ℝ) * (∏ l, μ l)^p ≤ tupleCubeMass S.tuples cube cubes p →
      ∀ j : Fin k,
        η^(1/p) * (cubes.card : ℝ) * μ j * δ ≤
          (B:ℝ) * S.length δ j * (S.count j : ℝ) := by
  classical
  obtain ⟨B, hB, hphysical⟩ := exists_actual_marginal_incidence_bound n
  refine ⟨B, hB, ?_⟩
  intro k T O _ _ S Y₀ cube tube δ hδ hv cubes hne available hmem hinj μ hμ hbound p η hp hp1 hη hmass j
  let A : ℝ := ∏ l ∈ Finset.univ.erase j, μ l
  let I : ℝ := ∑ q ∈ cubes, ((retainedCubeMarginal S.tuples cube tube j q).card : ℝ)
  have hA : 0 < A := Finset.prod_pos (fun l _ => hμ l)
  have hV : 0 < (cubes.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hne
  have hprod : A * μ j = ∏ l, μ l := Finset.prod_erase_mul Finset.univ μ (Finset.mem_univ j)
  have hlo : η * (A * μ j)^p ≤ tupleCubeMass S.tuples cube cubes p / (cubes.card : ℝ) := by
    apply (le_div_iff₀ hV).mpr
    rw [hprod]
    convert hmass using 1
    ring
  have hup := retained_tuple_mass_mean_le S.tuples cube cubes hne tube available
    (fun y hy l => hmem y (hv.1 hy) l)
    (fun y hy z hz hq ho => hinj y (hv.1 hy) z (hv.1 hz) hq ho)
    j μ (fun l => (hμ l).le) hbound hp.le hp1
  have hi : η^(1/p) * (cubes.card : ℝ) * μ j ≤ I :=
    retained_mass_incidence_lower hp hη hA (hμ j).le hV
      (Finset.sum_nonneg (fun q _ => Nat.cast_nonneg _)) hlo hup
  have hi' := mul_le_mul_of_nonneg_right (hi.trans (hphysical S Y₀ cube tube δ hδ hv cubes j)) hδ.le
  convert hi' using 1
  field_simp

end KakeyaTwoScale
#print axioms KakeyaTwoScale.actual_retained_marginal_le_record_incidence
#print axioms KakeyaTwoScale.exists_actual_marginal_incidence_bound
#print axioms KakeyaTwoScale.exists_actual_mass_to_length
