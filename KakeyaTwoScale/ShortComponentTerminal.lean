module
public import KakeyaTwoScale.TerminalTupleMass
public import KakeyaTwoScale.ShortCylinderGridCount
public import KakeyaTwoScale.LocalizedAncestorCylinder
public import Mathlib.Analysis.MeanInequalities

@[expose] public section

open Set Metric
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
attribute [local instance] Classical.propDecidable

/-- A finite multilinear incidence estimate with no factor counting all cubes.
The exponent need only be at least the reciprocal number of families. -/
theorem sum_product_rpow_le_of_family_sums {Q : Type*} {k : ℕ}
    (cubes : Finset Q) (hk : 0 < k) (b : Fin k → Q → ℝ) (B : Fin k → ℝ)
    (hb : ∀ j q, 0 ≤ b j q) (hB : ∀ j, 0 < B j)
    (hsum : ∀ j, ∑ q ∈ cubes, b j q ≤ B j)
    {p : ℝ} (hp : 1/(k:ℝ) ≤ p) :
    (∑ q ∈ cubes, (∏ j, b j q)^p) ≤ (∏ j, B j)^p := by
  classical
  have hkR : 0 < (k:ℝ) := by exact_mod_cast hk
  let f : Fin k → Q → ℝ := fun j q => b j q/B j
  have hf (j q) : 0 ≤ f j q := div_nonneg (hb j q) (hB j).le
  have hfs (j) : ∑ q ∈ cubes, f j q ≤ 1 := by
    dsimp [f]
    rw [← Finset.sum_div]
    exact (div_le_one (hB j)).mpr (hsum j)
  have hf1 (j q) (hq : q ∈ cubes) : f j q ≤ 1 :=
    (Finset.single_le_sum (fun t _ => hf j t) hq).trans (hfs j)
  have hw : (∑ _j : Fin k, (1:ℝ)/(k:ℝ))=1 := by
    simp [hkR.ne']
  have hpoint (q) (hq : q ∈ cubes) :
      (∏ j, f j q)^p ≤ ∑ j, (1/(k:ℝ))*f j q := by
    have hn : 0 ≤ ∏ j, f j q := Finset.prod_nonneg (fun j _ => hf j q)
    have hle : ∏ j, f j q ≤ 1 := by
      calc
        _ ≤ ∏ _j : Fin k, (1:ℝ) := Finset.prod_le_prod₀ (fun j _ => hf j q) (fun j _ => hf1 j q hq)
        _ = 1 := by simp
    have hpow := Real.rpow_le_rpow_of_exponent_ge' hn hle (by positivity : 0 ≤ 1/(k:ℝ)) hp
    have ham := Real.geom_mean_le_arith_mean_weighted (Finset.univ : Finset (Fin k))
      (fun _ => 1/(k:ℝ)) (fun j => f j q) (fun _ _ => by positivity) hw (fun j _ => hf j q)
    rw [Real.finsetProd_rpow _ _ (fun j _ => hf j q) _] at ham
    exact hpow.trans ham
  have hnorm : ∑ q ∈ cubes, (∏ j, f j q)^p ≤ 1 := by
    calc
      _ ≤ ∑ q ∈ cubes, ∑ j, (1/(k:ℝ))*f j q := Finset.sum_le_sum hpoint
      _ = ∑ j, (1/(k:ℝ))*(∑ q ∈ cubes, f j q) := by rw [Finset.sum_comm]; simp_rw [Finset.mul_sum]
      _ ≤ ∑ _j : Fin k, (1/(k:ℝ))*1 := Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hfs j) (by positivity))
      _ = 1 := by simpa using hw
  have hprod : 0 < ∏ j, B j := Finset.prod_pos (fun j _ => hB j)
  have hid (q) : (∏ j, b j q)^p = (∏ j, f j q)^p * (∏ j, B j)^p := by
    rw [← Real.mul_rpow (Finset.prod_nonneg (fun j _ => hf j q)) hprod.le,
      ← Finset.prod_mul_distrib]
    congr 1
    apply Finset.prod_congr rfl
    intro j _
    exact (div_mul_cancel₀ (b j q) (hB j).ne').symm
  simp_rw [hid]
  rw [← Finset.sum_mul]
  exact (mul_le_mul_of_nonneg_right hnorm (Real.rpow_nonneg hprod.le p)).trans_eq (one_mul _)

/-- Count actual cube/piece incidences in either order. -/
theorem sum_incident_piece_cards {Q P : Type*} [DecidableEq Q] [DecidableEq P]
    (cubes : Finset Q) (pieces : Finset P) (incident : P → Q → Prop)
    :
    (∑ q ∈ cubes, ((pieces.filter fun t => incident t q).card:ℝ)) =
      ∑ t ∈ pieces, ((cubes.filter fun q => incident t q).card:ℝ) := by
  classical
  simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
  rw [Finset.sum_comm]

/-- Terminal bound for the stored original relation. Only each physical
piece's cube-incidence count is used; no bound on all cubes or lower family
count is assumed. -/
theorem terminal_tuple_mass_le_incidence_caps {T Q P : Type*}
    [DecidableEq T] [DecidableEq Q] [DecidableEq P] {k : ℕ}
    (Y : Finset T) (hY : Y.Nonempty) (cube : T → Q) (cubes : Finset Q)
    (piece : T → Fin k → P) (pieces : Fin k → Finset P)
    (incident : Fin k → P → Q → Prop)
    (hmem : ∀ y ∈ Y, ∀ j, piece y j ∈ pieces j)
    (hinc : ∀ y ∈ Y, ∀ j, incident j (piece y j) (cube y))
    (hinj : ∀ y ∈ Y, ∀ z ∈ Y, cube y=cube z → piece y=piece z → y=z)
    (hk : 0 < k) {B : ℕ} (hB : 0 < B)
    (hcap : ∀ j t, t ∈ pieces j →
      ((cubes.filter fun q => incident j t q).card:ℝ) ≤ B)
    {p : ℝ} (hp : 1/(k:ℝ) ≤ p) :
    tupleCubeMass Y cube cubes p ≤ (∏ j, (B:ℝ)*((pieces j).card:ℝ))^p := by
  classical
  let b : Fin k → Q → ℝ := fun j q => ((pieces j).filter fun t => incident j t q).card
  have hp0 : 0 ≤ p := (by positivity : (0:ℝ) ≤ 1/(k:ℝ)).trans hp
  have hpoint (q : Q) : (ParentLevel.capacity Y cube q:ℝ) ≤ ∏ j, b j q := by
    have hh := Finset.card_le_card_of_injOn (s:=Y.filter fun y => cube y=q)
      (t:=Fintype.piFinset (fun j => (pieces j).filter fun t => incident j t q)) piece
      (fun y hy => Fintype.mem_piFinset.mpr (fun j =>
        Finset.mem_filter.mpr ⟨hmem y (Finset.mem_filter.mp hy).1 j,
          (Finset.mem_filter.mp hy).2 ▸ hinc y (Finset.mem_filter.mp hy).1 j⟩))
      (by
        intro y hy z hz he
        obtain ⟨hy,hyq⟩ := Finset.mem_filter.mp hy
        obtain ⟨hz,hzq⟩ := Finset.mem_filter.mp hz
        exact hinj y hy z hz (hyq.trans hzq.symm) he)
    dsimp [b]
    exact_mod_cast (show ParentLevel.capacity Y cube q ≤
      ∏ j, ((pieces j).filter fun t => incident j t q).card by
        simpa only [ParentLevel.capacity,Fintype.card_piFinset] using hh)
  have hpos (j : Fin k) : 0 < (B:ℝ)*((pieces j).card:ℝ) := by
    obtain ⟨y,hy⟩ := hY
    have he : (pieces j).Nonempty := ⟨piece y j,hmem y hy j⟩
    exact mul_pos (by exact_mod_cast hB) (by exact_mod_cast Finset.card_pos.mpr he)
  have hsum (j : Fin k) : ∑ q ∈ cubes, b j q ≤ (B:ℝ)*((pieces j).card:ℝ) := by
    rw [show (∑ q ∈ cubes, b j q) =
      ∑ t ∈ pieces j, ((cubes.filter fun q => incident j t q).card:ℝ) by
        exact sum_incident_piece_cards cubes (pieces j) (incident j)]
    exact (Finset.sum_le_sum (fun t ht => hcap j t ht)).trans_eq (by simp [mul_comm])
  exact (Finset.sum_le_sum (fun q _ => Real.rpow_le_rpow (Nat.cast_nonneg _) (hpoint q) hp0)).trans
    (sum_product_rpow_le_of_family_sums cubes hk b (fun j => (B:ℝ)*((pieces j).card:ℝ))
      (fun j q => Nat.cast_nonneg _) hpos hsum hp)

/-- The actual all-short terminal estimate for Euclidean cylinders and grid
cubes. A uniform bound is constructed before the scale and finite data. No
common grain ball, family lower budget, or incidence-count premise remains. -/
theorem exists_short_component_terminal_bound (n : ℕ) (A : ℝ) :
    ∃ B : ℕ, 0 < B ∧ ∀ {T P : Type} [DecidableEq T] [DecidableEq P] {k : ℕ},
      ∀ (Y : Finset T), Y.Nonempty → ∀ (cube : T → Fin n → ℤ)
        (cubes : Finset (Fin n → ℤ)) (piece : T → Fin k → P)
        (pieces : Fin k → Finset P)
        (base dir : Fin k → P → EuclideanSpace ℝ (Fin n)) (L : Fin k → P → ℝ)
        (δ : ℝ), 0 < δ →
      (∀ j t, ‖dir j t‖=1) → (∀ j t, t ∈ pieces j → L j t ≤ A*δ) →
      (∀ y ∈ Y, ∀ j, piece y j ∈ pieces j) →
      (∀ y ∈ Y, ∀ j,
        ((WithLp.ofLp ⁻¹' gridCell δ (cube y)) ∩
          flatCylinder (base j (piece y j)) (dir j (piece y j)) (L j (piece y j)) δ).Nonempty) →
      (∀ y ∈ Y, ∀ z ∈ Y, cube y=cube z → piece y=piece z → y=z) →
      0 < k → ∀ p : ℝ, 1/(k:ℝ) ≤ p →
        tupleCubeMass Y cube cubes p ≤ (∏ j, (B:ℝ)*((pieces j).card:ℝ))^p := by
  obtain ⟨B,hB,hpack⟩ := exists_shortCylinder_grid_count n A
  refine ⟨B,hB,?_⟩
  intro T P _ _ k Y hY cube cubes piece pieces base dir L δ hδ hu hL hmem hinc hinj hk p hp
  let incident : Fin k → P → (Fin n → ℤ) → Prop := fun j t z =>
    ((WithLp.ofLp ⁻¹' gridCell δ z) ∩ flatCylinder (base j t) (dir j t) (L j t) δ).Nonempty
  apply terminal_tuple_mass_le_incidence_caps Y hY cube cubes piece pieces incident hmem hinc hinj hk hB ?_ hp
  intro j t ht
  exact_mod_cast hpack δ (L j t) hδ (hL j t ht) (base j t) (dir j t) (hu j t)
    (cubes.filter fun q => incident j t q) (fun q hq => (Finset.mem_filter.mp hq).2)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.sum_product_rpow_le_of_family_sums

#print axioms KakeyaTwoScale.sum_incident_piece_cards
#print axioms KakeyaTwoScale.terminal_tuple_mass_le_incidence_caps

#print axioms KakeyaTwoScale.exists_short_component_terminal_bound
