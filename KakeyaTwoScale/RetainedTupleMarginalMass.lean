module
public import KakeyaTwoScale.TerminalTupleMass
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow
public import Mathlib.Analysis.Convex.Jensen

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- A cube's actual retained marginal; this is an image of the stored relation,
not the original family of every tube meeting the cube. -/
def retainedCubeMarginal {T Q O : Type*} [DecidableEq Q] [DecidableEq O]
    {k : ℕ} (Y : Finset T) (cube : T → Q) (original : T → Fin k → O)
    (j : Fin k) (q : Q) : Finset O :=
  (Y.filter fun y => cube y = q).image fun y => original y j

/-- Injectivity of the actual tuple representation yields the one-marginal
capacity bound. The other factors may be any genuine per-cube upper envelopes. -/
theorem retained_capacity_le_one_marginal {T Q O : Type*}
    [DecidableEq T] [DecidableEq Q] [DecidableEq O] {k : ℕ}
    (Y : Finset T) (cube : T → Q) (original : T → Fin k → O)
    (available : Fin k → Q → Finset O)
    (hmem : ∀ y ∈ Y, ∀ l, original y l ∈ available l (cube y))
    (hinj : ∀ y ∈ Y, ∀ z ∈ Y, cube y = cube z → original y = original z → y = z)
    (j : Fin k) (q : Q) :
    ParentLevel.capacity Y cube q ≤
      (retainedCubeMarginal Y cube original j q).card *
        ∏ l ∈ Finset.univ.erase j, (available l q).card := by
  classical
  let pieces : Fin k → Finset O := fun l =>
    if l = j then retainedCubeMarginal Y cube original j q else available l q
  have hb := terminal_fiber_card_le (Y.filter fun y => cube y = q) cube original pieces
    (by
      intro y hy l
      obtain ⟨hy, hyq⟩ := Finset.mem_filter.mp hy
      dsimp [pieces]
      split_ifs with hl
      · subst l
        exact Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr ⟨hy, hyq⟩, rfl⟩
      · exact hyq ▸ hmem y hy l)
    (by
      intro y hy z hz he ho
      exact hinj y (Finset.mem_filter.mp hy).1 z (Finset.mem_filter.mp hz).1 he ho) q
  have hcap : ParentLevel.capacity (Y.filter fun y => cube y = q) cube q =
      ParentLevel.capacity Y cube q := by
    unfold ParentLevel.capacity
    congr 1
    ext y
    simp
  rw [hcap, ← Finset.mul_prod_erase Finset.univ (fun l => (pieces l).card) (Finset.mem_univ j)] at hb
  have he : (∏ l ∈ Finset.univ.erase j, (pieces l).card) =
      ∏ l ∈ Finset.univ.erase j, (available l q).card := by
    apply Finset.prod_congr rfl
    intro l hl
    simp [pieces, (Finset.mem_erase.mp hl).1]
  rw [he] at hb
  simpa [pieces] using hb

/-- Concavity in normalized form, avoiding any ambiguity at an empty cube bank. -/
theorem finite_rpow_mean_le {Q : Type*} (cubes : Finset Q) (hne : cubes.Nonempty)
    (f : Q → ℝ) (hf : ∀ q ∈ cubes, 0 ≤ f q) {p : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (∑ q ∈ cubes, (f q)^p) / (cubes.card : ℝ) ≤
      ((∑ q ∈ cubes, f q) / (cubes.card : ℝ))^p := by
  have hV : 0 < (cubes.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hne
  have hh := (Real.concaveOn_rpow hp hp1).le_map_sum
    (t := cubes) (w := fun _ => (cubes.card : ℝ)⁻¹) (p := f)
    (fun _ _ => inv_nonneg.mpr hV.le) (by simp [hV.ne']) hf
  simpa only [smul_eq_mul, ← Finset.mul_sum, ← div_eq_inv_mul, ← Finset.sum_div] using hh

/-- Retained nonlinear mass controls its actual single-family incidence sum.
No original-incidence coverage or multilinear Kakeya estimate is assumed. -/
theorem retained_tuple_mass_mean_le {T Q O : Type*}
    [DecidableEq T] [DecidableEq Q] [DecidableEq O] {k : ℕ}
    (Y : Finset T) (cube : T → Q) (cubes : Finset Q) (hne : cubes.Nonempty)
    (original : T → Fin k → O) (available : Fin k → Q → Finset O)
    (hmem : ∀ y ∈ Y, ∀ l, original y l ∈ available l (cube y))
    (hinj : ∀ y ∈ Y, ∀ z ∈ Y, cube y = cube z → original y = original z → y = z)
    (j : Fin k) (μ : Fin k → ℝ) (hμ : ∀ l, 0 ≤ μ l)
    (hbound : ∀ q ∈ cubes, ∀ l, ((available l q).card : ℝ) ≤ μ l)
    {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    tupleCubeMass Y cube cubes p / (cubes.card : ℝ) ≤
      ((∏ l ∈ Finset.univ.erase j, μ l) *
        (∑ q ∈ cubes, ((retainedCubeMarginal Y cube original j q).card : ℝ)) /
          (cubes.card : ℝ))^p := by
  let A : ℝ := ∏ l ∈ Finset.univ.erase j, μ l
  let a : Q → ℝ := fun q => (retainedCubeMarginal Y cube original j q).card
  have hA : 0 ≤ A := Finset.prod_nonneg (fun l _ => hμ l)
  have hpoint (q) (hq : q ∈ cubes) : (ParentLevel.capacity Y cube q : ℝ) ≤ A * a q := by
    have hh : (ParentLevel.capacity Y cube q : ℝ) ≤
        a q * ∏ l ∈ Finset.univ.erase j, ((available l q).card : ℝ) := by
      dsimp [a]
      exact_mod_cast retained_capacity_le_one_marginal Y cube original available hmem hinj j q
    exact hh.trans ((mul_le_mul_of_nonneg_left
      (Finset.prod_le_prod₀ (fun l _ => Nat.cast_nonneg _) (fun l _ => hbound q hq l))
      (Nat.cast_nonneg _)).trans_eq (mul_comm _ _))
  calc
    _ ≤ (∑ q ∈ cubes, (A * a q)^p) / (cubes.card : ℝ) := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact Finset.sum_le_sum (fun q hq => Real.rpow_le_rpow (Nat.cast_nonneg _) (hpoint q hq) hp)
    _ ≤ ((∑ q ∈ cubes, A * a q) / (cubes.card : ℝ))^p :=
      finite_rpow_mean_le cubes hne _ (fun q _ => mul_nonneg hA (Nat.cast_nonneg _)) hp hp1
    _ = _ := by rw [← Finset.mul_sum]

/-- Exact loss inversion used by mass-to-length: retention η gives the
incidence factor η^(1/p), not η. This is scalar algebra after finite Jensen. -/
theorem retained_mass_incidence_lower {p η A μ V I M : ℝ}
    (hp : 0 < p) (hη : 0 ≤ η) (hA : 0 < A) (hμ : 0 ≤ μ)
    (hV : 0 < V) (hI : 0 ≤ I)
    (hlower : η * (A * μ)^p ≤ M / V)
    (hupper : M / V ≤ (A * I / V)^p) :
    η^(1/p) * V * μ ≤ I := by
  have hbase : 0 ≤ A * μ := mul_nonneg hA.le hμ
  have hpw : (η^(1/p) * (A * μ))^p = η * (A * μ)^p := by
    rw [Real.mul_rpow (Real.rpow_nonneg hη _) hbase]
    rw [one_div, Real.rpow_inv_rpow hη hp.ne']
  have hi : η^(1/p) * (A * μ) ≤ A * I / V := by
    apply (Real.rpow_le_rpow_iff (mul_nonneg (Real.rpow_nonneg hη _) hbase)
      (div_nonneg (mul_nonneg hA.le hI) hV.le) hp).mp
    rw [hpw]
    exact hlower.trans hupper
  have hh := (le_div_iff₀ hV).mp hi
  have he : η^(1/p) * (A * μ) * V = A * (η^(1/p) * V * μ) := by ring
  rw [he] at hh
  exact (mul_le_mul_iff_right₀ hA).mp hh

end KakeyaTwoScale
#print axioms KakeyaTwoScale.retained_capacity_le_one_marginal
#print axioms KakeyaTwoScale.finite_rpow_mean_le
#print axioms KakeyaTwoScale.retained_tuple_mass_mean_le

#print axioms KakeyaTwoScale.retained_mass_incidence_lower
