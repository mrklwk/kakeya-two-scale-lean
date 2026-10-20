module
public import KakeyaTwoScale.ConcreteRootAmbient
public import KakeyaTwoScale.ConcreteRootDecomposition
public import KakeyaTwoScale.ActualArchiveEpsilonEnvelope

@[expose] public section

open Filter
noncomputable section
namespace KakeyaTwoScale

/-- Uniform epsilon envelope for archives whose root is actually constructed
from source-separated unit cylinders and literal cube tuples. Precision and
scale threshold precede the finite family, translation, relation and block.
This is a geometric theorem, not the published analytic Zahl estimate. -/
theorem exists_concrete_root_archive_envelope (n k : ℕ) (hn : 0<n) (hk : 0<k)
    {epsilon : ℝ} (he : 0<epsilon) :
    ∃ tau : ℝ, 0<tau ∧ ∃ t : ℕ, ∃ ht : 2≤t, ∀ᶠ q : ℕ in atTop,
      ∀ (hq : 1≤q) (N : ℕ) (Y : Finset (RootTuple n k (Fin N))) (a : Fin n → ℤ)
        (b u : Fin N → EuclideanSpace ℝ (Fin n)) (hu : ∀ o, ‖u o‖=1)
        (hsep : ∀ o p, o≠p → ((2:ℝ)^q)⁻¹ ≤ Real.arccos |inner ℝ (u o) (u p)|)
        (hinc : ∀ y ∈ Y, ∀ j, (rootGridCube ((2:ℝ)^q)⁻¹ y.1 ∩
          flatCylinder (b (y.2 j)) (u (y.2 j)) 1 ((2:ℝ)^q)⁻¹).Nonempty)
        (hne : (coarseRootTuples Y ((2:ℝ)^q)⁻¹ a).Nonempty)
        (alpha : ℝ) (hp : 0<alpha) (hp1 : alpha≤1),
      let I := concreteRootAmbient hn hk hq ht Y a b u hu hsep hinc hne alpha hp hp1
      ∃ H : ActualBufferedArchive k (n+1) (((4*k+3)*n)*q) q ⌊tau*(q:ℝ)⌋₊ t
          (RootTuple n k (Fin N)) (Fin n → ℤ) (Fin N) (fun j => (I.W.count j:ℝ)) I 1 1 n,
        H.loss ≤ (2:ℝ)^(epsilon*(q:ℝ)/2) ∧
        H.finalUpper ≤ (2:ℝ)^(epsilon*(q:ℝ)/2) ∧
        H.loss*H.finalUpper ≤ (2:ℝ)^(epsilon*(q:ℝ)) ∧
        tupleCubeMass I.W.tuples I.cube I.cubes I.alpha / (2:ℝ)^(epsilon*(q:ℝ)/2) ≤
          tupleCubeMass H.terminal.state.tuples I.cube I.cubes I.alpha := by
  obtain ⟨tau,htau,t,ht,huniform⟩ := exists_actual_archive_epsilon_envelope
    n k (n+1) ((4*k+3)*n) 0 hn he
  obtain ⟨Q,hQ⟩ := exists_nat_gt (2/tau)
  refine ⟨tau,htau,t,ht,?_⟩
  filter_upwards [huniform,eventually_ge_atTop Q] with q hbound hqQ
  intro hq N Y a b u hu hsep hinc hne alpha hp hp1
  let I := concreteRootAmbient hn hk hq ht Y a b u hu hsep hinc hne alpha hp hp1
  have hqR : (Q:ℝ) ≤ q := by exact_mod_cast hqQ
  have hscale : 2 ≤ tau*(q:ℝ) := by
    have h := (div_lt_iff₀ htau).mp (hQ.trans_le hqR)
    linarith
  have ha : 0 < ⌊tau*(q:ℝ)⌋₊ := (floor_drop_bounds hscale).1
  obtain ⟨H⟩ := I.exists_actual_archive (fun j => (I.W.count j:ℝ)) 1 1 ha ht
    (fun _ => Nat.cast_nonneg _) (by norm_num) (by norm_num) (fun j => by simp) n (le_refl _)
  have hh := hbound _ _ _ _ _ _ _ _ _ _ (fun j => (I.W.count j:ℝ)) I 1 1 H
    (by omega) rfl (fun _ _ => rfl) (le_refl _) (le_refl _) (le_refl _) (le_refl _) (le_refl _)
  refine ⟨H,hh.1,by simpa using hh.2.1,by simpa using hh.2.2,?_⟩
  have hm := H.terminal_mass_of_dyadic_loss (epsilon/2) q (by
    simpa only [div_mul_eq_mul_div] using hh.1)
  simpa only [div_mul_eq_mul_div] using hm

end KakeyaTwoScale
#print axioms KakeyaTwoScale.exists_concrete_root_archive_envelope
#print axioms KakeyaTwoScale.kakeya_upperMinkowski_lower_of_published_zahl
