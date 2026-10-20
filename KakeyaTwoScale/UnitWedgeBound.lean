module
public import KakeyaTwoScale.GramRecursion

@[expose] public section

noncomputable section
namespace KakeyaTwoScale

/-- Gram volume of any ordered tuple of unit vectors is at most one,
including dependent and repeated tuples. -/
theorem tupleWedgeVolume_le_one {n k : ℕ}
    (v : Fin k → EuclideanSpace ℝ (Fin n)) (hv : ∀ i, ‖v i‖=1) :
    tupleWedgeVolume v ≤ 1 := by
  induction k with
  | zero => simp [tupleWedgeVolume, Matrix.gram]
  | succ k ih =>
    rw [← Fin.cons_self_tail v, tupleWedgeVolume_cons]
    have ht := ih (Fin.tail v) (fun i => hv i.succ)
    have hp : ‖normalProjection (Submodule.span ℝ (Set.range (Fin.tail v))) (v 0)‖ ≤ 1 := by
      have h := (normalProjection (Submodule.span ℝ (Set.range (Fin.tail v)))).le_opNorm (v 0)
      have hnorm := normalProjection_norm_le (Submodule.span ℝ (Set.range (Fin.tail v)))
      simpa only [hv 0, mul_one] using h.trans (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _))
    exact (mul_le_mul ht hp (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.tupleWedgeVolume_le_one
