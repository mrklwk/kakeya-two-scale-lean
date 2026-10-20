module
public import KakeyaTwoScale.FrozenFamilyAccounting

@[expose] public section

open scoped BigOperators
namespace KakeyaTwoScale

def frozenHeightPotential {k : ℕ} (d : ℕ) (H : Fin k → ℕ) : ℕ :=
  ∑ j, (H j+d*(if H j=0 then 0 else 1))

def dropFamilyHeight {k : ℕ} (d : ℕ) (H : Fin k → ℕ) (i : Fin k) (j : Fin k) : ℕ :=
  if j=i then H j-d else H j

theorem fixed_drop_height_mono {k d : ℕ} (H : Fin k → ℕ) (i j : Fin k) :
    dropFamilyHeight d H i j ≤ H j := by
  unfold dropFamilyHeight
  split <;> omega

theorem fixed_drop_potential {k d : ℕ} (H : Fin k → ℕ) (i : Fin k) (hi : 0 < H i) :
    frozenHeightPotential d (dropFamilyHeight d H i)+d ≤ frozenHeightPotential d H := by
  have hpoint (j : Fin k) :
      dropFamilyHeight d H i j+d*(if dropFamilyHeight d H i j=0 then 0 else 1)+
        (if j=i then d else 0) ≤ H j+d*(if H j=0 then 0 else 1) := by
    by_cases hj : j=i
    · subst j
      simp only [dropFamilyHeight,ite_true]
      split_ifs <;> omega
    · simp [dropFamilyHeight,hj]
  have hh := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin k))) => hpoint j)
  simpa only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true,frozenHeightPotential] using hh

theorem frozen_potential_bound {k d B : ℕ} (H : Fin k → ℕ) (hH : ∀ j, H j ≤ B) :
    frozenHeightPotential d H ≤ k*(B+d) := by
  have hpoint (j : Fin k) : H j+d*(if H j=0 then 0 else 1) ≤ B+d := by
    split_ifs <;> simp_all
  simpa [frozenHeightPotential] using
    Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin k))) => hpoint j)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.fixed_drop_height_mono
#print axioms KakeyaTwoScale.fixed_drop_potential
#print axioms KakeyaTwoScale.frozen_potential_bound
