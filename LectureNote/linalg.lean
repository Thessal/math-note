import LectureNote.Common
import Mathlib.LinearAlgebra.Basic
import Mathlib.LinearAlgebra.Dimension
import Mathlib.LinearAlgebra.Finrank
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.Logic.Equiv.Defs

open Matrix 

-- Rank
section Rank
variable {n p : ℕ} (A B : Matrix (fin n) (fin p) ℝ)

#check And (Matrix.toLin' A).rank_le_of_injective (Matrix.toLin' A).rank_le_of_surjective
#check rank_range_add_rank_ker (Matrix.toLin' A) 
theorem invertible_matrix_det_rank (h: n = p) :
  A.det > 0 → A.rank = n := by
  -- intro h1
  -- contrapose! h1
  -- have h2 A.rank < n
  -- rw [rank_range_add_rank_ker]  -- by rank nullity thm, nullity > 0
  -- ∃ T, (A * T).det = 0 
  sorry 
-- TODO: rank(AB) ≤ min(rank(A), rank(B))
-- TODO: rank(A A.transpose) = rank(A.transpose A) = rank(A)
end Rank


-- Determinant
section Determinant 
variable (n : ℕ)  (A B : Matrix (fin n) (fin n) ℝ) {Fintype n} (σ : Equiv.Perm (fin n))
variable (i : ℕ) (c : ℝ) 
-- Properties of determinant
#check A.det_updateColumn_smul A i c (fun n => (n:ℝ))
#check A.det_permute σ A
-- TODO : det(AB) = det(A)det(B)
-- TODO : if A is triangular, det(A) = sum A_ii
-- TODO : det(A) = mul eigenvalues
end Determinant 


section Determinant_test
def AA := (![![1,2,3],![4,5,6],![7,8,9]] : Matrix (Fin 3) (Fin 3) ℝ)
-- Define a permutation that swaps the first and second elements
def my_perm : Equiv.Perm (Fin 3) :=
{ toFun := λ i => if i = 0 then 1 else if i = 1 then 0 else i,
  invFun := λ i => if i = 0 then 1 else if i = 1 then 0 else i,
  left_inv := by sorry,
  right_inv := by sorry 
}
example : (Matrix.det (λ i j => AA (my_perm i) j)) = Equiv.Perm.sign my_perm * Matrix.det AA :=
  by 
  exact Matrix.det_permute my_perm AA
end Determinant_test

