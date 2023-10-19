import LectureNote.Common
import Mathlib.Data.Vector
import Mathlib.Data.Real.Basic
import Mathlib.Data.List.Basic
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
-- import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

-- Vector Space
class Vec (a : Type) where
  add : a → a → a
  prod_s : ℂ → a → a
  prod_in : a → a → ℂ
  norm : a → ℝ 
  zero : a

-- Declare infix notation for Vec operations
infixl:65 " + " => Vec.add
infixl:70 " * " => Vec.prod_s
infix:70 " ⬝ " => Vec.prod_in  
-- notation:max "|" e "|" => Vec.norm e


def is_linear (x y : a) (c: ℂ) [Vec a] (f: a → a): Prop 
  := f (c * x + y) = c * ( f x ) + f y 


-- Inner Product Space
section inner_product_space
variable (α: Type) [Vec α] 
axiom conjugate_symmetry : 
  ∀ x y : α, x ⬝ y = y ⬝ x
axiom linearity : 
  ∀ x y z: α, ∀ a: ℂ, 
  ((a * x) + y) ⬝ z = (a * (x ⬝ z)) + (y ⬝ z)
axiom positive_definite : 
  ∀ x : α, (Complex.abs (x ⬝ x)) ≥ 0 --FIXME
  -- ∀ x : α, ( Vec.is_zero x ) → ( Complex.abs (x ⬝ x) > 0 )
end inner_product_space

-- Normed space
section normed_space
variable (α: Type) [Vec α] 
axiom positive_definite_norm :
  ∀ x : α, ( Vec.norm x ) ≥ 0
axiom zero_norm :
  ∀ x : α, ( Vec.norm x = 0 ) ↔ ( x = Vec.zero ) 
axiom linearity_norm : 
  ∀ x : α, ∀ c : ℂ,  Vec.norm (c * x ) = c * (Vec.norm x)
axiom additivity :
  ∀ x y : α, Vec.norm ( x + y) ≤ Vec.norm x + Vec.norm y
end normed_space

noncomputable def lp_norm (p : ℝ ) (n : ℕ) (x : Vector ℝ n) : ℝ :=
  ( x.toList.foldl (fun acc xx => acc + (xx ^ p ) ) (0.0 : ℝ) ) ^ ( 1.0 / p )

-- #eval 0.5 ^ 0.5
-- #eval 0.5 ^ ((2 : ℝ)⁻¹ )