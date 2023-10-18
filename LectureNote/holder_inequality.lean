import LectureNote.Common

class Vec (a : Type) where
  add : a → a → a
  prod_s : ℂ → a → a
  prod_in : a → a → ℂ 

-- Declare infix notation for Vec operations
infixl:65 " + " => Vec.add
infixl:70 " * " => Vec.prod_s
infix:70 " ⬝ " => Vec.prod_in  

variable ( x y : α) [Vec α]
#check Complex.abs (x ⬝ x) ≥ 0


section Inner_Product_Space
variable (α: Type) [Vec α] 
axiom conjugate_symmetry : 
  ∀ x y : α, x ⬝ y = y ⬝ x
axiom linearity : 
  ∀ x y z: α, ∀ a: ℂ, 
  ((a * x) + y) ⬝ z = (a * (x ⬝ z)) + (y ⬝ z)
axiom positive_definite : 
  ∀ x : α, (Complex.abs (x ⬝ x)) ≥ 0 --FIXME
  -- ∀ x : α, ( Vec.is_zero x ) → ( Complex.abs (x ⬝ x) > 0 )
end Inner_Product_Space


-- Normed space

-- -- Holder's inequality
-- theorem holders_inequality :