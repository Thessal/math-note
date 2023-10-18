import LectureNote.Common
import Mathlib.MeasureTheory.Measure.MeasureSpace -- Basic definitions related to measure spaces
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure


open ProbabilityMeasure
open Set
variable {α : Type} (P : Set α → ℝ) (MeasurableSet : Set α → Prop)

-----------
-- Define P
-----------
axiom P_nonneg : ∀ A, And (0 ≤ P A) (P A ≤ 1)
axiom P_norm : P univ = 1
axiom P_additivity (A B: Set α) : MeasurableSet A → MeasurableSet B → A ∩ B = ∅ → P A + P B = P (A ∪ B)

-- variable (h1 : MeasurableSet ∅) (h2 : MeasurableSet univ) (h3: ∅ ∩ univ = ∅ )
-- variable (h0: Set.univ univ)
-- #check P_additivity P MeasurableSet ∅ univ h1 h2 h3
-- #check P_norm P

-----------------------
-- Base properties of P
-----------------------
theorem P_zero (univ : Set α) (h0: Set.univ = univ)
 (h1 : MeasurableSet ∅ ) (h2: MeasurableSet univ) (h3: ∅ ∩ univ = ∅ ) (h4: ∅ ∪ univ = univ ): P ∅ = 0 :=
by
  have h_additivity := P_additivity P MeasurableSet ∅ univ h1 h2 h3
  have h_norm := P_norm P
  rw [h0] at h_norm
  rw [h_norm] at h_additivity
  rw [h4] at h_additivity
  linarith

variable (E : Set α )
theorem P_complement (h1: MeasurableSet E) (h2: MeasurableSet Eᶜ ) (h3: Eᶜ ∩  E  = ∅ ) (h4: Eᶜ ∪ E = Set.univ)
: (P (Eᶜ )) + (P E) = 1 :=
by
  have h_additivity := P_additivity P MeasurableSet Eᶜ E h2 h1 h3
  rw [h4] at h_additivity
  rw [P_norm P] at h_additivity
  linarith

theorem arith_greater (a : ℝ )(b:ℝ ): b ≥ 0 → a+b ≥ a := sorry
theorem P_include
  (h1: MeasurableSet A) (h2: MeasurableSet (B ∩ Aᶜ) )
  (h3: A ∩ (B ∩ Aᶜ ) = ∅ )
  (h4: A ⊂ B → (B = A ∪ B ∩ Aᶜ) )
: (A ⊂ B) → ((P A) ≤ (P B)) := by
  intro h
  have h6 := h4 h
  have h_additivity := P_additivity P MeasurableSet A (B ∩ Aᶜ) h1 h2 h3
  rw [←h6] at h_additivity
  have h7 := arith_greater (P A) (P (B ∩ Aᶜ))
  have p8 := h7 (P_nonneg P (B ∩ Aᶜ)).left
  simp [h_additivity] at p8
  linarith


-----------------
--Continuity of p
-----------------

-- limits of sequences of events
def events (α : Type) := ℕ → Set α
def is_increasing_seq (An : events α) : Prop := ∀ n m : ℕ, n ≤ m → An n ⊆ An m
def is_decreasing_seq (An : events α) : Prop := ∀ n m : ℕ, m ≤ n → An n ⊆ An m
def lim_inc (An: events α) (_ : is_increasing_seq An) : Set α := ⋃ n, An n
def lim_dec (An: events α) (_ : is_decreasing_seq An) : Set α := ⋃ n, An n

def probs : (events α) → (ℕ → ℝ) :=
  fun events n => P (events n)
def is_limit (a : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, abs (a n - l) < ε

theorem continuity
(An: events α)
(n: ℕ)
(h1: is_increasing_seq An)
: is_limit (probs P An) (P (lim_inc An h1)) := by
  sorry

-- Limit Superior of Events, Limit Inferior of Events, all but finite, infinitely open
def limsup (An : ℕ → Set α) : Set α := ⋂ n, ⋃ k ≥ n, An k -- abf
def liminf (An : ℕ → Set α) : Set α := ⋃ n, ⋂ k ≥ n, An k -- io

theorem lim_compare
(a b: ℝ)
(n : ℕ )
(An: events α)
(h1 : a = P (liminf An))
(h2 : is_limit (fun n => (P (An n))) b )
: a ≤ b := by sorry


--------------
-- Expectation
--------------
-- Integral

-- MGF

-- Markov inequality