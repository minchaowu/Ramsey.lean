import data.set data.nat standard
open classical set nat decidable

-------- Definitions and Axioms --------

noncomputable theory

definition tuples {A : Type} (S : set A) (n : ℕ) : set (set A) := 
{ T : set A | T ⊆ S ∧ card T = n ∧ finite T}

lemma sub_tuples {A : Type} (S1 S2 : set A) (H : S1 ⊆ S2) (n : ℕ) : tuples S1 n ⊆ tuples S2 n := 
take x, assume H1, 
have x ⊆ S2, from subset.trans (and.left H1) H,
and.intro this (and.right H1)

theorem dne {p : Prop} (H : ¬¬p) : p := or.elim (em p) (assume Hp : p, Hp) (assume Hnp : ¬p, absurd Hnp H)

section

variable {A : Type}

abbreviation infinite (X : set A) : Prop := ¬ finite X

end

constant ω : set ℕ

axiom natω : ∀ x : ℕ, x ∈ ω

axiom infω : infinite ω

abbreviation is_coloring (X : set ℕ) (n : ℕ) (μ : ℕ) (c : set ℕ → ℕ) : Prop := ∀₀ a ∈ tuples X n, c a < μ
 
abbreviation is_homogeneous (X : set ℕ) (c : set ℕ → ℕ) (n μ : ℕ) (H : set ℕ) : Prop := is_coloring X n μ c ∧ H ⊆ X ∧ ∀₀ a ∈ tuples H n, ∀₀ b ∈ tuples H n, c a = c b 
