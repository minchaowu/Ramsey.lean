import definitions lemmas_for_RT_n_m RT_1_2 RT_n_2
open classical set nat decidable

noncomputable theory

theorem RT_n_m (n m : ℕ) : ∀ X : set ℕ, ∀ c : set ℕ → ℕ, infinite X → is_coloring X (n+1) (m+2) c → ∃ S, S ⊆ X ∧ infinite S ∧ is_homogeneous X c (n+1) (m+2) S := 
nat.induction_on m
(take X, take c, assume H1, assume H2,
show ∃ S, S ⊆ X ∧ infinite S ∧ is_homogeneous X c (n+1) (0+2) S, from RT_n_2 n X c H1 H2)
(take m, assume IH, 
take X, take c, assume Hinf, assume Hic,
let c' (s : set ℕ) : ℕ := if c s = (m+(2:ℕ)) then (1:ℕ) else 0 in
have is_coloring X (n+1) 2 c', from
  take a, assume Ha,
  by_cases
  (suppose Hca : c a = m+2, 
    have Hcca : c' a = (1:ℕ),from if_pos Hca,
    by_contradiction
    (assume Hn : ¬ c' a < 2,
    have H12 : 1 < (2:ℕ), from dec_trivial,
    have ¬ 1 < (2:ℕ), by+ rewrite Hcca at Hn;exact Hn,
    this H12))
  (suppose Hnca : c a ≠ m+2,
    have Hcca : c' a = (0:ℕ),from if_neg Hnca,
    by_contradiction
    (assume Hn : ¬ c' a < 2,
    have H02 : 0 < (2:ℕ), from dec_trivial,
    have ¬ 0 < (2:ℕ), by+ rewrite Hcca at Hn;exact Hn,
    this H02)),
have ∃ S, S ⊆ X ∧ infinite S ∧ is_homogeneous X c' (n+1) 2 S, from RT_n_2 _ _ _ Hinf this,
obtain (H : set ℕ) (Hp : H ⊆ X ∧ infinite H ∧ is_homogeneous X c' (n+1) 2 H), from this,
have Hsub : H ⊆ X, from and.left Hp,
have HinfH : infinite H, from and.left (and.right Hp),
--show ∃ H, H ⊆ X ∧ infinite H ∧ is_homogeneous X c (n+1) (m+3) H, from
  by_cases
  (suppose Ha : ∀₀ a ∈ tuples H (n+1), c' a = 1, 
   have Hp1 : H ⊆ X, from and.left Hp,
   have ∀₀ a ∈ tuples H (n+1), ∀₀ b ∈ tuples H (n+1), c a = c b, from
     take a, assume Hta, take b, assume Htb,
     have Hc'a : c' a = 1, from Ha Hta,
     have (1:ℕ) ≠ 0, from dec_trivial,
     have Hcaneq0 : c' a ≠ 0, by+ rewrite -Hc'a at this;exact this, 
     have Hca : c a = m+2, from
       by_contradiction
       (assume Hc : c a ≠ m+2,
        have c' a = 0, from if_neg Hc,
        Hcaneq0 this),
     have Hc'b : c' b = 1, from Ha Htb,
     have (1:ℕ) ≠ 0, from dec_trivial,
     have Hcbneq0 : c' b ≠ 0, by+ rewrite -Hc'b at this;exact this, 
     have Hcb : c b = m+2, from
       by_contradiction
       (assume Hc : c b ≠ m+2,
        have c' b = 0, from if_neg Hc,
        Hcbneq0 this),
     begin+ rewrite -Hcb at Hca, exact Hca end,
   have is_homogeneous X c (n+1) (m+3) H, from  and.intro Hic (and.intro Hp1 this),
   have H ⊆ X ∧ infinite H ∧ is_homogeneous X c (n+1) (m+3) H, from and.intro Hsub (and.intro HinfH this),
   exists.intro H this)
  (suppose ¬∀₀ a ∈ tuples H (n+1), c' a = 1,
   have ∃₀ a ∈ tuples H (n+1), ¬ c' a = 1, by+ rewrite not_bounded_forall at this;exact this,
   obtain (a : set ℕ) (Hc'a1 : a ∈ tuples H (n+1) ∧ c' a ≠ 1), from this,
   have Hc'aneq1 : c' a ≠ 1, from and.right Hc'a1,
   have c a ≠ m+2, from
     by_contradiction
     (suppose ¬ c a ≠ m+2, 
      have c a = m+2, from dne this,
      have c' a = 1, from if_pos this,
      Hc'aneq1 this), 
   have Hc'aeq0 : c' a = 0, from if_neg this,
   have Hall0 : ∀₀ a ∈ tuples H (n+1), c' a = 0, from 
     take b, assume Hbt,
     have is_homogeneous X c' (n+1) 2 H, from and.right (and.right Hp),
     have ∀₀ a ∈ tuples H (n+1), ∀₀ b ∈ tuples H (n+1), c' a = c' b, from and.right (and.right this),
     have c' a = c' b, from this (and.left Hc'a1) Hbt,
     by+ rewrite this at Hc'aeq0;exact Hc'aeq0,
   have is_coloring H (n+1) (m+2) c, from 
     take d, assume Hdt,
     have Hcdneq : c d ≠ m+2, from 
       by_contradiction
       (suppose ¬ c d ≠ m+2,
        have c d = m+2, from dne this,
        have Hc'deq1 : c' d = 1, from if_pos this,
        have Hc'd0 : c' d = 0, from Hall0 Hdt,
        have (0:ℕ) ≠ 1, from dec_trivial,
        have c' d ≠ 1, by+ rewrite -Hc'd0 at this;exact this, 
        this Hc'deq1),
     have d ∈ tuples X (n+1), from sub_tuples H X (and.left Hp) (n+1) Hdt,
     have c d < m+3, from Hic this,
     have c d ≤ m+2, from le_of_lt_succ this,
     have c d < m+2 ∨ c d = m+2, from lt_or_eq_of_le this,
     or_resolve_left this Hcdneq,
   have ∃ S, S ⊆ H ∧ infinite S ∧ is_homogeneous H c (n+1) (m+2) S, from IH H c HinfH this,
   obtain (S : set ℕ) (HS : S ⊆ H ∧ infinite S ∧ is_homogeneous H c (n+1) (m+2) S), from this,
   have HsubS : S ⊆ X, from subset.trans (and.left HS) Hsub,
   have HinfS : infinite S, from and.left (and.right HS),
   have is_homogeneous H c (n+1) (m+2) S, from and.right (and.right HS),
   have ∀₀ a ∈ tuples S (n+1), ∀₀ b ∈ tuples S (n+1), c a = c b, from and.right (and.right this),
   have is_homogeneous X c (n+1) (m+3) S, from and.intro Hic (and.intro HsubS this),
   have S ⊆ X ∧ infinite S ∧ is_homogeneous X c (n+1) (m+3) S, from and.intro HsubS (and.intro HinfS this),
   exists.intro S this))

check RT_n_m
