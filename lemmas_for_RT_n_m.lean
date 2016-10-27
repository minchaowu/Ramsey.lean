import definitions
open classical set nat decidable prod subtype

section
-- the least number principle.

lemma alt_of_wf {A : set ℕ}: ∀ n, n ∈ A → ∃₀ a ∈ A, ∀₀ b ∈ A, a ≤ b := 
take n,
nat.strong_induction_on n
(take n, assume IH, assume ninA,  
by_cases
(suppose ∃₀ m ∈ A,  m < n, 
obtain m (Hm : m ∈ A ∧ m < n), from this,
IH m (and.right Hm) (and.left Hm))
(suppose ¬ ∃₀ m ∈ A,  m < n, 
have ∀₀ m ∈ A,  ¬ m < n, by+ rewrite not_bounded_exists at this ; exact this,
have ∀ m, m ∈ A → n ≤ m, from λ m, λ HmA, le_of_not_gt (this HmA),
exists.intro n (and.intro ninA this)))

theorem wf_of_le (S : set ℕ) (H : S ≠ ∅) : ∃₀ a ∈ S, ∀₀ b ∈ S, a ≤ b :=
have ∃ x, x ∈ S, from exists_mem_of_ne_empty H,
obtain n (Hn : n ∈ S), from this,
alt_of_wf n Hn

noncomputable definition chooseleast (S : set ℕ) (H : S ≠ ∅) : ℕ := 
have ∃₀ a ∈ S, ∀₀ b ∈ S, a ≤ b, from wf_of_le S H,
some this

theorem least_is_mem (S : set ℕ) (H : S ≠ ∅) : chooseleast S H ∈ S := 
have H1 : ∃₀ a ∈ S, ∀₀ b ∈ S, a ≤ b, from wf_of_le S H,
have inS : some H1 ∈ S, from proof and.left (some_spec H1) qed,
have chooseleast S H = some H1, from rfl,
by+ rewrite -this at inS ; exact inS

theorem minimality {S : set ℕ} {a : ℕ} {H0 : S ≠ ∅} (H : a = chooseleast S H0): 
∀₀ x ∈ S, a ≤ x :=
take b, assume Hb,
have H1 : ∃₀ n ∈ S, ∀₀ m ∈ S, n ≤ m, from wf_of_le S H0,
have chooseleast S H0 = some H1, from rfl,
have eq : a = some H1, by+ rewrite this at H;exact H,
have ∀₀ m ∈ S, some H1 ≤ m, from proof and.right (some_spec H1) qed, 
have some H1 ≤ b, from this Hb,
by+ simp 

end

section

lemma infset_neq_empty {A : Type} {S : set A} (H : infinite S) : S ≠ ∅ := 
by_contradiction
(suppose H1 : ¬ S ≠ ∅,
have finemp : finite (∅ : set A), from finite_empty,
have S = (∅ : set A), from dne H1,
have finite S, by+ rewrite -this at finemp;exact finemp,
H this)

lemma nonzero_card_of_finite {A : Type} {S : set A} (H : card S ≠ 0) : finite S :=
by_contradiction
(suppose ¬ finite S,
have card S = 0, from card_of_not_finite this,
H this)

lemma mem_not_in_diff {A : Type} {S : set A} {a : A} : a ∉ S \ '{a} := 
by_contradiction
(suppose ¬ a ∉ S \ '{a},
have a ∈ S \ '{a}, from dne this,
have a ∉ '{a}, from not_mem_of_mem_diff this,
this (mem_singleton a))

lemma insert_of_diff_singleton {A : Type} {S : set A} {a : A} (H : a ∈ S) : insert a (S \ '{a}) = S :=
ext
(take x, iff.intro
  (assume H1, 
   or.elim H1
   (λ Hl, by+ simp)
   (λ Hr, and.left Hr))
  (assume H2,
   by_cases
   (suppose x = a, or.intro_left (x ∈ S \ '{a}) this)
   (suppose neq : x ≠ a, 
    have x ∉ '{a}, from by_contradiction 
     (suppose ¬ x ∉ '{a}, 
      have x ∈ '{a}, from dne this,
      have x = a, from eq_of_mem_singleton this,
      neq this),
    have x ∈ S \ '{a}, from and.intro H2 this,
    or.intro_right (x = a) this))
)


lemma union_of_diff_singleton {A : Type} {S : set A} {a : A} (H : a ∈ S) : S \ '{a} ∪ '{a} = S := 
ext
(take x, iff.intro
(assume H1, 
  or.elim H1
  (assume Hl, and.left Hl)
  (assume Hr, 
   have x = a, from (and.left (mem_singleton_iff x a)) Hr,
   show x ∈ S, by+ rewrite -this at H;exact H))
(assume H2,
  by_cases
  (suppose x ∈ '{a}, or.intro_right (x ∈ S \ '{a}) this)
  (suppose x ∉ '{a}, 
   have x ∈ S \ '{a}, from and.intro H2 this,
   or.intro_left (x ∈ '{a}) this))
)

lemma finite_singleton {A : Type} {a : A} : finite '{a} := 
have carda : card '{a} = 1, from card_singleton a,
have (1:ℕ) ≠ 0, from dec_trivial,
have card '{a} ≠ 0, by+ rewrite -carda at this;exact this,
nonzero_card_of_finite this

lemma diff_of_infset_singleton {A : Type} (S : set A) (a : A) (H : infinite S): infinite (S \ '{a}) := 
by_contradiction
(suppose ¬ infinite (S \ '{a}),
 have fin : finite (S \ '{a}), from dne this,
 by_cases
 (suppose a ∈ S, 
  have eq : S \ '{a} ∪ '{a} = S, from union_of_diff_singleton this,
  have finite '{a}, from finite_singleton,
  have finite (S \ '{a} ∪ '{a}), from @finite_union _ _ _ fin this,
  have finite S, by+ rewrite eq at this;exact this,
  H this)
(suppose Hneg : a ∉ S, 
 have S ⊆ S \ '{a}, from
   take x, assume Hx,
   have x ∉ '{a}, from
     by_contradiction
     (suppose ¬ x ∉ '{a}, 
      have x ∈ '{a}, from dne this,
      have x = a, from (and.left (mem_singleton_iff x a)) this,
      have a ∈ S, by+ rewrite this at Hx ; exact Hx,
      Hneg this),
   and.intro Hx this,
 have finite S, from @finite_subset _ _ _ fin this, 
 H this)
) 

lemma sub_of_eq {A : Type} {S T: set A} (H : S = T) : S ⊆ T :=
have T ⊆ T, from subset.refl T,
by+ rewrite -H at this{1};exact this

theorem ne_empty_of_mem' {X : Type} {s : set X} {x : X} (H : x ∈ s) : s ≠ ∅ :=
begin intro Hs, rewrite Hs at H, apply not_mem_empty _ H end --this is on github

lemma mem_of_infset {S S': set ℕ} (H1 : infinite S) (H2 : S' ⊆ S) (H3 : finite S') : ∃₀ x ∈ S,  x ∉ S' := 
by_contradiction
(suppose ¬ ∃₀ x ∈ S, x ∉ S',
have ∀₀ x ∈ S, ¬ x ∉ S', by+ rewrite not_bounded_exists at this;exact this,
have S ⊆ S', from
  take s, assume Hs,
  have ¬ s ∉ S', from this Hs,
  dne this,
have finite S, from finite_subset this,
H1 this)

lemma tuples_of_infset_is_nonemp {S : set ℕ} (H : infinite S) (n : ℕ) : tuples S n ≠ ∅ := 
nat.induction_on n
(have sub : ∅ ⊆ S, from empty_subset S,
have finemp : finite ∅, from finite_empty,
have card (∅ : set ℕ) = 0, from card_empty,
have ∅ ∈ tuples S 0, from and.intro sub (and.intro this finemp),
ne_empty_of_mem' this)
(take a, assume indhyp,
have ∃ y, y ∈ tuples S a, from exists_mem_of_ne_empty indhyp,
obtain s h, from this,
have sub : s ⊆ S, from and.left h,
have card s = a, from and.left (and.right h),
have fins : finite s, from and.right (and.right h),
have ∃₀ x ∈ S,  x ∉ s, from mem_of_infset H sub fins,
obtain k h, from this,
have sub' : insert k s ⊆ S, from 
  take k', assume Hk',
  or.elim Hk' 
  (λ H1, have k ∈ S, from and.left h,
   by+ rewrite -H1 at this;exact this) 
  (λ H2, sub H2),
have k ∉ s, from and.right h,
have card (insert k s) = card s + 1, from @card_insert_of_not_mem _ _ _ fins this,
have fin : finite (insert k s), from @finite_insert _ _ _ fins,
have card (insert k s) = a+1, by+ simp,
have insert k s ∈ tuples S (a+1), from and.intro sub' (and.intro this fin),
ne_empty_of_mem' this) 

noncomputable definition color_of_n_tuples (c : set ℕ → ℕ) (n : ℕ) (S : set ℕ) (H : infinite S): ℕ := 
have tuples S n ≠ ∅, from tuples_of_infset_is_nonemp H n,
have H1 : ∃ H0, H0 ∈ tuples S n, from exists_mem_of_ne_empty this,
c (some H1)

theorem eq_of_le_ge {a b : ℕ} (H1 : a ≤ b) (H2 : b ≤ a) : a = b := 
by_contradiction
(suppose a ≠ b,
have a < b, from lt_of_le_of_ne H1 this,
le_lt_antisymm H2 this)

theorem lt_or_eq_of_not_le {a b : ℕ} (H : ¬ a < b) : b < a ∨ b = a :=
have b ≤ a, from le_of_not_gt H,
lt_or_eq_of_le this

theorem succ_lt_or_eq_of_le {a b : ℕ} (H : a < b) : a+1 < b ∨ a+1 = b :=
have a+1 ≤ b, from (and.left (lt_iff_succ_le a b)) H,
lt_or_eq_of_le this

theorem lt_2_eq_0_or_1 {a : ℕ} (H : a < 2) : a = 0 ∨ a = 1 :=
have a ≤ 1, from (and.left (lt_succ_iff_le a 1)) H,
have a < 1 ∨ a = 1, from (and.left le_iff_lt_or_eq) this,
or.elim this
(λ Hl, 
have a ≤ 0, from (and.left (lt_succ_iff_le a 0)) Hl,
have Hl1 : a < 0 ∨ a = 0, from (and.left le_iff_lt_or_eq) this,
have ¬ a < 0, from dec_trivial,
have a = 0, from or_resolve_right Hl1 this,
or.intro_left (a = 1) this)
(λ Hr, or.intro_right (a = 0) Hr)  
 
end
