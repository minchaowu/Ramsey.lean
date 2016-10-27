import lemmas_for_RT_n_m
open classical set nat decidable prod subtype

noncomputable theory

proposition ne_empty_of_card_pos {A : Type} {s : set A} (H : card s > 0) : s ≠ ∅ :=
take H', begin rewrite [H' at H, card_empty at H], exact lt.irrefl 0 H end

proposition insert_subset {A : Type} {s t : set A} {a : A} (amem : a ∈ t) (ssubt : s ⊆ t) : insert a s ⊆ t :=
take x, assume xias,
  or.elim (eq_or_mem_of_mem_insert xias)
    (by simp)
    (take H, ssubt H)

proposition eq_singleton_of_forall_eq {A : Type} {s : set A} {x : A} (xs : x ∈ s) (H : ∀₀ y ∈ s, y = x) : s = '{x} :=
ext (take y, iff.intro 
  (assume ys, mem_singleton_of_eq (H ys))  
  (assume yx, by rewrite (eq_of_mem_singleton yx); assumption))

lemma eq_of_card_eq_one {A : Type} {S : set A} (H : card S = 1) {x y : A} (Hx : x ∈ S) (Hy : y ∈ S) : x = y := 
have finS : finite S, 
  from by_contradiction (assume nfinS, begin rewrite (card_of_not_finite nfinS) at H, contradiction end), 
by_contradiction
(assume H0 : x ≠ y,
  have H1 : '{x, y} ⊆ S, from insert_subset Hx (insert_subset Hy (empty_subset _)),
  have x ∉ '{y}, from assume H, H0 (eq_of_mem_singleton H), 
  have 2 ≤ 1, from calc
    2 = card '{x, y} : by+ rewrite [card_insert_of_not_mem this, card_insert_of_not_mem (not_mem_empty _), card_empty]
      ... ≤ card S   : @card_le_card_of_subset _ _ _ _ finS H1
      ... = 1        : H,
  show false, from dec_trivial this)

proposition eq_singleton_of_card_eq_one {A : Type} {s : set A} {x : A} (H : card s = 1) (xs : x ∈ s) : s = '{x} := 
eq_singleton_of_forall_eq xs (take y, assume ys, eq.symm (eq_of_card_eq_one H xs ys))

proposition exists_eq_singleton_of_card_eq_one {A : Type} {s : set A} (H : card s = 1) : ∃ x, s = '{x} := 
have s ≠ ∅, from ne_empty_of_card_pos (by rewrite H; apply dec_trivial),
obtain (x : A) (xs : x ∈ s), from exists_mem_of_ne_empty this,
exists.intro x (eq_singleton_of_card_eq_one H xs)


section
parameter X : set ℕ
parameter c : set ℕ → ℕ
parameter Hinf : infinite X
parameter Hc : is_coloring X 1 2 c

definition c' (n : ℕ) := c '{n}


theorem finite_color_for_rt_1_2 (n : ℕ) (H : n ∈ X): c' n < 2 := 
have sub : '{n} ⊆ X, from 
  take x, assume Hx, 
  have x = n, from eq_of_mem_singleton Hx,
  by+ simp,
have card : card '{n} = 1, from card_singleton n,
have fin : finite '{n}, from finite_singleton,
have '{n} ∈ tuples X 1, from and.intro sub (and.intro card fin),
Hc this

theorem existence_of_unique_color : ∃ i, infinite {n ∈ X | c' n = i} := 
by_contradiction
(suppose ¬ ∃ i, infinite {n ∈ X | c' n = i}, 
have H : ∀ i, ¬ infinite {n ∈ X | c' n = i}, from (and.left forall_iff_not_exists) this,
have ¬ infinite {n ∈ X | c' n = 0}, from H 0,
have fin_zero : finite {n ∈ X | c' n = 0}, from dne this,
have ¬ infinite {n ∈ X | c' n = 1}, from H 1,
have fin_one : finite {n ∈ X | c' n = 1}, from dne this,
have fin : finite ({n ∈ X | c' n = 0} ∪ {n ∈ X | c' n = 1}), from @finite_union _ _ _ fin_zero fin_one,
have infinite ({n ∈ X | c' n = 0} ∪ {n ∈ X | c' n = 1}), from
  by_contradiction
  (suppose ¬ infinite ({n ∈ X | c' n = 0} ∪ {n ∈ X | c' n = 1}),
   have finite ({n ∈ X | c' n = 0} ∪ {n ∈ X | c' n = 1}), from dne this,
   have ({n ∈ X | c' n = 0} ∪ {n ∈ X | c' n = 1}) ⊆ X, from 
     λ a, λ Ha, or.elim Ha
     (λ Hl, and.left Hl)
     (λ Hr, and.left Hr),
   have ∃₀ x ∈ X, x ∉ ({n ∈ X | c' n = 0} ∪ {n ∈ X | c' n = 1}), from mem_of_infset Hinf this fin,
   obtain k h, from this,
   have neg : k ∉ ({n ∈ X | c' n = 0} ∪ {n ∈ X | c' n = 1}), from and.right h,
   have c' k < 2, from finite_color_for_rt_1_2 k (and.left h),
   have c' k = 0 ∨ c' k = 1, from lt_2_eq_0_or_1 this,
   have k ∈ ({n ∈ X | c' n = 0} ∪ {n ∈ X | c' n = 1}), from
     or.elim this
     (λ Hl, or.intro_left (k ∈ X ∧ c' k = 1) (and.intro (and.left h) Hl))
     (λ Hr, or.intro_right (k ∈ X ∧ c' k = 0) (and.intro (and.left h) Hr)),
   neg this),
this fin)

definition homoset := {n ∈ X | c' n = some existence_of_unique_color}

theorem inf_homoset : infinite homoset := some_spec existence_of_unique_color

theorem sub_of_X_for_rt_1_2 : homoset ⊆ X := λ a, λ Ha, and.left Ha

theorem critical_lemma_for_rt_1_2 (x : set ℕ) (H : x ∈ tuples homoset 1) : c x = some existence_of_unique_color :=
have cardx : card x = 1, from and.left (and.right H),
have subx : x ⊆ homoset, from and.left H,
have ∃ a, x = '{a}, from exists_eq_singleton_of_card_eq_one cardx,
obtain a h, from this,
have a ∈ homoset, from 
  have a ∈ '{a}, from mem_singleton a,
  have a ∈ x, by+ simp,
  subx this,
have c '{a} = some existence_of_unique_color, from and.right this,
by+ simp

lemma alt_form_of_the_critical_lemma_for_rt_1_2 : ∀₀ a ∈ tuples homoset 1, ∀₀ b ∈ tuples homoset 1, c a = c b :=
take a, assume Ha, take b, assume Hb,
have c a = some existence_of_unique_color, from critical_lemma_for_rt_1_2 a Ha,
have c b = some existence_of_unique_color, from critical_lemma_for_rt_1_2 b Hb,
by+ simp

theorem homo_homoset : is_homogeneous X c 1 2 homoset := 
and.intro Hc (and.intro sub_of_X_for_rt_1_2 alt_form_of_the_critical_lemma_for_rt_1_2)

theorem goal_of_rt_1_2 : ∃ s, s ⊆ X ∧ infinite s ∧ is_homogeneous X c 1 2 s :=
have homoset ⊆ X ∧ infinite homoset ∧ is_homogeneous X c 1 2 homoset, from and.intro sub_of_X_for_rt_1_2 (and.intro inf_homoset homo_homoset),
exists.intro homoset this

end

check goal_of_rt_1_2

-- The principal of infinite pigeon hole.

theorem RT_1_2 : ∀ X : set ℕ, ∀ c : set ℕ → ℕ, infinite X → is_coloring X 1 2 c → ∃ S, S ⊆ X ∧ infinite S ∧ is_homogeneous X c 1 2 S :=
take X, take c, assume Hinf, assume Hc,
goal_of_rt_1_2 X c Hinf Hc

check RT_1_2
