import lemmas_for_RT_n_m RT_1_2

open classical set nat decidable prod subtype

noncomputable theory

section

parameter X : set ℕ
parameter k : ℕ 
parameter c : set ℕ → ℕ

parameter Hinf : infinite X

parameter IH : (∀ X : set ℕ, ∀ c : set ℕ → ℕ, infinite X → is_coloring X (k+1) 2 c → ∃ S, S ⊆ X ∧ infinite S ∧ is_homogeneous X c (k+1) 2 S) 

parameter Hc : is_coloring X (k+2) 2 c

lemma X_neq_empty : X ≠ ∅ := infset_neq_empty Hinf

noncomputable definition pairs_n (n : ℕ) : ({x : ℕ | x ∈ X} × {x : set ℕ | infinite x ∧ x ⊆ X}) × (ℕ × (set ℕ → ℕ)) := 
nat.rec_on n
(let a := chooseleast X X_neq_empty in
have mem : a ∈ X, from least_is_mem X X_neq_empty,
have infinite X ∧ X ⊆ X, from and.intro Hinf (subset.refl X),
((tag a mem, tag X this),(0, c))
)
(λ pred p_n', 
let S_n' := elt_of (pr2 (pr1 p_n')) in
have infS_n' : infinite S_n', from and.left (has_property (pr2 (pr1 p_n'))),
have S_n' ≠ ∅, from infset_neq_empty infS_n',
let a_n' := elt_of (pr1 (pr1 p_n')) in
let c_n (S : set ℕ) : ℕ := c (insert a_n' S) in
have infSn'an' : infinite (S_n' \ '{a_n'}), from diff_of_infset_singleton S_n' a_n' infS_n',
have sub0 : S_n' ⊆ X, from and.right (has_property (pr2 (pr1 p_n'))),
have sub1 : S_n' \ '{a_n'} ⊆ X, from take b, assume Hb, have b ∈ S_n', from and.left Hb, sub0 this,
have is_coloring (S_n' \ '{a_n'}) (k+1) 2 c_n, from
  take x, assume xintuples,
  have cardx : card x = k+1, from and.left (and.right xintuples),
  have k+1 ≠ 0, from dec_trivial,
  have card x ≠ 0, by+ rewrite -cardx at this;exact this, 
  have finx : finite x, from nonzero_card_of_finite this,
  have a_n' ∉ x, from 
    by_contradiction
    (suppose ¬ a_n' ∉ x,
     have an'inx : a_n' ∈ x, from dne this,
     have x ⊆ S_n' \ '{a_n'}, from and.left xintuples,
     have Hpos : a_n' ∈ S_n' \ '{a_n'}, from mem_of_subset_of_mem this an'inx,
     have a_n' ∉ S_n' \ '{a_n'}, from mem_not_in_diff,
     this Hpos), -- if so, x is not a subset of S_n' \ '{a_n'}
  have card (insert a_n' x) = card x + 1, from @card_insert_of_not_mem _ _ _ finx this,
  have cardanx : card (insert a_n' x) = k+2, by+ rewrite cardx at this;exact this,
  have finins : finite (insert a_n' x), from 
    have k+2 ≠ 0, from dec_trivial,
    have card (insert a_n' x) ≠ 0, by+ rewrite -cardanx at this;exact this,
    nonzero_card_of_finite this,
  have insert a_n' x ⊆ X, from 
    take a, assume Ha, 
    or.elim Ha
    (λ Hl, have mem_a_n' : a_n' ∈ X, from has_property (pr1 (pr1 p_n')), 
     by+ rewrite -Hl at mem_a_n'; exact mem_a_n')
    (λ Hr, 
     have sub3 : x ⊆ S_n' \ '{a_n'}, from and.left xintuples,
     have x ⊆ X, from subset.trans sub3 sub1,
     this Hr),
  have insert a_n' x ∈ tuples X (k+2), from and.intro this (and.intro cardanx finins),
  Hc this, -- from Hc and definition of c_n.
have H0 : ∃ h, h ⊆ (S_n' \ '{a_n'}) ∧ infinite h ∧ is_homogeneous (S_n' \ '{a_n'}) c_n (k+1) 2 h,  from IH (S_n' \ '{a_n'}) c_n infSn'an' this,
let S_n := some H0 in
have S_n_spec : S_n ⊆ (S_n' \ '{a_n'}) ∧ infinite S_n ∧ is_homogeneous (S_n' \ '{a_n'}) c_n (k+1) 2 S_n, from some_spec H0,
have sub4 : S_n ⊆ (S_n' \ '{a_n'}), from proof and.left S_n_spec qed,
have infS_n : infinite S_n, from proof and.left (and.right S_n_spec) qed,
have nonempS_n : S_n ≠ ∅, from proof infset_neq_empty infS_n qed,
let a_n := chooseleast S_n nonempS_n in
let i_nminus1 := color_of_n_tuples c_n (k+1) S_n infS_n in
have sub_S_n : S_n ⊆ X, from proof subset.trans sub4 sub1 qed,
have propS_n : infinite S_n ∧ S_n ⊆ X, from proof  and.intro infS_n sub_S_n qed,
have a_n ∈ X, from 
  have a_n ∈ S_n, from least_is_mem S_n nonempS_n,
  proof sub_S_n this qed,
((tag a_n this, tag S_n propS_n),(i_nminus1, c_n))
)

noncomputable definition a_n (n : ℕ) : ℕ := elt_of (pr1 (pr1 (pairs_n n)))

noncomputable definition S_n (n : ℕ) : set ℕ := elt_of (pr2 (pr1 (pairs_n n)))

theorem infS_n (n : ℕ): infinite (S_n n) := and.left (has_property (pr2 (pr1 (pairs_n n))))

theorem subS_n (n : ℕ) : (S_n n) ⊆ X := and.right (has_property (pr2 (pr1 (pairs_n n))))

theorem nonempS_n (n : ℕ) : S_n n ≠ ∅ := infset_neq_empty (infS_n n)

definition c_n (n : ℕ) : set ℕ → ℕ := pr2 (pr2 ((pairs_n n)))

-- i_n returns the color of homogeneous set S_{n+1}, which is induced by a_n.
definition i_n (n : ℕ) : ℕ := pr1 (pr2 (pairs_n (n+1))) 

lemma fact_of_sub1 (n : ℕ): S_n n \ '{a_n n} ⊆ X := take x, assume Hx, 
have x ∈ S_n n, from and.left Hx,
(subS_n n) this

theorem nice_property1 (n : ℕ) : is_coloring (S_n n \ '{a_n n}) (k+1) 2 (c_n (n+1)) :=
  take x, assume xintuples,
  have cardx : card x = k+1, from and.left (and.right xintuples),
  have k+1 ≠ 0, from dec_trivial,
  have card x ≠ 0, by+ rewrite -cardx at this;exact this, 
  have finx : finite x, from nonzero_card_of_finite this,
  have a_n n ∉ x, from 
    by_contradiction
    (suppose ¬ a_n n ∉ x,
     have an'inx : a_n n ∈ x, from dne this,
     have x ⊆ S_n n \ '{a_n n}, from and.left xintuples,
     have Hpos : a_n n ∈ S_n n \ '{a_n n}, from mem_of_subset_of_mem this an'inx,
     have a_n n ∉ S_n n \ '{a_n n}, from mem_not_in_diff,
     this Hpos), -- if so, x is not a subset of S_n' \ '{a_n'}
  have card (insert (a_n n) x) = card x + 1, from @card_insert_of_not_mem _ _ _ finx this,
  have cardanx : card (insert (a_n n) x) = k+2, by+ rewrite cardx at this;exact this,
  have finins : finite (insert (a_n n) x), from 
    have k+2 ≠ 0, from dec_trivial,
    have card (insert (a_n n) x) ≠ 0, by+ rewrite -cardanx at this;exact this,
    nonzero_card_of_finite this,
  have insert (a_n n) x ⊆ X, from 
    take a, assume Ha, 
    or.elim Ha
    (λ Hl, have mem_a_n' : (a_n n) ∈ X, from has_property (pr1 (pr1 (pairs_n n))), 
     by+ rewrite -Hl at mem_a_n'; exact mem_a_n')
    (λ Hr, 
     have sub3 : x ⊆ S_n n \ '{a_n n}, from and.left xintuples,
     have x ⊆ X, from subset.trans sub3 (fact_of_sub1 n),
     this Hr),
  have insert (a_n n) x ∈ tuples X (k+2), from and.intro this (and.intro cardanx finins),
  Hc this -- from Hc and definition of c_n.

theorem S_n_refl (n : ℕ) (H : ∃ h, h ⊆ (S_n n \ '{a_n n}) ∧ infinite h ∧ is_homogeneous (S_n n \ '{a_n n}) (c_n (n+1)) (k+1) 2 h) : S_n (n+1) = some H := rfl

theorem nice_property2 (n : ℕ) : S_n (n+1) ⊆ (S_n n \ '{a_n n}) ∧ infinite (S_n (n+1)) ∧ is_homogeneous (S_n n \ '{a_n n}) (c_n (n+1)) (k+1) 2 (S_n (n+1)) := 
have infinite (S_n n \ '{a_n n}), from diff_of_infset_singleton (S_n n) (a_n n) (infS_n n),
have H0 : ∃ h, h ⊆ (S_n n \ '{a_n n}) ∧ infinite h ∧ is_homogeneous (S_n n \ '{a_n n}) (c_n (n+1)) (k+1) 2 h, from IH (S_n n \ '{a_n n}) (c_n (n+1)) this (nice_property1 n),
have inst : (some H0) ⊆ (S_n n \ '{a_n n}) ∧ infinite (some H0) ∧ is_homogeneous (S_n n \ '{a_n n}) (c_n (n+1)) (k+1) 2 (some H0), from some_spec H0,

have S_n (n+1) = some H0, from S_n_refl n H0, -- from rfl,
by+ rewrite -this at inst;exact inst

theorem sub_nice_property2 (n : ℕ) : is_homogeneous (S_n n \ '{a_n n}) (c_n (n+1)) (k+1) 2 (S_n (n+1)) := and.right (and.right (nice_property2 n))

theorem sub2_nice_property2 (n : ℕ) : ∀₀ a ∈ tuples (S_n (n+1)) (k+1), ∀₀ b ∈ tuples (S_n (n+1)) (k+1), (c_n (n+1)) a = (c_n (n+1)) b :=
and.right (and.right (sub_nice_property2 n))

lemma decreasing_S_n_aux (n : ℕ) : S_n (n+1) ⊆ S_n n :=
have S_n (n+1) ⊆ (S_n n \ '{a_n n}), from and.left (nice_property2 n),
take s, assume H, 
have s ∈ (S_n n \ '{a_n n}), from this H,
and.left this

lemma decreasing_S_n_aux2 (n : ℕ) : ∀ k, S_n (n+k+1) ⊆ S_n n := 
take k, 
nat.induction_on k
(decreasing_S_n_aux n)
(take k, assume indhyp,
have S_n (n+k+2) ⊆ S_n (n+k+1), from decreasing_S_n_aux (n+k+1),
subset.trans this indhyp)

theorem decreasing_S_n {a b : ℕ} (H : a < b): S_n b ⊆ S_n a := 
have ∃ k, a+1+k = b, from lt_elim H,
obtain k h, from this,
have sub : S_n (a+k+1) ⊆ S_n a, from decreasing_S_n_aux2 a k,
have a+k+1 = a+1+k, by+ simp,
have a+k+1 = b, by+ rewrite h at this;exact this,
by+ rewrite this at sub;exact sub

theorem decreasing_S_n' {a b : ℕ} (H : a ≤ b): S_n b ⊆ S_n a := 
have a < b ∨ a = b, from lt_or_eq_of_le H,
or.elim this
(assume H1 : a < b, decreasing_S_n H1)
(assume H2 : a = b, have S_n a ⊆ S_n a, from subset.refl (S_n a),
by+ simp)

theorem a_n_not_in_S_nplus1 (n : ℕ) : a_n n ∉ S_n (n+1) :=
by_contradiction
(suppose ¬ a_n n ∉ S_n (n+1),
have H1 : a_n n ∈ S_n (n+1), from dne this,
have S_n (n+1) ⊆ (S_n n \ '{a_n n}), from and.left (nice_property2 n),
have a_n n ∈ (S_n n \ '{a_n n}), from this H1,
have a_n n ∉ '{a_n n}, from and.right this,
this (mem_singleton (a_n n))
)

theorem a_n_refl (a : ℕ) : a_n (a+1) = chooseleast (S_n (a+1)) (nonempS_n (a+1)) := rfl

theorem value_of_S_0 : S_n 0 = X := rfl

theorem a_n_in_S_n (m : ℕ) : a_n m ∈ S_n m :=
by_cases
(suppose H : m = 0, 
have a_n 0 = chooseleast X X_neq_empty, from rfl,
have chooseleast X X_neq_empty ∈ X, from least_is_mem X X_neq_empty,
have S_n 0 = X, from value_of_S_0,
by+ simp)
(suppose H : m ≠ 0,
have ∃ a, m = a+1, from exists_eq_succ_of_ne_zero H,
obtain a h, from this,
have inf : infinite (S_n (a+1)), from infS_n (a+1),
have nonemp : S_n (a+1) ≠ ∅, from nonempS_n (a+1),
have eq : a_n (a+1) = chooseleast (S_n (a+1)) nonemp, from a_n_refl a,
have chooseleast (S_n (a+1)) nonemp ∈ S_n (a+1), from least_is_mem (S_n (a+1)) nonemp,
--have a_n (a+1) ∈ S_n (a+1), by+ simp,--by+ rewrite -eq at this;exact this,
by+ simp
--by+ rewrite -h at this;exact this
)


lemma minimality_of_a_n {x : ℕ} (n : ℕ) (H : x ∈ S_n n): a_n n ≤ x :=
by_cases
(suppose H1 : n = 0,
have a_n 0 = chooseleast X X_neq_empty, from rfl,
have H2 : ∀₀ b ∈ X, a_n 0 ≤ b, from minimality this, 
have x ∈ S_n 0, by+ rewrite H1 at H; exact H,
have x ∈ X, by+ rewrite value_of_S_0 at this;exact this, 
have a_n 0 ≤ x, from H2 this,
by+ simp)
(suppose H : n ≠ 0,
have ∃ a, n = a+1, from exists_eq_succ_of_ne_zero H,
obtain a h, from this,
have H' : x ∈ S_n (a+1), by+ rewrite h at H;exact H, -- blast fails here
have a_n (a+1) ∈ S_n (a+1), from a_n_in_S_n (a+1),
have a_n (a+1) = chooseleast (S_n (a+1)) (nonempS_n (a+1)), from rfl,
have ∀ x, x ∈ S_n (a+1) → a_n (a+1) ≤ x, from minimality this,
have a_n (a+1) ≤ x, from this x H',
by+ simp)

lemma property_of_a_n {n : ℕ} {x : ℕ} (H : x ∈ S_n (n+1)) : a_n n < x :=
have x ∈ S_n n, from (decreasing_S_n_aux n) H,
have le : a_n n ≤ x, from minimality_of_a_n n this,
have a_n n ≠ x, from
  by_contradiction
  (suppose ¬ a_n n ≠ x,
   have a_n n = x, from dne this,
   have neg : a_n n ∈ S_n (n+1), by+ simp,
   have a_n n ∉ S_n (n+1), from a_n_not_in_S_nplus1 n,
   this neg),
lt_of_le_of_ne le this

theorem strictly_increasing_a_n {a b : ℕ} (H : a < b) : a_n a < a_n b := 
have a+1 ≤ b, from (and.left (lt_iff_succ_le a b)) H,
have sub : S_n b ⊆ S_n (a+1), from decreasing_S_n' this,
have a_n b ∈ S_n b, from a_n_in_S_n b,
have a_n b ∈ S_n (a+1), from sub this,
property_of_a_n this

theorem eq_of_n_of_a_n {a b : ℕ} (H : a_n a = a_n b) : a = b := 
have ¬ a < b, from
  by_contradiction
  (suppose ¬ ¬ a < b,
   have a < b, from dne this,
   have a_n a < a_n b, from strictly_increasing_a_n this,
   have a_n a < a_n a, by+ simp,
   (lt.irrefl (a_n a)) this),
have H1 : b ≤ a, from le_of_not_gt this,
have ¬ b < a, from
  by_contradiction
  (suppose ¬ ¬ b < a,
   have b < a, from dne this,
   have a_n b < a_n a, from strictly_increasing_a_n this,
   have a_n b < a_n b, by+ simp,
   (lt.irrefl (a_n b)) this),
have H2 : a ≤ b, from le_of_not_gt this,
eq_of_le_ge H2 H1 

theorem c_n_refl (n : ℕ) (S : set ℕ) : (c_n (n+1)) S = c (insert (a_n n) S) := rfl

theorem nice_property3 (i : ℕ): color_of_n_tuples (c_n (i+1)) (k+1) (S_n (i+1)) (infS_n (i+1)) = i_n i := rfl

  section
  parameter i : ℕ

  lemma exists_mem_of_tuples : ∃ y, y ∈ tuples (S_n (i+1)) (k+1) :=
  have tuples (S_n (i+1)) (k+1) ≠ ∅, from tuples_of_infset_is_nonemp (infS_n (i+1)) (k+1),
  exists_mem_of_ne_empty this

  lemma refl_of_mem_in_tuples : some exists_mem_of_tuples ∈ tuples (S_n (i+1)) (k+1) :=
  some_spec exists_mem_of_tuples
  
  theorem color_lt_2 : color_of_n_tuples (c_n (i+1)) (k+1) (S_n (i+1)) (infS_n (i+1)) < 2 := 
  have color_of_n_tuples (c_n (i+1)) (k+1) (S_n (i+1)) (infS_n (i+1)) = (c_n (i+1)) (some exists_mem_of_tuples), from rfl,
  have (S_n (i+1)) ⊆ (S_n i\ '{a_n i}), from and.left (nice_property2 i),
  have tuples (S_n (i+1)) (k+1) ⊆ tuples (S_n i\ '{a_n i}) (k+1), from sub_tuples (S_n (i+1)) (S_n i\ '{a_n i}) this (k+1),
  have mem : (some exists_mem_of_tuples) ∈ tuples (S_n i\ '{a_n i}) (k+1), from this refl_of_mem_in_tuples,
  have ∀₀ a ∈ tuples (S_n i\ '{a_n i}) (k+1), (c_n (i+1)) a < 2, from nice_property1 i,
  have (c_n (i+1)) (some exists_mem_of_tuples) < 2, from this mem,
  by+ simp

  end

theorem finite_color (i : ℕ) : i_n i < 2 := 
have color_of_n_tuples (c_n (i+1)) (k+1) (S_n (i+1)) (infS_n (i+1)) = i_n i, from nice_property3 i,
have color_of_n_tuples (c_n (i+1)) (k+1) (S_n (i+1)) (infS_n (i+1)) < 2, from color_lt_2 i,
by+ simp

theorem exists_a_unique_color : ∃ i, infinite {x | i_n x = i} := 
by_contradiction
(suppose ¬ ∃ i, infinite {x | i_n x = i},
have H : ∀ i, ¬ infinite {x | i_n x = i}, from (and.left forall_iff_not_exists) this,
have ¬ infinite {x | i_n x = 0}, from H 0,
have fin_zero : finite {x | i_n x = 0}, from dne this,
have ¬ infinite {x | i_n x = 1}, from H 1,
have fin_one : finite {x | i_n x = 1}, from dne this,
have fin : finite ({x | i_n x = 0} ∪ {x | i_n x = 1}), from @finite_union _ _ _ fin_zero fin_one,
have infinite ({x | i_n x = 0} ∪ {x | i_n x = 1}), from 
  by_contradiction
  (suppose ¬ infinite ({x | i_n x = 0} ∪ {x | i_n x = 1}),
   have fin : finite ({x | i_n x = 0} ∪ {x | i_n x = 1}), from dne this,
   have ({x | i_n x = 0} ∪ {x | i_n x = 1}) ⊆ ω, from  λ a, λ Ha, natω a,
   have ∃₀ x ∈ ω, x ∉ ({x | i_n x = 0} ∪ {x | i_n x = 1}), from mem_of_infset infω this fin,
   obtain i h, from this,
   have neg : i ∉ ({x | i_n x = 0} ∪ {x | i_n x = 1}), from and.right h,
   have i_n i < 2, from finite_color i,
   have i_n i = 0 ∨ i_n i = 1, from lt_2_eq_0_or_1 this,
   have i ∈ ({x | i_n x = 0} ∪ {x | i_n x = 1}), from
     or.elim this
     (λ Hl, or.intro_left (i_n i = 1) Hl)
     (λ Hr, or.intro_right (i_n i = 0) Hr),
   neg this),
this fin)

definition index : set ℕ := {i | i_n i = some exists_a_unique_color}

theorem infindex : infinite index := some_spec exists_a_unique_color

definition target : set ℕ := a_n ' index

definition i_of_a_in_target (x : ℕ) : ℕ := if H : x ∈ target then 
have ∃ i, i ∈ index ∧ a_n i = x, from H,
some this else 0

definition index_of_target := i_of_a_in_target ' target

section
-- To handle the error of invalid local context.

parameter a : ℕ
parameter H : a ∈ target

lemma ex1 : ∃ i, i ∈ index ∧ a_n i = a := H

theorem refl_of_i_of_a_in_target : i_of_a_in_target a = some ex1 := if_pos H

theorem mem_of_index : some H ∈ index := and.left (some_spec H)

theorem refl_of_mem : a_n (i_of_a_in_target a) = a :=
have i_of_a_in_target a = some ex1, from if_pos H,
have some ex1 ∈ index ∧ a_n (some ex1) = a, from some_spec ex1,
have i_of_a_in_target a ∈ index ∧ a_n (i_of_a_in_target a) = a, by+ simp,
and.right this

theorem mem_of_index_of_target : ∃ i, i ∈ index_of_target ∧ a_n i = a := 
have a ∈ target ∧ i_of_a_in_target a = i_of_a_in_target a, from and.intro H rfl,
have ∃ k, k ∈ target ∧ i_of_a_in_target k = i_of_a_in_target a, from exists.intro a this,
have mem : i_of_a_in_target a ∈ index_of_target, from this,
have a_n (i_of_a_in_target a) = a, from refl_of_mem,
exists.intro (i_of_a_in_target a) (and.intro mem this)

end

lemma sub_of_index : index_of_target ⊆ index :=
take x, assume H,
have ∃ a, a ∈ target ∧ i_of_a_in_target a = x, from H,
obtain a h, from this,
have aintar : a ∈ target, from and.left h,
have i_of_a_in_target a = x, from and.right h,
have i_of_a_in_target a = some aintar, from refl_of_i_of_a_in_target a aintar,
have eq : x = some aintar, by+ simp,
have some aintar ∈ index, from mem_of_index a aintar,
show x ∈ index, by+ simp

theorem inftarget : infinite target :=
by_contradiction
(suppose ¬ infinite target,
have finite target, from dne this,
have finite index_of_target, from @finite_image _ _ i_of_a_in_target target this,
have ∃₀ k ∈ index, k ∉ index_of_target, from mem_of_infset infindex sub_of_index this,
obtain i' h, from this,
have negi' : i' ∉ index_of_target, from and.right h,
have neg : a_n i' ∉ target, from 
  by_contradiction
  (suppose ¬ a_n i' ∉ target,
   have a_n i' ∈ target, from dne this,
   have ∃ i, i ∈ index_of_target ∧ a_n i = a_n i', from mem_of_index_of_target (a_n i') this,
   obtain i h, from this,
   have a_n i = a_n i', from and.right h,
   have i = i', from eq_of_n_of_a_n this,
   have i ∈ index_of_target, from and.left h,
   have i' ∈ index_of_target, by+ simp,
   negi' this),
have i' ∈ index ∧ a_n i' = a_n i', from and.intro (and.left h) rfl,
have a_n i' ∈ target, from exists.intro i' this,
neg this)

theorem unique_i {i : ℕ} (H : a_n i ∈ target) : i_n i = some exists_a_unique_color := 
have ∃ x, x ∈ index ∧ a_n x = a_n i, from H,
obtain i' h, from this,
have a_n i' = a_n i, from and.right h,
have eq : i' = i, from eq_of_n_of_a_n this,
have i' ∈ index, from and.left h,
have i ∈ index, by+ rewrite eq at this;exact this,
this

lemma canonical_form {x : set ℕ} {y : ℕ} (H1 : x ∈ (tuples target (k+2))) (H2 : y ∈ x) : ∃ n, y = a_n n := 
have x ⊆ target, from and.left H1,
have y ∈ target, from this H2,
have ∃ z, z ∈ index ∧ a_n z = y, from this,
obtain i h, from this,
have a_n i = y, from and.right h,
have y = a_n i, by+ simp,
exists.intro i this -- by definition

lemma nonemp_mem_of_k2tuples {x : set ℕ} (H1 : x ∈ (tuples target (k+2))) : x ≠ ∅ :=
have cardx : card x = k+2, from and.left (and.right H1), 
  by_contradiction
  (suppose ¬ x ≠ ∅,
   have x = ∅, from dne this,
   have k+2 ≠ 0, from dec_trivial,
   have neq : card x ≠ 0, by+ rewrite -cardx at this;exact this,
   have card (∅ : set ℕ) = 0, from card_empty,
   have card x = 0, by+ simp,
   neq this)

lemma big_thing {x : set ℕ} (i : ℕ) (H1 : x ∈ (tuples target (k+2))) (H2 : x ≠ ∅) (H3 : a_n i = chooseleast x H2) (H4 : a_n i ∈ x) : (x \ '{a_n i}) ∈ tuples (S_n (i+1)) (k+1) :=
have cardx : card x = k+2, from and.left (and.right H1),
have finx : finite x, from and.right (and.right H1),
have sub : (x \ '{a_n i}) ⊆ S_n (i+1), from 
  take a, assume Ha,
  have H : ∀ y, y ∈ x → a_n i ≤ y, from minimality H3,
  have ainx : a ∈ x, from and.left Ha,
  have le : a_n i ≤ a, from H a ainx,
  have a_n i ≠ a, from by_contradiction
  (suppose ¬ a_n i ≠ a,
   have a_n i = a, from dne this,
   have Hin : a_n i ∈ (x \ '{a_n i}), by+ simp,
   have a_n i ∉ (x \ '{a_n i}), from mem_not_in_diff,
   this Hin),
  have a_n i < a, from lt_of_le_of_ne le this,
  have ∃ n, a = a_n n, from canonical_form H1 ainx,
  obtain i' h, from this,
  have i < i', from by_contradiction
    (suppose ¬ i < i',
     have i' < i ∨ i' = i, from lt_or_eq_of_not_le this,
     or.elim this
     (λ Hl, 
     have le2 : a_n i' < a_n i, from strictly_increasing_a_n Hl,
     have a_n i < a_n i', by+ simp,
     have ¬ a_n i' < a_n i, from not_lt_of_gt this,
     this le2)
     (λ Hr, --by+ simp works! I'm surprised because I don't think this is trivial enough.
     have eq : a_n i = a_n i', by+ simp,
     have a_n i ≠ a_n i', by+ simp,
     this eq) 
    ),
  have orinst : i+1 < i' ∨ i+1 = i', from succ_lt_or_eq_of_le this, 
  have a_n i' ∈ S_n (i+1), from
    or.elim orinst
    (λ Hl, 
     have Hl1 : a_n i' ∈ S_n i', from a_n_in_S_n i',
     have S_n i' ⊆ S_n (i+1), from decreasing_S_n Hl,
     this Hl1)
    (λ Hr, 
     have a_n (i+1) ∈ S_n (i+1), from a_n_in_S_n (i+1),
     by+ simp),
  by+ simp,
have notin : a_n i ∉ x \ '{a_n i}, from mem_not_in_diff,
have insert (a_n i) (x \ '{a_n i}) = x, from insert_of_diff_singleton H4,
have card (insert (a_n i) (x \ '{a_n i})) = k+2, by+ simp,
have fin : finite (x \ '{a_n i}), from 
  have x \ '{a_n i} ⊆ x, from λ a, λ Ha, and.left Ha, @finite_subset _ _ _ finx this,
have card : card (x \ '{a_n i}) = k+1, from 
  have card (insert (a_n i) (x \ '{a_n i})) = card (x \ '{a_n i}) + 1, from @card_insert_of_not_mem _ _ _ fin notin,
  have 1+1 = (2:ℕ), from dec_trivial,
  have (k+1)+1 = card (x \ '{a_n i}) + 1, by+ simp,
  have (k+1) = card (x \ '{a_n i}), from proof nat.add_right_cancel this qed,
  by+ simp,
and.intro sub (and.intro card fin)

section

parameter x : set ℕ
parameter H1 : x ∈ (tuples target (k+2))

theorem nonempx : x ≠ ∅ := nonemp_mem_of_k2tuples H1

definition amin := chooseleast x nonempx

theorem amin_in_x : amin ∈ x := least_is_mem x nonempx

theorem existence_of_index : ∃ n, amin = a_n n := canonical_form H1 amin_in_x

definition i := some existence_of_index

theorem eq_of_a_n_i : a_n i = chooseleast x nonempx :=
have amin = a_n i, from some_spec existence_of_index,
have amin = chooseleast x nonempx, from rfl,
by+ simp

theorem a_n_i_in_x : a_n i ∈ x :=
have amin = a_n i, from some_spec existence_of_index,
have amin ∈ x, from amin_in_x,
by+ simp

theorem fact_about_color : ∀₀ a ∈ tuples (S_n (i+1)) (k+1), ∀₀ b ∈ tuples (S_n (i+1)) (k+1), (c_n (i+1)) a = (c_n (i+1)) b := sub2_nice_property2 i

theorem existence_of_mem : ∃ y, y ∈ tuples (S_n (i+1)) (k+1) := 
have (x \ '{a_n i}) ∈ tuples (S_n (i+1)) (k+1), from big_thing i H1 nonempx eq_of_a_n_i a_n_i_in_x,
exists.intro (x \ '{a_n i}) this

theorem fact_about_color_of_n_tuples : color_of_n_tuples (c_n (i+1)) (k+1) (S_n (i+1)) (infS_n (i+1)) = (c_n (i+1)) (some existence_of_mem) := rfl

lemma fact_about_some_existence : some existence_of_mem ∈ tuples (S_n (i+1)) (k+1) :=
some_spec existence_of_mem

theorem eq_of_color : c_n (i+1) (x \ '{a_n i}) = color_of_n_tuples (c_n (i+1)) (k+1) (S_n (i+1)) (infS_n (i+1)) := 
have (x \ '{a_n i}) ∈ tuples (S_n (i+1)) (k+1), from big_thing i H1 nonempx eq_of_a_n_i a_n_i_in_x,
have c_n (i+1) (x \ '{a_n i}) = (c_n (i+1)) (some existence_of_mem), from fact_about_color this (fact_about_some_existence),
have color_of_n_tuples (c_n (i+1)) (k+1) (S_n (i+1)) (infS_n (i+1)) = (c_n (i+1)) (some existence_of_mem), from fact_about_color_of_n_tuples,
by+ simp

theorem eq_of_i_n : color_of_n_tuples (c_n (i+1)) (k+1) (S_n (i+1)) (infS_n (i+1)) = i_n i := nice_property3 i

theorem assoc_of_a_n_i_n : c_n (i+1) (x \ '{a_n i}) = i_n i := 
have eq : c_n (i+1) (x \ '{a_n i}) = color_of_n_tuples (c_n (i+1)) (k+1) (S_n (i+1)) (infS_n (i+1)), from eq_of_color,
have color_of_n_tuples (c_n (i+1)) (k+1) (S_n (i+1)) (infS_n (i+1)) = i_n i, from eq_of_i_n,
by+ rewrite this at eq;exact eq

theorem eq_of_cx : c x = i_n i :=
have insert (a_n i) (x \ '{a_n i}) = x, from insert_of_diff_singleton a_n_i_in_x,
have c x = c (insert (a_n i) (x \ '{a_n i})), by+ simp,
have c_n (i+1) (x \ '{a_n i}) = c (insert (a_n i) (x \ '{a_n i})), from c_n_refl i (x \ '{a_n i}),
have c x = c_n (i+1) (x \ '{a_n i}), by+ simp,
have c_n (i+1) (x \ '{a_n i}) = i_n i, from assoc_of_a_n_i_n,
by+ simp

theorem critical_lemma : c x = some exists_a_unique_color :=
have c x = i_n i, from eq_of_cx,
have x ⊆ target, from and.left H1,
have a_n i ∈ target, from this a_n_i_in_x,
have i_n i = some exists_a_unique_color, from unique_i this,
by+ simp

end

lemma alt_form_of_the_critical_lemma : ∀₀ a ∈ tuples target (k+2), ∀₀ b ∈ tuples target (k+2), c a = c b :=
take a, assume Ha, take b, assume Hb,
have c a = some exists_a_unique_color, from critical_lemma a Ha,
have c b = some exists_a_unique_color, from critical_lemma b Hb,
by+ simp

lemma mem_of_X (n : ℕ) : a_n n ∈ X :=  has_property (pr1 (pr1 (pairs_n n)))

lemma sub_of_X : target ⊆ X := 
take a, assume Ha, 
obtain i h, from Ha,
have a_n i ∈ X, from mem_of_X i,
have a_n i = a, from and.right h,
by+ simp

lemma homo_target : is_homogeneous X c (k+2) 2 target :=
and.intro Hc (and.intro sub_of_X alt_form_of_the_critical_lemma)

theorem goal : ∃ s, s ⊆ X ∧ infinite s ∧ is_homogeneous X c (k+2) 2 s :=
have target ⊆ X ∧ infinite target ∧ is_homogeneous X c (k+2) 2 target, from and.intro sub_of_X (and.intro inftarget homo_target),
exists.intro target this

end

check goal

theorem RT_n_2 : ∀ n : ℕ, ∀ X : set ℕ, ∀ c : set ℕ → ℕ, infinite X → is_coloring X (n+1) 2 c → ∃ S, S ⊆ X ∧ infinite S ∧ is_homogeneous X c (n+1) 2 S := 
take n,
nat.induction_on n
(RT_1_2)
(take n, assume IH,
take X, take c, assume HinfX, assume Hi,
--have succ_eq : succ n + 1 = n + succ 1, from succ_add_eq_succ_add n 1,
have succ 1 = 2, from dec_trivial,
have eq : succ n + 1 = n + 2, by+ rewrite -this,
have Hc : is_coloring X (n+2) 2 c, by+ rewrite eq at Hi; exact Hi,
have ∃ s, s ⊆ X ∧ infinite s ∧ is_homogeneous X c (n+2) 2 s, from goal X n c HinfX IH Hc,
by+ rewrite -eq at this;exact this)

check RT_n_2
