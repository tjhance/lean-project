import project.identities
import tactic.linarith
import data.list

def balanced_aux : (list bool) → (ℕ) → Prop
    | [] 0 := true
    | [] (d + 1) := false
    | (tt :: l) d := balanced_aux l (d + 1)
    | (ff :: l) 0 := false
    | (ff :: l) (d + 1) := balanced_aux l d

def balanced (l : list bool) : Prop := balanced_aux l 0

def set_balanced (n : ℕ) : set (list bool) :=
    { l : list bool | list.length l = 2 * n ∧ balanced l }

def sum_to : (ℕ) → (ℕ → ℕ) → ℕ
    | 0 f := 0
    | (n+1) f := f n + sum_to n f

def catalan_aux : ℕ → ℕ → ℕ
    | b 0 := 1
    | 0 (n + 1) := 1 /- doesn't matter -/
    | (b + 1) (n + 1) := sum_to (n+1) (λ i,
        catalan_aux b i * catalan_aux b (n-i))
def catalan (n : ℕ) : ℕ :=
    catalan_aux n n

theorem catalan_recurrence : ∀ n ,
    catalan (n+1) = sum_to (n+1) (λ i , catalan i * catalan (n - i)) :=
    sorry

theorem balanced_recursor : ∀ (l : list bool) ,
    balanced l ↔ (∃ a b , balanced a ∧ balanced b ∧ l = tt :: a ++ ff :: b) :=
    sorry

/- split (A)B into A, B -/
def split_parens_aux : (list bool) → (ℕ) → (list bool × list bool)
| ([]) n := ([],[])
| (ff :: l) 0 := ⟨ [], [] ⟩ /- doesn't matter -/
| (ff :: l) 1 := ⟨ [], l ⟩
| (ff :: l) (d + 1) := let p := split_parens_aux l d in ⟨ ff :: p.1 , p.2 ⟩
| (tt :: l) (d) := let p := split_parens_aux l (d+1) in ⟨ tt :: p.1 , p.2 ⟩
def split_parens : (list bool) → (list bool × list bool)
| [] := ([],[]) /- doesn't matter -/
| (ff :: l) = split_parens_aux l 1
| (tt :: l) = ([],[]) /- doesn't matter -/

/- combined A, B into (A)B -/
def combine_parens (l : list bool) (m : list bool) : (list bool) :=
    tt :: l ++ ff :: m

theorem balanced_split_parens_1 : ∀ (l : list bool) ,
    balanced l -> balanced (split_parens l).1 := sorry

theorem balanced_split_parens_2 : ∀ (l : list bool) ,
    balanced l -> balanced (split_parens l).2 := sorry

theorem balanced_combine : ∀ (l : list bool) (m : list bool) ,
    balanced l →
    balanced m →
    balanced (combine_parens l m) := sorry

theorem split_parens_combine_parens : ∀ (l : list bool) (m : list bool) ,
    balanced l →
    balanced m →
    split_parens (combine_parens l m) = ⟨l, m⟩ := sorry

theorem combine_parens_split_parens : ∀ (l : list bool) ,
    balanced l →
    ¬(l = list.nil) → 
    combine_parens (split_parens l).1 (split_parens l).2 = l := sorry

theorem length_combine_parens : ∀ (l : list bool) (m : list bool) ,
    balanced l →
    balanced m →
    list.length (combine_parens l m) = list.length l + list.length m + 2
    := sorry

theorem even_length_of_balanced : ∀ (l : list bool) ,
    balanced l →
    2 ∣ list.length l
    := sorry

theorem length_split_parens_1_le : ∀ (l : list bool) ,
    balanced l →
    ¬(l = list.nil) →
    list.length (split_parens l).1 ≤ list.length l - 2

lemma catalan_set_eq_with_bound : ∀ (n:ℕ) ,
    {l : list bool | list.length l = 2 * (n + 1) ∧ balanced l} = 
    {l : list bool | list.length l = 2 * (n + 1) ∧ balanced l ∧
                     list.length (split_parens l).1 < 2*(n+1)} :=
begin
    intros , 
    apply set.ext ,
    intros , split ,
    {
        intros ,
        split ,
        cases a, assumption ,
        split ,
        cases a , assumption ,
        simp at a , cases a , 
        calc list.length (split_parens x).1 ≤ (list.length x) - 2
                : (begin
                    apply length_split_parens_1_le , assumption ,
                    apply not.intro , intros , subst x , simp at a_left , trivial ,
                  end)
            ... = 2 * n
                : (begin
                    rw a_left,
                    exact sorry ,
                  end)
            ... < 2 * (n + 1)
                : by linarith
    },
    {
        intros ,
        cases a , cases a_right , simp , split , assumption ,
        assumption ,
    }
end

theorem even_nat_lt : ∀ (n:ℕ) (m:ℕ) ,
    (n) < 2*(m + 1) → 
    ¬ ((n) = 2*m) →
    2 ∣ n → 
    n < 2*m := sorry

lemma catalan_set_induction : ∀ (n:ℕ) (i:ℕ) (a:ℕ) (b:ℕ) ,
    has_card {l : list bool | list.length l = 2 * (n + 1) ∧ balanced l ∧
                     list.length (split_parens l).1 < 2*i} a →
    has_card {l : list bool | list.length l = 2 * (n + 1) ∧ balanced l ∧
                     list.length (split_parens l).1 = 2*i} b →
    has_card {l : list bool | list.length l = 2 * (n + 1) ∧ balanced l ∧
                     list.length (split_parens l).1 < 2*(i+1)} (a+b) :=
begin
    intros ,
    apply card_split _ 
        {l : list bool | list.length l = 2 * (n + 1) ∧ balanced l ∧
                     list.length (split_parens l).1 < 2*i}
        {l : list bool | list.length l = 2 * (n + 1) ∧ balanced l ∧
                     list.length (split_parens l).1 = 2*i}
        a b ,
    {
        simp ,
        intros ,
        by_cases (list.length (split_parens x).1 = 2*i) ,
        {
            right , split, assumption, split, assumption, assumption ,
        },
        {
            left, split, assumption, split, assumption, 
            apply even_nat_lt ,
            assumption ,
            assumption ,
            apply even_length_of_balanced ,
            apply balanced_split_parens_1 ,
            assumption ,
        }
    },
    {
        simp , intros ,
        apply not.intro , intros , 
        rw a_8 at a_5 ,
        linarith ,
    },
    {
        assumption ,
    },
    {
        assumption ,
    },
end

lemma catalan_set_base : ∀ (n:ℕ) ,
    has_card {l : list bool | list.length l = 2 * (n + 1) ∧ balanced l ∧
                     list.length (split_parens l).1 < 2*0} 0 :=
begin
    intros,
    apply card_0 ,
    simp ,
end

lemma has_card_set_balanced_aux : ∀ bound n ,
    n < bound →
    has_card (set_balanced n) (catalan n)
| 0 n := sorry
| (bound+1) 0 :=
    begin
        intros ,
        rw [set_balanced, catalan] ,
        rw [catalan_aux] ,
        apply (card_1 _ []) ,
        simp ,
        intros , simp at a_1 , cases a_1 , cases y ; trivial ,
    end
| (bound+1) (n+1) :=
    begin
        intros , 
        rw catalan_recurrence ,
        rw set_balanced ,

        /- add the bound that the first part of the split is < 2*(n+1) -/
        rw catalan_set_eq_with_bound ,

        /- replace n+1 with j (why is this so annoying omg) -/
        have j' : (∃ j , j = n+1) , existsi (n+1), trivial, cases j', rename j'_w j ,
        have e : (
            {l : list bool | list.length l = 2 * (n + 1) ∧ balanced l ∧ list.length ((split_parens l).fst) < 2 * (n + 1)} =
            {l : list bool | list.length l = 2 * (n + 1) ∧ balanced l ∧ list.length ((split_parens l).fst) < 2 * j}) ,
        rw j'_h ,
        rw e ,
        clear e ,
        have e : (sum_to (n + 1) = sum_to j) , rw j'_h, rw e , clear e,
        have n_bound : (n+1) < (bound+1) := a , /- copy this -/
        have j_bound : j ≤ (n+1) := sorry ,
        clear a , clear j'_h ,

        /- do induction on j for the summation of the recursion -/
        induction j, 
        {
            rw [sum_to] ,
            apply catalan_set_base ,
        },
        {
            rw [sum_to] ,
            rw [@nat.add_comm (catalan j_n * catalan (n - j_n)) _] ,
            apply catalan_set_induction ,
            {
                apply j_ih ,
                calc j_n ≤ n + 1 : sorry , /- should be easy -/
            },
            {
                clear j_ih ,
                apply (card_product
                    {l : list bool | list.length l = 2 * j_n ∧      
                        balanced l}
                    {l : list bool | list.length l = 2 * (n - j_n) ∧      
                        balanced l}
                    _
                    (catalan j_n)
                    (catalan (n - j_n))
                    combine_parens
                 ) ,
                 {
                     simp, intros,
                     split ,
                     rw [combine_parens] , simp , rw a , rw a_2 ,
                     {
                        calc 1 + (1 + (2 * j_n + 2 * (n - j_n))) = 2 * (n + 1) : sorry
                     },
                     {
                         split,
                         apply balanced_combine , assumption, assumption ,
                         rw split_parens_combine_parens , simp , assumption ,
                         assumption, assumption,
                     }
                 },
                 {
                    simp, intros ,
                    existsi (split_parens z).1 ,
                    existsi (split_parens z).2 ,
                    apply combine_parens_split_parens ,
                    assumption ,
                    apply not.intro , intros , subst z , simp at a ,linarith , 
                 },
                 {
                    simp, intros , 
                    have e : (( x, y ) = ( x', y' )) := (
                    calc ( x, y ) = split_parens (combine_parens x y) :
                            (begin
                                rw split_parens_combine_parens ,
                                assumption, assumption ,
                            end)
                        ... = split_parens (combine_parens x' y') :
                            (begin
                                rw a_8 ,
                            end)
                        ... = ( x', y' ) :
                            (begin
                                rw split_parens_combine_parens ,
                                assumption, assumption ,
                            end)),
                    simp at e ,
                    assumption ,
                 },
                 {
                     apply (has_card_set_balanced_aux bound) ,
                     exact sorry /- should be easy -/
                 },
                 {
                     apply (has_card_set_balanced_aux bound) ,
                     exact sorry /- should be easy -/
                 },
            }
        }

    end

theorem has_card_set_balanced : ∀ n ,
    has_card (set_balanced n) (catalan n) :=
begin
    intros ,
    apply (has_card_set_balanced_aux (n+1) n) ,
    linarith ,
end

/-
def count_tt_prefix : ℕ → (list bool) -> ℕ
    | 0 l := 0
    | (i+1) [] := 0
    | (i+1) (ff :: l) := count_tt_prefix i l
    | (i+1) (tt :: l) := count_tt_prefix i l + 1
-/

def below_diagonal_path (n : ℕ) (l : list bool) :=
    list.length l = 2*n + 1 ∧
    count_tt l = n ∧
    (forall (i:ℕ) , 0 ≤ i → i ≤ (2*n + 1) →
        ((int.of_nat i) * (int.of_nat n) -
            (2*(int.of_nat n)+1) * (int.of_nat count_tt (list.take i l)) < 0))

def argmax : (ℕ → ℤ) → ℕ → ℕ
    | f 0 := 0
    | f (n+1) := if f (n+1) > f (argmax f n) then (n+1) else argmax f n

def best_point (n:ℕ) (l : list bool) :=
    argmax (λ i ,
        (int.of_nat n) * (int.of_nat i) -
            (2*(int.of_nat n) + 1) * (int.of_nat (count_tt (list.take i l)))
    ) (2*n)

def negate_rotation (n:ℕ) (i:ℕ) :=
    if i = 0 then 0 else n - i

def compose_rotation (n:ℕ) (i:ℕ) (j:ℕ) :=
    (i + j) % n

theorem negate_rotation_lt : ∀ (n:ℕ) (i:ℕ) ,
    0 < n → negate_rotation n i < n := sorry

theorem compose_rotation_lt : ∀ (n:ℕ) (i:ℕ) (j:ℕ) ,
    0 < n → compose_rotation n i j < n := sorry

theorem eq_0_of_compose_negate : ∀ (n:ℕ) (i:ℕ) (j:ℕ) ,
    i < n →
    j < n → 
    compose_rotation n (negate_rotation n i) j = 0 →
    i = j := sorry

theorem compose_compose_rotation {α : Type} : ∀ (l:list α) (i:ℕ) (j:ℕ) ,
    i < list.length l → 
    list.drop i
        (list.drop j l ++ list.take j l) ++
      list.take i
        (list.drop j l ++ list.take j l) =
    list.drop (compose_rotation (list.length l) i j) l ++
    list.take (compose_rotation (list.length l) i j) l := sorry

theorem negate_negate_rotation {α : Type} : ∀ (l:list α) (i:ℕ) ,
    i < list.length l → 
    list.drop (negate_rotation (list.length l) i)
        (list.drop i l ++ list.take i l) ++
      list.take (negate_rotation (list.length l) i)
        (list.drop i l ++ list.take i l) =
    l := sorry

theorem best_point_lt_length : ∀ (n : ℕ) (l : list bool) ,
    best_point n l < 1 + 2 * n := sorry

theorem below_diagonal_path_rotate_best_point : ∀ (n : ℕ) (l : list bool) ,
    list.length l = 2*n + 1 →
    count_tt l = n →
    below_diagonal_path n (list.drop (best_point n l) l ++
                           list.take (best_point n l) l) := sorry

theorem below_diagonal_path_ends_in_ff : ∀ (n : ℕ) (l : list bool) ,
    below_diagonal_path n l →
    (exists t , l = t ++ [ff] ∧ balanced t) := sorry

theorem below_diagonal_path_of_balanced : ∀ (n : ℕ) (l : list bool) ,
    list.length l = 2 * n →
    balanced l →
    below_diagonal_path n (l ++ [ff]) := sorry

theorem take_app {α : Type} : ∀ (a : list α) (b : list α) ,
    list.take (list.length a) (a ++ b) = a := sorry

theorem count_tt_app : ∀ (a : list bool) (b : list bool) ,
    (count_tt (a ++ b)) = (count_tt a) + (count_tt b) := sorry

theorem below_diagonal_rotation_is_0 : ∀ (n : ℕ) (l : list bool) (i : ℕ) ,
    i < (2*n + 1) →
    below_diagonal_path n l →
    below_diagonal_path n (list.drop i l ++ list.take i l) →
    i = 0 := sorry

theorem below_diagonal_rotations_eq : ∀ (n : ℕ) (l : list bool) (l' : list bool) (i : ℕ) (i' : ℕ) ,
    below_diagonal_path n l →
    below_diagonal_path n l' →
    i < 1 + 2 * n → 
    i' < 1 + 2 * n → 
    list.drop i l ++ list.take i l = list.drop i' l' ++ list.take i' l' → 
    l = l' ∧ i = i' :=
begin
    intros ,
    have e := (calc
        l = 
            list.drop (negate_rotation (1+2*n) i)
                (list.drop i l ++ list.take i l) ++
            list.take (negate_rotation (1+2*n) i)
                (list.drop i l ++ list.take i l) : by
                begin
                    rw [below_diagonal_path] at a ,
                    cases a ,
                    rw nat.add_comm at a_left ,
                    rw <- a_left ,
                    rw [negate_negate_rotation] ,
                    rw a_left , assumption ,
                end
        ... = 
            list.drop (negate_rotation (1+2*n) i)
                (list.drop i' l' ++ list.take i' l') ++
            list.take (negate_rotation (1+2*n) i)
                (list.drop i' l' ++ list.take i' l') : by rw a_4
        ... =
            list.drop (compose_rotation (1+2*n) (negate_rotation (1+2*n) i) i') l'
            ++
            list.take (compose_rotation (1+2*n) (negate_rotation (1+2*n) i) i') l' : by
            begin
                rw [below_diagonal_path] at a_1 ,
                cases a_1 ,
                rw nat.add_comm at a_1_left ,
                rw <- a_1_left ,
                rw [compose_compose_rotation] ,
                apply negate_rotation_lt ,
                rw a_1_left , linarith ,
            end
        ) ,
    have h : ((compose_rotation (1 + 2 * n) (negate_rotation (1 + 2 * n) i) i') = 0)
        :=
        (begin
            apply (below_diagonal_rotation_is_0 n l' _) ,
            rw nat.add_comm ,
            apply compose_rotation_lt , linarith ,
            assumption ,
            rw [<- e] , assumption ,
        end),
    rw h at e ,
    rw [list.drop, list.take] at e , simp at e ,
    split ,
    {
        assumption ,
    },
    {
        apply (eq_0_of_compose_negate (1+2*n)) ,
        assumption, assumption, assumption ,
    },
end

theorem has_card_set_below_diagonal_path_catalan : ∀ n ,
    has_card {l : list bool | below_diagonal_path n l} (catalan n) :=
begin
    intros ,
    apply (card_bijection (set_balanced n) _
        (catalan n)
        (λ l , l ++ [ff])) ,
    {
        rw set_balanced , simp , intros ,
        apply below_diagonal_path_of_balanced , assumption , assumption ,
    },
    {
        simp , intros ,
        existsi (list.take (2*n) y) ,
        have h := below_diagonal_path_ends_in_ff n y a ,
        cases h , cases h_h ,
        have e := (
            calc list.length h_w = list.length (h_w ++ [ff]) - list.length [ff] : 
                by simp 
            ... = list.length y - list.length [ff] : by subst y
            ... = list.length y - 1 : by simp
            ... = (2*n + 1) - 1 : (begin
                rw below_diagonal_path at * ,
                cases a, 
                rw a_left ,
            end)
            ... = (2 * n) : by simp
        ),
        have e2 := (
            calc list.take (2 * n) y = list.take (list.length h_w) y : by rw e
            ... = list.take (list.length h_w) (h_w ++ [ff]) : by subst y
            ... = h_w : by rw take_app
        ),
        rw e2 ,
        split , rw [set_balanced] , simp , split , assumption, assumption ,
        subst y ,
    },
    {
        rw set_balanced , simp , intros ,
        calc x = list.take (list.length x) (x ++ [ff]) : by rw take_app
        ... = list.take (list.length x') (x' ++ [ff]) : by rw [a, a_2, a_4]
        ... = x' : by rw take_app
    },
    {
        apply has_card_set_balanced
    },
end

theorem has_card_set_n_choose_k_catalan : ∀ n ,
    has_card (set_n_choose_k (2*n+1) n) (catalan n * (2*n+1)) :=
begin
    intros ,
    apply (card_product_nat
        {l : list bool | below_diagonal_path n l}
        (2*n + 1)
        (set_n_choose_k (2*n+1) n)
        (catalan n)
        (λ l , λ i , list.drop i l ++ list.take i l)
    ) ,
    {
        rw set_n_choose_k , simp , intros ,
        split ,
        rw below_diagonal_path at * , cases a ,
        rw a_left ,
        have e : min y (2 * n + 1) = y :=
            (begin
                apply min_eq_left , apply le_of_lt , rw nat.add_comm , assumption ,
            end),
        {
            calc 2 * n + 1 - y + min y (2 * n + 1) = 2 * n + 1 - y + y : by rw e
            ... = 2 * n + 1 : sorry
            ... = 1 + 2 * n : by apply nat.add_comm
        },
        {
            rw below_diagonal_path at a , cases a , cases a_right ,
            calc count_tt (list.drop y x ++ list.take y x)
                = count_tt (list.drop y x) + count_tt (list.take y x) : by rw count_tt_app
            ... = count_tt (list.take y x) + count_tt (list.drop y x) : by rw nat.add_comm
            ... = count_tt (list.take y x ++ list.drop y x) : by rw count_tt_app
            ... = count_tt x : sorry
            ... = n : by rw a_right_left
        },
    },
    {
        intros ,
        rw set_n_choose_k at * ,
        simp at a ,
        cases a ,
        simp ,
        existsi (list.drop (best_point n z) z ++ list.take (best_point n z) z) ,
        split ,
        {
            apply below_diagonal_path_rotate_best_point ,
            rw nat.add_comm , assumption ,
            assumption ,
        },
        existsi (negate_rotation (1+2*n) (best_point n z)) ,
        split ,
        {
            apply negate_rotation_lt , linarith ,
        },
        {
            rw [<- a_left] ,
            apply negate_negate_rotation ,
            rw a_left ,
            apply best_point_lt_length ,
        },
    },
    {
        simp , intros ,
        apply (below_diagonal_rotations_eq n x x' y y') ; assumption ,
    },
    {
        apply has_card_set_below_diagonal_path_catalan ,
    },
end