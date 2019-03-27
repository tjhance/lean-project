import data.nat.choose
import data.set
import data.set.finite
import data.multiset
import data.list

--import classical

#check set
#check finset ℕ 
#check @finset.mk
#check choose 5 4

/- Collaboration between
   Travis Hance (thance)
   Katherine Cordwell (kcordwell)
-/

/- Our plan is to prove various combinatorial identities.
In paritcular,

 - Vandermonde's identity (Katherine's focus)
 - the Hockeystick identity (Katherine's focus)
 - the catalan identity: that the catalan numbers, as defined
    by the usual recurrence, equals (1/(n+1))*(2n+1 choose n). (Travis's focus)

For some or all of these, we will use combinatorial bijections.
-/

/-
    Machinery for bijective proofs.
    `has_card` is a Prop that indicates a set is finite
    and has a certain cardinality.

    Below are several theorems for using a bijection
    between multiple sets to establish a relation between their
    sizes. (Both Travis and Katherine's focus)
-/

def has_card {α : Type} (s : set α) (n : ℕ) : Prop :=
    ∃ l : (list α) , list.length l = n ∧ (∀ x : α , x ∈ s ↔ x ∈ l)
            ∧ list.nodup l

theorem card_bijection
    {α : Type} {β : Type}
        (A : set α) (B : set β) (a : ℕ)
        (f : (α → β)) :
    (∀ (x:α) , x ∈ A → f x ∈ B) →
    (∀ y , y ∈ B → ∃ x , x ∈ A ∧ f x = y) →
    (∀ x x' , x ∈ A → x' ∈ A → f x = f x' → x = x') →
    has_card A a →
    has_card B a := begin
    assume A1 A2 A3 h4,
    simp[has_card],
    have exh: ∃ L: (list α) , list.length L = a ∧ (∀ x : α , x ∈ A ↔ x ∈ L)
            ∧ list.nodup L, from h4,
    apply exists.elim exh,
    {
        assume L, assume hL: list.length L = a ∧ (∀ x : α , x ∈ A ↔ x ∈ L)
            ∧ list.nodup L,
        have nodupL: list.nodup L, from and.right (and.right hL),
        have iffL: (∀ x : α , x ∈ A ↔ x ∈ L), from and.left (and.right hL),
        have lengthHyp: list.length L = a, from and.left hL,
        let fL: list β := list.map f L,
        have B1: list.length fL = a, from sorry,
        have B2: (∀ x : β , x ∈ B ↔ x ∈ fL), from sorry,
        have h: ∀ x ∈ A, ∀ y ∈ A, f x = f y → x = y, begin intros, exact A3 x y H H_1 a_1 end,  
        have h1: ∀ x ∈ L, ∀ y ∈ L, f x = f y → x = y, 
            begin 
                intros, have h1: x ∈ A, from iff.elim_right(iffL x) H, 
                have h2: y ∈ A, from iff.elim_right(iffL y) H_1,
                exact A3 x y h1 h2 a_1
            end,  
        have h2: list.nodup (list.map f L), from list.nodup_map_on h1 nodupL,
        have B3: list.nodup fL, from h2,
        exact ⟨fL, and.intro B1 (and.intro B2 B3)⟩,
    }
    end

theorem card_split
    {α : Type} (A : set α) (B : set α) (C : set α) (b : ℕ) (c : ℕ) :
    (∀ x , x ∈ B → x ∈ A) →
    (∀ x , x ∈ C → x ∈ A) →
    (∀ x , x ∈ A → (x ∈ B ∨ x ∈ C)) → 
    (∀ x , ¬ (x ∈ B ∧ x ∈ C)) → 
    has_card B b ->
    has_card C c ->
    has_card A (b+c) :=
begin
    intros,
    rw [has_card] at * ,
    cases a_4, cases a_5 ,
    rename a_4_w l1 , rename a_5_w l2 ,
    cases a_4_h , cases a_5_h ,
    cases a_4_h_right, cases a_5_h_right,
    existsi (l1 ++ l2) ,
    split ,
    simp , subst b , subst c ,
    split ,
    intros ,
    split ,
    intros ,
    have b_or_c := a_2 x a_4 ,
    cases b_or_c ,
    have x_in_l1 := (iff.elim_left (a_4_h_right_left x)) b_or_c ,
    simp , left , assumption , 
    have x_in_l2 := (iff.elim_left (a_5_h_right_left x)) b_or_c ,
    simp , right , assumption , 
    intros ,
    simp at a_4 ,
    cases a_4 ,
    exact (a x (iff.elim_right (a_4_h_right_left x) a_4)) ,
    exact (a_1 x (iff.elim_right (a_5_h_right_left x) a_4)) ,
    apply list.nodup_append_of_nodup , assumption, assumption ,
    rw list.disjoint_iff_ne ,
    intros , apply not.intro , intros ,
    rename b_1 x , rw a_5 at * ,
    have x_in_b := (iff.elim_right (a_4_h_right_left x) H) ,
    have x_in_c := (iff.elim_right (a_5_h_right_left x) H_1) ,
    have x_in_b_and_x_in_c := and.intro x_in_b x_in_c ,
    have not_x_in_b_and_x_in_c := a_3 x ,
    contradiction ,
end

theorem card_split_map
    {α : Type} {β : Type} {γ : Type}
        (A : set α) (B : set β) (C : set γ) (b : ℕ) (c : ℕ)
        (f : (β → α)) (g : (γ → α)) : 
    (∀ y , y ∈ B → f y ∈ A) →
    (∀ z , z ∈ C → g z ∈ A) → 
    (∀ x , x ∈ A → (∃ y:β , y ∈ B ∧ f y = x) ∨ (∃ z:γ , z ∈ C ∧ g z = x)) → 
    (∀ y z , (y ∈ B → z ∈ B → f y = f z → y = z )) →
    (∀ y z , (y ∈ C → z ∈ C → g y = g z → y = z )) →
    (∀ y z , (y ∈ B → z ∈ C → f y = g z → false)) →
    has_card B b ->
    has_card C c ->
    has_card A (b+c) :=
begin
    intros ,
    apply (card_split A
        { x : α | ∃ y , y ∈ B ∧ f y = x }
        { x : α | ∃ z , z ∈ C ∧ g z = x }
        b c) ,
    {
        intros , simp at a_8 , cases a_8 , rename a_8_w y ,
        cases a_8_h , subst x , apply (a y) , assumption ,
    },
    {
        intros , simp at a_8 , cases a_8 , rename a_8_w z ,
        cases a_8_h , subst x , apply (a_1 z) , assumption ,
    },
    {
        simp, intros, apply (a_2 x) , assumption ,
    },
    {
        intros , apply not.intro , simp , intros , 
        exact (a_5 x_1 x_2 a_8 a_10 (begin
            rw a_9 , rw a_11 ,
        end)) ,
    },
    {
        apply (card_bijection
            B
            {x : α | ∃ (y : β), y ∈ B ∧ f y = x}
            b f
        ),
        intros , simp , existsi x , split, assumption, trivial,
        intros , simp at a_8 , cases a_8 , existsi a_8_w , assumption ,
        intros , exact (a_3 x x' a_8 a_9 a_10) ,
        assumption ,
    },
    {
        apply (card_bijection
            C
            {x : α | ∃ (z : γ), z ∈ C ∧ g z = x}
            c g
        ),
        intros , simp , existsi x , split, assumption, trivial,
        intros , simp at a_8 , cases a_8 , existsi a_8_w , assumption ,
        intros , exact (a_4 x x' a_8 a_9 a_10) ,
        assumption ,
    },
end

theorem card_0
    {α : Type} (A : set α) :
    (∀ (y:α) , y ∈ A → false) →
    has_card A 0 := 
    begin
    intro h,
    have h0: list.length ([]: list α) = 0, by rw[list.length],
    have h1: (∀ x : α , x ∈ A ↔ x ∈ ([]: list α)), 
        by {intro x, split, 
            {intro xh, apply h x xh},
            intro xh, simp at xh, contradiction},
    have h2: list.nodup ([]: list α), by simp,
    exact ⟨([]: list α), and.intro h0 (and.intro h1 h2)⟩ 
    end

theorem card_1
    {α : Type} (A : set α) (x : α) :
    (x ∈ A) →
    (∀ (y:α) , y ∈ A → x = y) →
    has_card A 1 := 
    begin
    intro h,
    intro hall,
    have h0: list.length (x::[]) = 1, by simp,
    have h1: (∀ z : α , z ∈ A ↔ z ∈ (x::[])), 
        by {intro z, split, 
            {intro zh, have newh: x = z, by apply hall z zh, simp *},
            intro zh, simp at zh, simp *},
    have h2: list.nodup (x::[]), by simp,
    exact ⟨(x::[]), and.intro h0 (and.intro h1 h2)⟩
    end

theorem set_induct
    {α : Type} (A : set α) (a:ℕ) :
    has_card A (a+1) →
    (∃ (x:α) (A':set α) ,
        has_card A' a ∧
        ¬ (x ∈ A') ∧
        A = { x' : α | x' ∈ A' ∨ x' = x }
    ) :=
begin
    intros , rw [has_card] at a_1 , cases a_1 , rename a_1_w l ,
    cases a_1_h ,
    cases l , simp at a_1_h_left , contradiction ,
    existsi l_hd ,
    existsi { x : α | x ∈ A ∧ ¬ (x = l_hd)} ,
    split ,
    {
        rw [has_card] , existsi l_tl ,
        split , simp at a_1_h_left , rw add_comm at a_1_h_left ,
        rw add_right_cancel_iff at a_1_h_left , assumption ,
        cases a_1_h_right ,
        split ,
        intros ,
        split ,
        simp , intros ,
        have x_in_l := iff.elim_left (a_1_h_right_left x) a_1,
        simp at x_in_l , cases x_in_l , contradiction , assumption ,
        simp , intros ,
        split ,
        exact (iff.elim_right (a_1_h_right_left x) (begin
                simp, right, assumption,
            end)),
        rw [list.nodup_cons] at a_1_h_right_right ,
        apply not.intro , intros , rw a_2 at * , cases a_1_h_right_right ,
        contradiction ,
        rw [list.nodup_cons] at a_1_h_right_right ,
        cases a_1_h_right_right , assumption ,
    },
    split ,
    {
        simp ,
    },
    {
        apply set.ext ,
        intros ,
        split ,
        {
            intros , simp , 
            /- TODO don't actually need classical here
               (could prove this with x ∈ l_hd :: l_tl
               and list.nodup (l_hd :: l_tl) instead) -/
            have c := classical.em (x = l_hd) ,
            cases c ,
            right , assumption ,
            left , split , assumption, assumption,
        },
        {
            simp , intros ,
            cases a_1 ,
            cases a_1 , assumption ,
            cases a_1_h_right , 
            exact (iff.elim_right (a_1_h_right_left x) (begin
                rw a_1 , simp , 
            end)),
        }
    }
end

theorem card_product
    {α : Type} {β : Type} {γ : Type}
        (A : set α) (B : set β) (C : set γ) (a : ℕ) (b : ℕ)
        (f : α → β → γ) :
    (∀ x y , x ∈ A → y ∈ B → f x y ∈ C) →
    (∀ z , z ∈ C → ∃ x y , x ∈ A ∧ y ∈ B ∧ f x y = z) → 
    (∀ (x:α) (y:β) (x':α) (y':β) , x ∈ A → x' ∈ A → y ∈ B → y' ∈ B →
            f x y = f x' y' → x = x' ∧ y = y') →
    has_card A a →
    has_card B b →
    has_card C (a * b) :=
begin
    revert C , revert A , induction a ,
    {
        intros , simp , apply card_0 ,
        intros ,
        have h := a_1 y a_5 ,
        cases h ,
        cases h_h ,
        cases h_h_h ,
        rename h_w a' , have t : a' ∈ A := by assumption ,
        rw [has_card] at a_3 ,
        cases a_3 ,
        cases a_3_h ,
        rename a_3_w l ,
        cases l ,
        have m := a_3_h_right.left a' ,
        simp at m , contradiction ,
        simp at a_3_h_left , contradiction ,
    },
    {
        intros ,
        have h := set_induct A a_n a_3 ,
        cases h , cases h_h , rename h_w new_x , rename h_h_w A' ,
        cases h_h_h , cases h_h_h_right , rename h_h_h_right_right A_eq ,
        have s_eq : (nat.succ a_n = a_n + 1) := rfl ,
        rw s_eq , rw add_mul , simp ,

        have A'_to_A : (∀ x , x ∈ A' → x ∈ A) := (λ x , λ x_in_A' ,
            begin
                rw A_eq , simp , left , assumption ,
            end
        ) ,
        have new_x_in_A : new_x ∈ A := begin
            rw A_eq , simp ,
        end ,

        have ih := a_ih A' { z : γ | ∃ x y, x ∈ A' ∧ y ∈ B ∧ f x y = z }
            (
                λ x:α , λ y:β , λ x_in_A' , λ y_in_B , (begin
                    simp , existsi x , split , assumption ,
                    existsi y , split , assumption , trivial ,
                end)
            ) (λ z:γ , begin
                simp , intros , rename x_1 y ,
                existsi x , split , assumption ,
                existsi y , split , assumption , assumption ,
            end) (
                λ (x : α) (y : β) (x' : α) (y' : β) ,
                λ x_in_A' , λ x'_in_A' , λ y_in_B , λ y'_in_B' , λ f_eq ,
                    a_2 x y x' y' (A'_to_A x x_in_A') (A'_to_A x' x'_in_A') y_in_B y'_in_B' f_eq
            ) (begin
                by assumption
            end) (begin
                by assumption
            end),

        rw add_comm ,
        apply (card_split_map C
             { z : γ | ∃ x y, x ∈ A' ∧ y ∈ B ∧ f x y = z }
             B
             (a_n * b) b
             (λ z : γ , z)
             (λ y : β , f new_x y)) ,
        {
            intros , simp , simp at a_5 ,
            cases a_5 , cases a_5_h , cases a_5_h_right ,
            cases a_5_h_right_h ,
            rw <- a_5_h_right_h_right ,
            apply (a a_5_w a_5_h_right_w) ,
            apply A'_to_A, assumption,
            assumption,
        },
        {
            intros , simp ,
            apply (a new_x z) ,
            rw A_eq , simp , assumption ,
        },
        {
            intros ,
            rename x z ,
            have q := a_1 z a_5 ,
            cases q ,
            cases q_h ,
            rename q_w x , rename q_h_w y ,
            cases q_h_h , rw A_eq at q_h_h_left , simp at q_h_h_left ,
            cases q_h_h_right ,
            cases q_h_h_left ,
            {
                left , existsi z , simp , existsi x , split , assumption ,
                existsi y , split , assumption, assumption ,
            },
            {
                right , existsi y , split , assumption , simp ,
                rw <- q_h_h_left , assumption ,
            },
        },
        {
            intros , simp at a_7 , assumption ,
        },
        {
            intros , simp at a_7 ,
            exact (a_2 new_x y new_x z new_x_in_A new_x_in_A a_5 a_6 a_7).right,
        },
        {
            intros , simp at a_7 , simp at a_5 , cases a_5 ,
            rename a_5_w x , cases a_5_h , cases a_5_h_right ,
            rename a_5_h_right_w z' , cases a_5_h_right_h ,
            rw a_7 at * , 
            have x_eq_new_x : (x = new_x) := (a_2 x z' new_x z (A'_to_A x a_5_h_left) new_x_in_A a_5_h_right_h_left a_6 a_5_h_right_h_right).left ,
            rw x_eq_new_x at * , contradiction ,
        },
        {
            assumption ,
        },
        {
            assumption ,
        },
    }
end 

theorem has_card_nats_lt (n : ℕ) :
    has_card { i : ℕ | i < n } n :=
begin
    rw [has_card] , existsi (list.range n) ,
    split ,
    {
        apply list.length_range ,
    },
    split ,
    {
        intros , split ,
        {
            simp ,
        },
        {
            simp , 
        }
    },
    {
        apply list.nodup_range ,
    }
end

theorem card_product_nat
    {α : Type} {γ : Type}
        (A : set α) (b : ℕ) (C : set γ) (a : ℕ)
        (f : α → ℕ → γ) :
    (∀ x y , x ∈ A → 0 ≤ y → y < b → f x y ∈ C) →
    (∀ z , z ∈ C → ∃ x y , x ∈ A ∧ 0 ≤ y ∧ y < b ∧ f x y = z) → 
    (∀ (x:α) (y:ℕ) (x':α) (y':ℕ) ,
            x ∈ A → x' ∈ A → 0 ≤ y → y < b → 0 ≤ y' → y' < b →
            f x y = f x' y' → x = x' ∧ y = y') →
    has_card A a →
    has_card C (a * b) :=
begin
    intros ,
    apply (card_product A { i : ℕ | i < b } C a b
        (λ x , λ i , f x i)) ,
    {
        intros , simp , simp at a_6 ,
        exact (a_1 x y a_5 (by simp) a_6) ,
    },
    {
        intros , simp ,
        have h := a_2 z a_5 ,
        cases h , cases h_h , rename h_w x , rename h_h_w y ,
        cases h_h_h , cases h_h_h_right , cases h_h_h_right_right ,
        existsi x , split , assumption , existsi y , split , assumption ,
        assumption ,
    },
    {
        exact (
            λ (x : α) (y : ℕ) (x' : α) (y' : ℕ),
            λ (x_in_A : x ∈ A) ,
            λ (x'_in_A : x' ∈ A) ,
            λ (y_in : y ∈ {i : ℕ | i < b}) ,
            λ (y'_in : y' ∈ {i : ℕ | i < b}) ,
            begin
                simp , intros ,
                simp at y_in ,
                simp at y'_in ,
                exact (a_3 x y x' y' x_in_A x'_in_A (by simp) y_in (by simp) y'_in a_5) ,
            end
        )
    },
    {
        assumption ,
    },
    {
        apply has_card_nats_lt ,
    },
end


theorem cardinality_unique {α : Type} (A : set α) (a:ℕ) (b:ℕ) :
    has_card A a → has_card A b → a = b := begin
    intro h1,
    intro h2,
    simp[has_card] at h1,
    simp[has_card] at h2,
    apply exists.elim h1,
    assume a1 l1,
    apply exists.elim h2,
    assume a2 l2,
    have h1: ∀ x: α, x ∈ a1 ↔ x ∈ a2,
        from sorry,
    sorry
    end
    /- {λ x: α, iff.intro (assume x ∈ a1, sorry) (assume x ∈ a2, sorry)} -/
    /- def has_card {α : Type} (s : set α) (n : ℕ) : Prop :=
    ∃ l : (list α) , list.length l = n ∧ (∀ x : α , x ∈ s ↔ x ∈ l)
            ∧ list.nodup l -/


/-
    Here we define the set of boolean sequences of length n with
    exactly k elements set to `tt`.
    We show that the cardinality of this set is `choose n k`.
    (theorem `has_card_set_n_choose_k`).
-/

def count_tt : (list bool) → (ℕ)
| [] := 0
| (ff :: l) := count_tt l
| (tt :: l) := count_tt l + 1

def set_n_choose_k (n : ℕ) (k : ℕ) : set (list bool) :=
    { l : list bool | list.length l = n ∧ count_tt l = k }

def all_ff : (ℕ) → (list bool)
| 0 := []
| (n + 1) := ff :: (all_ff n)

theorem is_all_ff : ∀ x : (list bool),
    count_tt x = 0 → x = all_ff (list.length x)
    | [] := by simp[count_tt, all_ff]
    | (tt :: l) := by simp[count_tt]
    | (ff :: l) := λ h: count_tt (ff::l) = 0, 
    have h0: 0 = count_tt (ff::l), by simp[refl, h],
    have h1: count_tt (ff::l) = count_tt l, by simp[count_tt], 
    have h2: count_tt l = 0, by simp[h0, h1, refl],
    have h3: l = all_ff (list.length l), by apply (is_all_ff l) h2,
    have h5: list.length (ff :: l) = list.length l + 1, by simp[list.length],
    have h6: all_ff (list.length (ff :: l)) 
        = all_ff(list.length l + 1), by simp[*],
    begin
    have h7:  all_ff (list.length (ff :: l)) = ff :: l, by
    {calc
        all_ff (list.length (ff :: l)) = all_ff (list.length l + 1): by simp[*]
                            ... = ff::(all_ff (list.length l)): by rw[all_ff]
                            ... = ff :: l : by rw[←h3]},
    apply eq.symm h7
    end
    
theorem length_all_ff : ∀ n : ℕ ,
    list.length (all_ff n) = n
    | 0 := by simp[all_ff, refl]
    | (n + 1) := by simp[all_ff, list.length_cons, length_all_ff n]

theorem count_tt_all_ff : ∀ n : ℕ ,
    count_tt (all_ff n) = 0
    | 0 := by simp[count_tt, all_ff, refl]
    | (n+1) := 
        begin
            calc
            count_tt (all_ff (n + 1)) = count_tt (ff:: (all_ff n)): by simp[all_ff]
                                ... = count_tt(all_ff n): by simp[count_tt]
                                ... = 0: by simp[count_tt_all_ff n]
        end

theorem eq_of_add_1 : ∀ n : ℕ , ∀ m : ℕ ,
    (n + 1) = (m + 1) -> n = m := by simp[refl]

theorem has_card_set_n_choose_k : ∀ (n : ℕ) (k : ℕ) ,
    has_card (set_n_choose_k n k) (choose n k)
| n 0 :=
    begin
        rw [has_card, set_n_choose_k] ,
        existsi ([all_ff n]) ,
        split ,
        simp ,
        intros ,
        split ,
        intros ,
        cases a ,
        simp ,
        subst n ,
        apply is_all_ff , assumption ,
        intros ,
        simp at a ,
        simp ,
        subst x ,
        split ,
        apply length_all_ff ,
        apply count_tt_all_ff ,
    end
| 0 (k + 1) :=
    begin
        simp [has_card, set_n_choose_k] ,
        existsi ([]) ,
        split ,
        refl ,
        intros , split ,
        intros ,
        simp ,
        cases a ,
        have h : (x = list.nil) ,
        cases x , trivial, trivial ,
        subst x at a_right , simp [count_tt] at a_right , trivial ,
        simp ,
    end
| (n+1) (k+1) :=
    begin
        simp [set_n_choose_k] ,
        apply (card_split_map
            ({l : list bool | list.length l = n + 1 ∧ count_tt l = k + 1})
            ({l : (list bool) | list.length l = n ∧ count_tt l = k})
            ({l : (list bool) | list.length l = n ∧ count_tt l = k+1})
            (choose n k)
            (choose n (k+1))
            (λ r : (list bool) , ((tt :: r) : list bool))
            (λ r : (list bool) , ((ff :: r) : list bool))
        ) ,
        {
            simp , intros ,
            cases x , trivial ,
            cases x_hd ,
            {
                right , existsi x_tl ,
                split , split ,
                simp at a , rw [@nat.add_comm 1 _] at a ,
                apply eq_of_add_1 , assumption ,
                simp [count_tt] at a_1 , assumption ,
                trivial ,
            },
            {
                left , existsi x_tl ,
                split , split ,
                simp at a , rw [@nat.add_comm 1 _] at a ,
                apply eq_of_add_1 , assumption ,
                simp [count_tt] at a_1 , assumption ,
                trivial ,
            }
        },
        {
            intros ,
            simp at a_2 ,
            assumption ,
        },
        {
            intros ,
            simp at a_2 ,
            assumption ,
        },
        {
            intros ,
            simp at a_2 ,
            assumption ,
        },
        {
            apply has_card_set_n_choose_k ,
        },
        {
            apply has_card_set_n_choose_k ,
        },
    end

