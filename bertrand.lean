import data.nat.choose
import data.nat.prime
import data.nat.gcd
import data.list
import tactic.linarith

import data.set.finite
import data.multiset
import data.finset
import data.finset algebra.big_operators
import algebra.big_operators
import init.algebra.functions
import algebra.group_power

import data.nat.sqrt data.nat.gcd data.list.basic data.list.perm

open classical

/-
    https://en.wikipedia.org/wiki/Proof_of_Bertrand%27s_postulate
-/

/- Primes dividing choose -/

/- Define a floor log function for natural numbers.
    TODO does this already exist somewhere? -/
def log : ℕ → ℕ → ℕ 
| 0 _ := 0
| 1 _ := 0
| _ 0 := 0
| (p+2) (n+1) := if (n+1) < (p+2) then 0 else (
    have h : (n+1)/(p+2) < n+1, from begin
        calc (n + 1) / (p + 2) ≤ (n+1) / 2 : sorry
        ... < (n+1) / 1 : sorry
        ... = n+1 : by simp
    end,
    log (p+2) ((n+1)/(p+2)) + 1
)

theorem pow_log_le : ∀ (a b : ℕ) ,
    a ^ (log a b) ≤ b := sorry

/- This is a closed form for the largest exponent
    r such that p^r divides (choose n k). -/
def lpdc (n:ℕ) (k:ℕ) (p:ℕ) :=
    ((list.range' 1 (log p n)).map
        (λ (i:ℕ) , if (k % (p^i)) + ((n-k) % (p^i)) ≥ p^i then 1 else 0)).sum

theorem p_pow_lpdc_dvd_choose : ∀ (n k p : ℕ) ,
    p ^ lpdc n k p ∣ choose n k := sorry

theorem exp_le_lpdc_of_dvd_choose : ∀ (n k p r : ℕ) ,
    p ^ r ∣ choose n k → r ≤ lpdc n k p := sorry

-- Which has this corollary:

lemma exp_le_log_of_dvd_choose : ∀ (n k p r : ℕ) ,
    p ^ r ∣ choose n k → r ≤ log p n := sorry

/- "lemma 1" -/

lemma four_n_bound : ∀ (n : ℕ) ,
    4 ^ n ≤ 2 * n * (choose (2*n) n) := sorry

/- "lemma 2" -/

lemma p_to_R_bound : ∀ (p:ℕ) (r:ℕ) (n:ℕ) ,
    nat.prime p →
    p ^ r ∣ (choose (2*n) n) →
    p ^ r ≤ 2*n :=
begin
    intros ,
    have h : r ≤ log p (2*n) := exp_le_log_of_dvd_choose (2*n) n p r a_1,
    calc p ^ r ≤ p ^ (log p (2*n)) : begin
        apply nat.pow_le_pow_of_le_right ,
        cases p ,
        have q : ¬ nat.prime 0 := dec_trivial , contradiction ,
        rw nat.succ_eq_add_one , linarith ,
        assumption ,
    end
        ... ≤ 2*n : begin
        apply pow_log_le ,
    end
end

/- "lemma 3" -/

theorem log_p_eq_1 : ∀ (p n) ,
    p ≥ 3 → 2*n / 3 < p → p ≤ n → 
    log p (2*n) = 1 := sorry

lemma central_primes_do_not_divide : ∀ (p n : ℕ) ,
    nat.prime p →
    p ≠ 2 →
    2*n / 3 < p →
    p ≤ n →
    ¬ (p ∣ (choose (2*n) n)) :=
begin
    intros , by_contradiction , 
    have h := exp_le_lpdc_of_dvd_choose (2*n) n p 1 (begin
        simp , assumption ,
    end) ,

    have log_1 : log p (2*n) = 1 := begin
        apply log_p_eq_1 ,
        cases p ,
        have h : ¬ (nat.prime 0) := dec_trivial ,
        contradiction ,
        cases p , 
        have h : ¬ (nat.prime 1) := dec_trivial ,
        contradiction ,
        cases p ,
        contradiction ,
        rw nat.succ_eq_add_one , 
        rw nat.succ_eq_add_one , 
        rw nat.succ_eq_add_one ,
        linarith , assumption, assumption ,
    end, 

    have j : lpdc (2 * n) n p = 0 := begin
        rw [lpdc] , rw log_1 , rw [list.range'] ,
        simp , 
        have l : ¬(n % p + (2 * n - n) % p ≥ p) := begin
            simp , rw two_mul , rw nat.add_sub_cancel ,
            rw <- two_mul , 
            have t : n = (n - p) + p := begin
                rw nat.sub_add_cancel , assumption ,
            end,
            rw t , simp , 
            have s : ((n - p) % p) ≤ n-p := begin
                apply nat.mod_le ,
            end,
            have r : 2*n < 3*p := begin
                rw [@nat.mul_comm 3 p] ,
                rw <- nat.div_lt_iff_lt_mul' , assumption ,
                norm_num ,
            end ,
            have q : 2*(n-p) < p := begin
                rw nat.mul_sub_left_distrib ,
                calc 2*n - 2*p < 3*p - 2*p :
                    begin
                        rw nat.sub_lt_sub_right_iff , assumption , linarith ,
                    end
                ... = (3-2)*p : by rw nat.mul_sub_right_distrib
                ... = p : by norm_num
            end,
            linarith ,
        end,
        simp [l] , 
    end,
    rw j at h , linarith ,
end

/- range-related lemmas -/

def range_to (n:ℕ) (m:ℕ) := list.range' n (m-(n-1))

theorem range_to_append : ∀ (n m k : ℕ) ,
    n ≤ m+1 → m ≤ k →
    range_to n m ++ range_to (m+1) k = range_to n k := sorry

/- "lemma 4" -/

def primorial (n : ℕ) : ℕ :=
    (list.filter nat.prime (range_to 1 n)).prod

lemma primorial_induction : ∀ (n : ℕ) ,
    primorial (n+1) = (if nat.prime (n+1) then primorial n * (n+1) else primorial n) := sorry

lemma zero_lt_primorial : ∀ (n : ℕ) ,
    0 < primorial n :=
begin
    intros , induction n, 
    simp [primorial, list.filter, range_to, list.prod] , linarith ,
    rw primorial_induction ,
    split_ifs , rw mul_add , simp , linarith ,
    assumption ,
end

lemma primorial_ratio_eq_prod : ∀ (n m : ℕ) ,
    m ≤ n →
    primorial n / primorial m =
        (list.filter nat.prime (range_to (m+1) n)).prod :=
begin
    intros , 
    have h : primorial n = primorial m * (list.filter nat.prime (range_to (m+1) n)).prod := begin
        rw [primorial, primorial] ,
        rw <- list.prod_append,
        rw <- list.filter_append ,
        rw <- range_to_append ,
        linarith, linarith ,
    end,
    rw h , rw nat.mul_div_cancel_left ,
    apply zero_lt_primorial ,
end

lemma coprime_list : ∀ (m n p : ℕ) ,
    n < p →
    nat.prime p →
    nat.coprime (list.prod (list.filter nat.prime (range_to (m + 1) n))) p := sorry

lemma prime_list_dvd : ∀ (n m k : ℕ) ,
    (∀ (p:ℕ) , nat.prime p → m+1 ≤ p → p ≤ n → p ∣ k) → 
    (list.filter nat.prime (range_to (m+1) n)).prod ∣ k :=
begin
    intros, induction n ,
    {
        rw [range_to] , simp ,
    },
    {
        by_cases (m ≤ n_n) ,
        {
            have h : range_to (m + 1) (nat.succ n_n) = range_to (m+1) n_n ++ range_to (n_n + 1) (n_n + 1) := begin
                rw range_to_append , linarith , linarith ,
            end,
            rw h , rw list.filter_append , rw list.prod_append ,
            have h1 : range_to (n_n + 1) (n_n + 1) = [n_n + 1] := by simp [range_to] ,
            rw h1 , simp [list.filter] ,
            split_ifs ,
            {
                 have h2 : list.prod [n_n + 1] = n_n + 1 := by simp ,
                 rw h2 ,

                 have n_n_plus_1_dvd_k := a (n_n + 1) h_1 (by linarith) (begin
                    have t : nat.succ n_n = n_n + 1 := rfl , rw t ,
                 end),
                 apply nat.coprime.mul_dvd_of_dvd_of_dvd ,
                 apply coprime_list , linarith , assumption ,
                 apply n_ih , intros , apply a , assumption, assumption ,
                 have h_3 : nat.succ n_n = n_n + 1 := rfl , rw h_3 , linarith ,
                 assumption ,
            },
            {
                simp , apply n_ih , intros , apply a , assumption, assumption, have h_3 : nat.succ n_n = n_n + 1 := rfl , rw h_3 , linarith ,
            }
        },
        {
            have h_3 : nat.succ n_n = n_n + 1 := rfl , rw h_3 ,
            have t : n_n + 1 - m = 0 := begin
                rw nat.sub_eq_zero_iff_le , simp at h ,
                apply nat.le_of_lt_succ ,
                have h_4 : nat.succ m = m + 1 := rfl , rw h_4 ,
                linarith ,
            end,
            have h : range_to (m + 1) (n_n + 1) = [] := begin
                rw [range_to] , simp at h , rw nat.add_sub_cancel ,
                rw t , simp , 
            end,
            rw h , simp , 
        }
    }
end

lemma p_dvd_choose_2m_plus_1_of_ge_m_plus_2 : ∀ (m p : ℕ) ,
    nat.prime p →
    m + 2 ≤ p →
    p ≤ 2*m + 1 →
    p ∣ choose (2*m+1) (m+1) :=
begin
    intros ,
    have q := @choose_mul_fact_mul_fact (2*m + 1) (m + 1) (by linarith) ,
    have r : p ∣ nat.fact (2 * m + 1) := begin
            rw nat.prime.dvd_fact , assumption , assumption , 
        end,
    have r1 : ¬ (p ∣ nat.fact (m + 1)) := begin
            rw nat.prime.dvd_fact , simp , linarith , assumption ,
        end,
    have r2 : ¬ (p ∣ nat.fact (2 * m + 1 - (m + 1))) := begin
            rw nat.prime.dvd_fact , simp ,
            have h1 : 1 + 2 * m = (m + (m+1)) := by ring ,
            rw h1 , rw nat.add_sub_cancel , linarith , 
            assumption ,
        end,
    rw <- q at r ,
    rw nat.prime.dvd_mul at r ,
    cases r ,
    rw nat.prime.dvd_mul at r ,
    cases r , assumption , contradiction , assumption , contradiction ,
    assumption ,
end

lemma primorial_ratio_le_choose : ∀ (m : ℕ) ,
    m ≥ 2 →
    primorial (2*m + 1) / primorial (m+1) ≤ (choose (2*m + 1) (m+1)) :=
begin
    intros ,
    rw primorial_ratio_eq_prod ,
    apply nat.le_of_dvd ,
    {
        apply choose_pos , linarith ,
    },
    {
        apply prime_list_dvd , intros , apply p_dvd_choose_2m_plus_1_of_ge_m_plus_2 , assumption, linarith , assumption ,
    },
    {
        linarith ,
    },
    
end

lemma primorial_2m_plus_1_le_choose : ∀ (m : ℕ) ,
    m ≥ 2 →
    primorial (2*m + 1) ≤ primorial (m+1) * (choose (2*m + 1) (m+1)) := sorry

lemma finset_sum_finset_range_eq_sum_range : ∀ (f: ℕ → ℕ) (n : ℕ) ,
    finset.sum (finset.range n) f = ((list.range n).map f).sum := sorry

lemma choose_2m_plus_1_le_power_2 : ∀ (m : ℕ) ,
    choose (2*m + 1) (m+1) ≤ 2^(2*m) :=
begin
    intros ,
    have t := (
        calc 2 * 2^(2*m) = 2^(2*m+1) : sorry
        ... = ((1:ℕ) + (1:ℕ))^(2*m+1) : by simp
    ),
    have h := add_pow 1 1 (2*m+1) , simp at h ,
    simp at t , rw h at t , clear h,

    rw finset_sum_finset_range_eq_sum_range at t,
    
    have l : list.range (nat.succ (1 + 2 * m)) =
        list.range' 0 m ++
        list.range' m 2 ++
        list.range' (m+2) m := sorry ,
    rw l at t ,
    rw [list.map_append, list.map_append, list.sum_append, list.sum_append] at t , 
    have t' : 2 * 2 ^ (2 * m) ≥ 
        list.sum (list.map (choose (1 + 2 * m)) (list.range' m 2)) := by linarith ,
    clear t,
    simp at t' ,

    have q : choose (1 + 2 * m) m = choose (1 + 2 * m) (m+1) := sorry ,
    rw q at t' , 
    have q' : choose (1 + 2 * m) (m + 1) + choose (1 + 2 * m) (m + 1) = 2 * choose (1 + 2 * m) (m + 1) := by ring ,
    rw q' at t' ,
    simp , linarith ,
end

lemma primorial_2m_plus_1_le_power_2 : ∀ (m : ℕ) ,
    m ≥ 2 →
    primorial (2*m + 1) ≤ primorial (m+1) * 2^(2*m) :=
begin
    intros ,
    calc primorial (2*m + 1) ≤
         primorial (m+1) * (choose (2*m + 1) (m+1)) : 
            primorial_2m_plus_1_le_choose m a
    ... ≤ primorial (m+1) * 2^(2*m) :
        begin
            apply nat.mul_le_mul_left ,
            apply choose_2m_plus_1_le_power_2 ,
        end
end

lemma case_by_parity : ∀ (n : ℕ) ,
    (∃ (m:ℕ) , n = 2*m) ∨ (∃ (m:ℕ) , n = 2*m + 1) :=
begin
    intros , induction n ,
    left , existsi 0, norm_num ,
    cases n_ih ,
    cases n_ih , right , existsi n_ih_w , rw n_ih_h ,
    cases n_ih , left , existsi (n_ih_w + 1) , rw n_ih_h ,
    rw nat.succ_eq_add_one , ring , 
end

lemma le_2_pow_2_mul_2_mul_plus_1 : ∀ (m : ℕ) ,
    2 ^ (2 * (2 * m + 1)) ≤ 2 ^ (2 * (2 * (m + 1))) :=
begin
    intros ,
    apply nat.pow_le_pow_of_le_right , linarith ,
    linarith ,
end

local attribute [instance] nat.decidable_prime_1

lemma primorial_bound_aux : ∀ (bound n : ℕ) ,
    n < bound →
    n ≥ 3 →
    8 * primorial n < 2 ^ (2*n)
| 0 n :=
    begin
        intros , linarith , 
    end
| (bound+1) 0 := begin intros , linarith end 
| (bound+1) 1 := begin intros , linarith end
| (bound+1) 2 := begin intros , linarith end
| (bound+1) 3 :=
    begin
        intros ,
        have p1 : ¬ (nat.prime 1) := dec_trivial ,
        have p2 : (nat.prime 2) := dec_trivial ,
        have p3 : (nat.prime 3) := dec_trivial ,
        rw [primorial, range_to] , norm_num ,
        simp [list.filter, list.prod, p1, p2, p3],
        norm_num, 
    end
| (bound+1) 4 :=
    begin
        intros ,
        have p1 : ¬ (nat.prime 1) := dec_trivial ,
        have p2 : (nat.prime 2) := dec_trivial ,
        have p3 : (nat.prime 3) := dec_trivial ,
        have p4 : ¬ (nat.prime 4) := dec_trivial ,
        rw [primorial, range_to] , norm_num ,
        simp [list.filter, list.prod, p1, p2, p3, p4],
        norm_num, 
    end
| (bound+1) (n+5) := begin
    intros ,
    cases (case_by_parity (n+5)) ,
    {
        cases h , rename h_w m , rw h_h at * ,
        cases m , simp at a , linarith ,
        have q : (nat.succ m) = (m+1) := rfl , rw q at * , clear q ,
        have m_ge_1 : m ≥ 1 := by linarith ,
        rw primorial ,
        rw [<- @range_to_append 1 (2*m + 1) (2*(m+1))] ,
        {
        rw list.filter_append ,
        have r : range_to (2 * m + 1 + 1) (2 * (m + 1)) = [2 * (m+1)] :=
            begin
                rw [range_to] , rw nat.add_sub_cancel ,
                have q' : 2 * (m + 1) = 1 + (2 * m + 1) := by ring ,
                have q : 2 * (m + 1) - (2 * m + 1) = 1 := begin
                    rw q', rw nat.add_sub_cancel ,
                end,
                rw q ,
                rw [list.range', list.range'],
                have l : (2 * m + 1 + 1) = 2 * (m + 1) := by ring,
                rw l ,
            end,
        rw r ,
        have s : list.filter nat.prime [2 * (m + 1)] = [] :=
            begin
                rw [list.filter] , split_ifs ,
                have t : ¬ (nat.prime (2 * (m+1))) := begin
                    apply nat.not_prime_mul, linarith , linarith ,
                end,
                contradiction ,
                rw [list.filter] , 
            end ,
        rw s , simp ,
        have ih_bound : (2*m + 1 < bound) := by linarith ,
        have ih := primorial_bound_aux
            bound (2*m + 1) ih_bound (by linarith) ,
        rw [<- primorial] ,
        rw nat.add_comm ,
        calc 8 * primorial (2 * m + 1) < 2 ^ (2 * (2 * m + 1)) : ih
        ... ≤ 2 ^ (2 * (2 * (m + 1))) : (le_2_pow_2_mul_2_mul_plus_1 m)
        },
        linarith , linarith ,
    },
    {
        cases h , rename h_w m , rw h_h at * ,
        have m_ge_2 : m ≥ 2 := by linarith ,
        have h1 := primorial_2m_plus_1_le_power_2 m m_ge_2 ,
        have ih_bound : (m+1 < bound) := by linarith ,
        have h2 := primorial_bound_aux bound (m+1) ih_bound (by linarith) ,
        calc 8 * primorial (2 * m + 1) ≤ 8 * primorial (m + 1) * 2 ^ (2*m) :        begin
                rw nat.mul_assoc ,
                apply nat.mul_le_mul_left , assumption ,
              end
        ... < 2 ^ (2 * (m+1)) * 2 ^ (2*m) :
            begin
                rw mul_lt_mul_right , assumption ,
                apply nat.pos_pow_of_pos , linarith ,
            end
        ... = 2 ^ (2 * (2*m+1)) : begin
            rw <- nat.pow_add , ring , 
        end
    },
end

lemma primorial_bound : ∀ (n : ℕ) ,
    n ≥ 3 →
    8 * primorial n < 2 ^ (2*n) :=
begin
    intros , 
    apply (primorial_bound_aux (n+1) n) ,
    linarith , assumption ,
end

/- prime factorization -/

theorem factorize : ∀ (n m : ℕ) ,
    (∀ p , nat.prime p → p ∣ n → p ≤ m) →
    (∃ (r : ℕ → ℕ) , (∀ (p:ℕ) , nat.prime p → p ^ r p ∣ n) ∧ 
        n = (((range_to 1 m).filter nat.prime).map
            (λ p , p ^ (r p))).prod
    ) := sorry

lemma p_le_of_p_dvd_choose : ∀ (p n k : ℕ) ,
    k ≤ n → nat.prime p → p ∣ (choose n k) → p ≤ n :=
begin
    intros ,
    have q := @choose_mul_fact_mul_fact n k a,
    have r : (p ∣ nat.fact n) := begin
        cases a_2 , rw [a_2_h] at q , rw nat.mul_assoc at q ,
        rw nat.mul_assoc at q , rw <- q , apply dvd_mul_right ,
    end ,
    rw [nat.prime.dvd_fact] at r , assumption ,
    assumption ,
end

/- main result (bertrand's postulate for n ≥ 432 case) -/

lemma two_thirds_n_bound : ∀ (n : ℕ) ,
    n ≥ 468 → 
    2 * n / 3 < 2 →
    false :=
begin
    intros ,
    have t := (
        calc 2 < 2 * 468 / 3 : by norm_num
        ... ≤ 2 * n / 3 : begin
            apply nat.div_le_div_right , linarith ,
        end
        ... < 2 : a_1
    ),
    contradiction ,
end

lemma sqrt_le_2_3 : ∀ (n : ℕ) ,
    468 ≤ n → nat.sqrt (2 * n) ≤ 2 * n / 3 := sorry

lemma p_le_2n_over_3 : ∀ (n p : ℕ) ,
    (∀ (x : ℕ), nat.prime x → n < x → 2 * n < x) →
    n ≥ 468 → 
    nat.prime p →
    p ∣ (choose (2*n) n) →
    p ≤ (2*n / 3) :=
begin
    intros ,
    by_cases (p ≤ 2*n / 3) ,
    {
        assumption ,
    },
    simp at h , rename h p_bound ,
    by_cases (p ≤ n) ,
    {
        have q := central_primes_do_not_divide p n a_2 (begin
            /- show p > 2 -/
            by_contradiction , simp at a_4 , rw a_4 at * ,
            apply two_thirds_n_bound , assumption, assumption,
        end) p_bound h ,
        contradiction ,
    },
    simp at h , clear p_bound , rename h p_bound ,
    {
        have q := a p a_2 p_bound ,
        have r := p_le_of_p_dvd_choose p (2*n) n (by linarith) a_2 a_3 ,
        linarith ,
    },
end

lemma p_at_most_1_in_choose_of_gt_sqrt : ∀ (p n r : ℕ) ,
    nat.prime p → 
    p > nat.sqrt (2*n) →
    p ^ r ∣ choose (2*n) n →
    r ≤ 1 := sorry

lemma factorize_choose_2n_n : ∀ (n : ℕ) ,
    (∀ (x : ℕ), nat.prime x → n < x → 2 * n < x) →
    n ≥ 468 → 
    ∃ (r : ℕ → ℕ) ,
    (∀ (p:ℕ) , nat.prime p → p ^ r p ∣ choose (2*n) n) ∧
    (choose (2*n) n =
        (((range_to 1 (2*n/3)).filter nat.prime).map
                (λ p , p ^ (r p))).prod) :=
begin
    intros ,
    have f := factorize (choose (2*n) n) (2*n/3) (begin
        intros , apply p_le_2n_over_3 , assumption, assumption, assumption,
        assumption ,
    end),
    cases f , rename f_w r , cases f_h , rename f_h_left dvd_condition ,
    rename f_h_right prod_condition ,
    existsi r ,
    split , assumption ,
    rw prod_condition ,
end

lemma prod_le_prod : ∀ (l : list ℕ) (f g : ℕ → ℕ) ,
    (∀ (x:ℕ) , x ∈ l → f x ≤ g x) → 
    (l.map f).prod ≤ (l.map g).prod := sorry

lemma prod_repeat_eq_pow : ∀ (a b : ℕ) ,
    list.prod (list.repeat a b) = a ^ b :=
begin
    intros , 
    induction b ,
    simp , simp ,
    rw nat.pow_succ , rw nat.mul_comm , 
end

lemma length_filter_le_length {α : Type} (p : α → Prop) [decidable_pred p] : ∀ (l : list α) ,
    list.length (l.filter p) ≤ list.length l :=
begin
    intros ,
    induction l , simp , simp , rw [list.filter] , split_ifs ,
    simp , assumption , linarith ,
end

lemma prime_bounds_1 : ∀ (n : ℕ) (r : ℕ → ℕ),
    (∀ p , nat.prime p → p ^ r p ∣ (choose (2*n) n)) →
    (((range_to 1 (nat.sqrt (2*n))).filter nat.prime).map
                (λ p , p ^ (r p))).prod
    ≤ (2*n) ^ (nat.sqrt (2*n)) :=
begin
    intros ,
    by_cases (n ≥ 1) ,
    {
        have h := prod_le_prod 
            ((range_to 1 (nat.sqrt (2*n))).filter nat.prime)
            (λ p , p ^ (r p))
            (λ p , 2 * n)
            (begin
                intros, simp ,
                simp at a_1 , cases a_1 ,
                apply p_to_R_bound , assumption , apply a , assumption, 
            end),
        exact (nat.le_trans h (begin
            rw list.map_const , rw prod_repeat_eq_pow ,
            apply nat.pow_le_pow_of_le_right,
            linarith ,
            have l : (nat.sqrt (2 * n)) = list.length (range_to 1 (nat.sqrt (2 * n))) := begin
                rw [range_to] , rw [list.length_range'] , ring , 
            end,
            have len_le := length_filter_le_length nat.prime (range_to 1 (nat.sqrt (2 * n))) ,
            rw <- l at len_le ,
            assumption ,
        end)),
    },
    {
        simp at h ,
        have t : (nat.sqrt 0 = 0) := rfl ,
        rw h , norm_num , rw [range_to] , rw t , simp , 
    }
end

lemma prime_bounds_2 : ∀ (n : ℕ) (r : ℕ → ℕ),
    n ≥ 468 → 
    (∀ p , nat.prime p → p ^ r p ∣ (choose (2*n) n)) →
    (((range_to (nat.sqrt (2*n) + 1) (2*n/3)).filter nat.prime).map
                (λ p , p ^ (r p))).prod
    ≤ primorial (2*n / 3) :=
begin
    intros ,
    have h := prod_le_prod 
        ((range_to (nat.sqrt (2*n) + 1) (2*n/3)).filter nat.prime)
        (λ p , p ^ (r p))
        id
        (begin
            intros , simp at a_2, rw [range_to] at a_2 , simp at a_2 ,
            cases a_2 , cases a_2_left , 
            simp ,
            have t : x ^ r x ≤ x ^ 1 := begin
                apply nat.pow_le_pow_of_le_right , linarith ,
                apply p_at_most_1_in_choose_of_gt_sqrt x n (r x) ,
                assumption , linarith , apply a_1 , assumption ,
            end,
            simp at t,
            assumption ,
        end),
    exact (nat.le_trans h (begin
        rw list.map_id ,
        rw primorial , 
        have rsplit : range_to 1 (2 * n / 3) =
            range_to 1 (nat.sqrt (2 * n)) ++
            range_to (nat.sqrt (2 * n) + 1) (2 * n / 3) :=
                begin
                    rw range_to_append , linarith ,
                    apply sqrt_le_2_3 , assumption ,
                end,
        rw rsplit ,
        rw list.filter_append ,
        rw list.prod_append ,
        calc
            list.prod (list.filter nat.prime (range_to (nat.sqrt (2 * n) + 1) (2 * n / 3))) =
                1 * list.prod (list.filter nat.prime (range_to (nat.sqrt (2 * n) + 1) (2 * n / 3))) :
                begin
                    ring ,
                end
        ... ≤
                primorial (nat.sqrt (2 * n)) *
                list.prod (list.filter nat.prime (range_to (nat.sqrt (2 * n) + 1) (2 * n / 3))) :
                begin
                    apply nat.mul_le_mul_right,
                    apply nat.le_of_lt_succ ,
                    have x : nat.succ (primorial (nat.sqrt (2 * n))) = primorial (nat.sqrt (2 * n)) + 1 := rfl ,
                    rw x ,
                    have t := zero_lt_primorial (nat.sqrt (2 * n)) ,
                    linarith ,
                end
        ... =
                list.prod (list.filter nat.prime (range_to 1 (nat.sqrt (2 * n)))) *
                list.prod (list.filter nat.prime (range_to (nat.sqrt (2 * n) + 1) (2 * n / 3))) :
                begin
                    rw [primorial] , 
                end
    end))
end

lemma main_bound : ∀ (n : ℕ) ,
    n ≥ 468 →
    2*n * ((2*n) ^ (nat.sqrt (2*n))) * (4 ^ (2*n/3)) < 4^n := sorry

lemma b_lt_c_of_ab_lt_c : ∀ (a b c : ℕ) ,
    a > 0 → 
    a*b < c → b < c := sorry

/- copied from assignment 3, surprised I couldn't find this built-in? -/

theorem e1 {α : Type} : ∀ (p : α → Prop) , (¬ ∃ x, p x) → ∀ x, ¬ p x :=
  assume p : α → Prop ,
  assume h : (¬ ∃ x, p x) ,
  assume x : α ,
  not.intro (
    assume g : p x ,
    absurd (exists.intro x g) h
  )

theorem exists_of_not_forall {α : Type} : ∀ (p : α → Prop) , (¬ ∀ x, ¬ p x) → ∃ x, p x :=
  assume p : α → Prop ,
  assume g : (¬ ∀ x, ¬ p x) ,
  or.elim (em (∃ x, p x))
  (
    assume h : (∃ x, p x) ,
    h
  )
  (
    assume h : ¬ (∃ x, p x) ,
    absurd (e1 p h) g
  )

lemma bertrands_postulate_main : ∀ (n : ℕ) ,
    n ≥ 468 → 
    ∃ p , nat.prime p ∧ n < p ∧ p ≤ 2*n :=
begin
    intros ,
    apply exists_of_not_forall ,
    by_contradiction ,
    simp at a_1 ,

    have h := factorize_choose_2n_n n a_1 a ,
    cases h , rename h_w r , cases h_h ,
    rename h_h_left r_divides ,
    rename h_h_right choose_2n_n_factorization ,

    have t := (
    calc 4^n ≤ 2*n * (choose (2*n) n) : four_n_bound n
    ... = 2*n * (((range_to 1 (2*n/3)).filter nat.prime).map
                (λ p , p ^ (r p))).prod : begin
                     rw <- choose_2n_n_factorization,
                end
    ... = 2*n *
            (((range_to 1 (nat.sqrt (2*n))).filter nat.prime).map
                (λ p , p ^ (r p))).prod *
            (((range_to (nat.sqrt (2*n) + 1) (2*n/3)).filter nat.prime).map
                (λ p , p ^ (r p))).prod :
            begin
                rw [@nat.mul_assoc (2*n) _ _] ,
                rw <- list.prod_append ,
                rw <- list.map_append ,
                rw <- list.filter_append ,
                rw <- range_to_append ,
                linarith , 
                apply sqrt_le_2_3 , assumption ,
            end
    ... ≤ 2*n *
            (2*n) ^ (nat.sqrt (2*n)) *
            (((range_to (nat.sqrt (2*n) + 1) (2*n/3)).filter nat.prime).map
                (λ p , p ^ (r p))).prod :
            begin
                apply nat.mul_le_mul_right ,
                apply nat.mul_le_mul_left ,
                exact (prime_bounds_1 n r r_divides) ,
            end
    ... ≤ 2*n *
            (2*n) ^ (nat.sqrt (2*n)) *
            primorial (2*n / 3) :
            begin
                apply nat.mul_le_mul_left ,
                exact (prime_bounds_2 n r r_divides) ,
            end
    ... ≤ 2*n *
            (2*n) ^ (nat.sqrt (2*n)) *
            4 ^ (2*n/3) :
            begin
                have q := (calc
                        (3:ℕ) ≤ 312 : (by linarith)
                        ... = 2 * 468 / 3 : by norm_num
                        ... ≤ 2 * n / 3 : begin
                            apply nat.div_le_div_right ,
                            apply nat.mul_le_mul_left ,
                            assumption ,
                        end
                ),
                have h := primorial_bound (2*n / 3) q,
                have h' := b_lt_c_of_ab_lt_c _ _ _ (by linarith) h,
                rw nat.pow_mul at h' ,
                have h'' : (2 ^ 2 = 4) := by refl ,
                rw h'' at h' ,
                apply nat.mul_le_mul_left ,
                apply le_of_lt , assumption ,
            end
    ... < 4^n : main_bound n a
    ),
    linarith ,

end

/- full bertrand's postulate -/

theorem bertrands_postulate : ∀ (n : ℕ) ,
    n ≥ 1 →
    ∃ p , nat.prime p ∧ n < p ∧ p ≤ 2*n := sorry