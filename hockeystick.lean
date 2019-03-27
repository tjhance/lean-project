import data.nat.choose
import data.set
import data.set.finite
import data.multiset
import data.finset
import data.list
import data.finset algebra.big_operators
import algebra.big_operators
import init.algebra.functions
import algebra.group_power
#eval choose 5 4
#check nat.rec_on

/- Collaboration between
   Travis Hance (thance)
   Katherine Cordwell (kcordwell)
-/

/- Following the proof at https://artofproblemsolving.com/wiki/index.php/Combinatorial_identity -/

/- sum_for_hockey_stick takes r and k and computes the sum from i = r 
to i = r + k of (i choose r) -/
def sum_for_hockey_stick (r k : ℕ) : ℕ := 
nat.rec_on k 1 (λ k ih, ih + (choose (r + k + 1) r))

#eval sum_for_hockey_stick  5 0 /- this is really saying 5 choose 5 is 1 -/

#eval sum_for_hockey_stick 5 1 /- this is saying 5 choose 5 + 6 choose 5 is 7 -/
#eval choose 7 6

#eval sum_for_hockey_stick 5 2 /- calculates 5 choose 5 + 6 choose 5 + 7 choose 5-/
#eval choose 8 6

#eval sum_for_hockey_stick 5 3 /- calculates 5 choose 5 + 6 choose 5 + 7 choose 5 + 8 choose 5-/
#eval choose 9 6

/- Says that for natural numbers r and n, if n >= r, then the sum from i = r to n 
of i choose r equals n + 1 choose r + 1 -/
theorem hockey_stick_identity (k r : ℕ) :
sum_for_hockey_stick r k = (choose (r + k + 1) (r + 1)) :=
begin
induction k with k ih,
{have h: sum_for_hockey_stick r 0 = 1, by refl,
simp[*, refl]},
{
    calc sum_for_hockey_stick r (nat.succ k) 
        = (sum_for_hockey_stick r k) + (choose (r + k + 1) r): by simp[sum_for_hockey_stick]
    ... = (choose (r + k + 1) (r + 1)) + (choose (r + k + 1) r) : by rw[ih]
    ... = (choose (r + k + 1) r) + (choose (r + k + 1) (r + 1)): by simp
    ... = choose (r + k + 1) r + choose (r + k + 1) (nat.succ r) : by refl
    ... = choose (r + k + 1 + 1) (r + 1) : by rw[←choose]
}
end

variables x y: ℕ

/- Here I prove the first steps in the algebraic proof of Vandermonde's as found
on Wikipedia: https://en.wikipedia.org/wiki/Vandermonde%27s_identity -/
/- Lemma for a case of using the binomial theorem -/
lemma binomial_theorem_with_1 (x n : ℕ) : 
    ∀ n : ℕ, (x + 1)^n = (finset.range (nat.succ n)).sum (λ m, x ^ m * choose n m) :=
    begin
    intro n,
    have h3 := add_pow x 1 n,
    simp at h3, apply h3
    end 

 /-show sum from r = 0 to m + n (m + n choose r) x^r = (1 + x)^(m + n) = (
     1 + x)^m = (1 + x)^n = (scary) * (scary) -/
#check pow_add
lemma binomial_theorem_for_vandermonde (x m n : ℕ) :
    ∀ n m: ℕ, (finset.range (m + nat.succ n)).sum(λ r, x^r * (choose (m + n) r)) 
        = (finset.range (nat.succ m)).sum(λ r, x^r * 
        choose m r)*(finset.range (nat.succ n)).sum(λ r, x^r * choose n r) :=
    begin
        intros n m,
        have h := pow_add (x + 1) m n,
        have h1 : n + m = m + n, by simp[add_comm],
        simp at h,
        rw h1 at h,
        calc 
        (finset.range (m + nat.succ n)).sum(λ r, x^r * (choose (m + n) r)) = 
                (x + 1)^(m + n): by rw ← binomial_theorem_with_1 x (m + nat.succ n)
        ... = (x + 1)^m * (x + 1)^n: h
        ... = (finset.range (nat.succ m)).sum(λ r, x^r * choose m r) * (x + 1)^n: by rw binomial_theorem_with_1 x (nat.succ m)
        ... = (finset.range (nat.succ m)).sum(λ r, x^r * 
        choose m r)*(finset.range (nat.succ n)).sum(λ r, x^r * choose n r) : by rw binomial_theorem_with_1 x (nat.succ n)
    end

/- Vandermonde's identity says that m + n choose r equals the 
sum from k = 0 to r of (m choose k)*(n choose r - k)
-/
def sum_for_vandermonde (m n r i: ℕ) : ℕ :=
nat.rec_on i ((choose m 0)*(choose n r)) 
(λ i ih, ih + (choose m (i + 1))*(choose n (r - (i + 1))))

#eval sum_for_vandermonde  3 4 6 6
#eval choose (3 + 4) 6

#eval sum_for_vandermonde 12 5 8 8
#eval choose (12 + 5) 8

/- double-checked with Mathematica -/
#eval sum_for_vandermonde 12 5 8 3
#eval sum_for_vandermonde  3 4 6 5

/- The algebraic proof of Vandermonde's finishes with a difficult result regarding the the multiplication of two
polynomials, so I tried to instead prove Vandermonde's inductively, as at
 https://math.stackexchange.com/questions/219928/inductive-proof-for-vandermondes-identity/219938  
 This too was difficult because the induction is not just on a single variable but rather on both
 n and r, and due to time constraints I did not finish. -/
lemma sum_for_vandermonde_with_n_is_zero (m r: ℕ) : sum_for_vandermonde m 0 r r = choose m r := 
begin
induction r with r ih,
{
   calc 
    sum_for_vandermonde m 0 0 0 = (choose m 0)*(choose 0 0) : by refl
    ... = choose m 0 : by simp
    },
calc 
    sum_for_vandermonde m 0 (nat.succ r) (nat.succ r) = sorry : sorry
    ... = choose m (nat.succ r): sorry
end

theorem vandermonde_identity (m n : ℕ) :
∀ r : ℕ, sum_for_vandermonde m n r r = choose (m + n) r := 
begin
induction n with n ih1,
{simp[choose, sum_for_vandermonde_with_n_is_zero]},
intro r, simp[sum_for_vandermonde, choose], sorry
end

/-
def choose : ℕ → ℕ → ℕ
| _             0 := 1
| 0       (k + 1) := 0
| (n + 1) (k + 1) := choose n k + choose n (succ k)
-/
