import data.nat.choose
import data.set
import data.set.finite
import data.multiset
import data.finset
import data.list
import data.finset algebra.big_operators
import algebra.big_operators
import init.algebra.functions
#eval choose 5 4
#check nat.rec_on


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

/- sum_for_hockey_stick takes m, n, r, and k and computes the sum from k = 0 to i of
(m choose k)*(n choose r - k), which is what we'll use in Vandermonde's identity 
with i = r -/
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

/- Vandermonde's identity says that m + n choose r equals the 
sum from k = 0 to r of (m choose k)*(n choose r - k)
-/
variables x y: ℕ

theorem binomial_theorem_with_1 (x y n : ℕ) : 
    ∀ n : ℕ, (x + 1)^n = (finset.range (nat.succ n)).sum (λ m, x ^ m * choose n m) :=
    begin
    have h2: (x + y) ^ n = (finset.range (nat.succ n)).sum (λ m, x ^ m * y ^ (n - m) * ↑(choose n m)), 
        by apply add_pow x y n,
    let h1: y = 1,
    
    rw h1 at h2
    end

    /-(x + 1)^n = (finset.range (nat.succ n)).sum (λ m, x ^ m * choose n m)-/

theorem vandermonde_identity (m n r : ℕ) :
sum_for_vandermonde m n r r = choose (m + n) r := 
begin
induction n with n ih,
{sorry},
sorry
end