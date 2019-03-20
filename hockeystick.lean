import data.nat.choose
import data.set
import data.set.finite
import data.multiset
import data.finset
import data.list
import data.finset algebra.big_operators
#eval choose 5 4
#check nat.rec_on

/- Following the proof at https://artofproblemsolving.com/wiki/index.php/Combinatorial_identity -/

/- sum_for_hockey_stick takes r and k and computes the sum from i = r 
to i = r + k of (i choose r) -/
def sum_for_hockey_stick (r : ℕ) (k : ℕ) : ℕ := 
nat.rec_on k 1 (λ k ih, ih + (choose (r + k + 1) r))

#eval sum_for_hockey_stick  5 0
#eval sum_for_hockey_stick 5 1
#eval sum_for_hockey_stick 5 2
#eval sum_for_hockey_stick 5 3

/- Says that for natural numbers r and n, if n > r, then the sum from i = r to n 
of i choose r equals n + 1 choose r + 1 -/
theorem hockey_stick_identity (n : ℕ) (r : ℕ) :
n > r → (sum_for_hockey_stick r (n - r)) = (choose (n + 1) (r + 1)) :=
sorry