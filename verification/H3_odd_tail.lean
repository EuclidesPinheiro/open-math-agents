import Mathlib.NumberTheory.Primorial
import Mathlib.Tactic

namespace Erdos137OddTail

open Finset

def retainedCount (k : ℕ) : ℕ := k - ((range k).filter Nat.Prime).card

def rankBound (i : ℕ) : ℕ :=
  max i (max ((1260*(i-304)+352)/353) ((21701*(i-1492)+4999)/5000))

lemma rank_self_le (i : ℕ) : i ≤ rankBound i := le_max_left _ _

lemma rank_scaled (i : ℕ) : 21701*(i-1492) ≤ 5000*rankBound i := by
  have h : (21701*(i-1492)+4999)/5000 ≤ rankBound i :=
    (le_max_right _ _).trans (le_max_right _ _)
  omega

lemma rank_factorial_product (r : ℕ) (hr : 1492 ≤ r) :
    21701^(r-1492) * (r-1492).factorial ≤
      5000^(r-1492) * ∏ i ∈ range r, rankBound (i+1) := by
  have h (d : ℕ) : 21701^d * d.factorial ≤ 5000^d *
      ∏ i ∈ range (1492+d), rankBound (i+1) := by
    induction d with
    | zero =>
      simp only [pow_zero, Nat.factorial_zero, mul_one, one_mul, Nat.add_zero]
      exact one_le_prod' fun i _ => (Nat.succ_pos i).trans_le (rank_self_le (i+1))
    | succ d ih =>
      have hNew : 21701*(d+1) ≤ 5000*rankBound (1492+d+1) := by
        simpa only [show 1492+d+1-1492 = d+1 by omega] using rank_scaled (1492+d+1)
      rw [show 1492+d.succ = (1492+d)+1 by omega, prod_range_succ, pow_succ 21701,
        pow_succ 5000, Nat.factorial_succ]
      calc
        _ = (21701^d*d.factorial)*(21701*(d+1)) := by ac_rfl
        _ ≤ (5000^d*∏ i ∈ range (1492+d), rankBound (i+1))*
              (5000*rankBound (1492+d+1)) := Nat.mul_le_mul ih hNew
        _ = _ := by ac_rfl
  simpa only [Nat.add_sub_of_le hr] using h (r-1492)

lemma factorial_le_factorial_mul_pow (d s k : ℕ) (h : d+s ≤ k) :
    (d+s).factorial ≤ d.factorial*k^s := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [show d+s.succ = d+s+1 by omega, Nat.factorial_succ, pow_succ]
    exact (Nat.mul_le_mul h (ih (by omega))).trans_eq (Nat.mul_comm _ _)

lemma tail_rank_contradiction (k P : ℕ) (hk : 2^21 ≤ k) (hP : P ≤ k)
    (hRatio : 120*(P+1492) ≤ 11*k) (hPower : (k^(P+1492))^12 ≤ 2^(23*k)) :
    (k-1).factorial < ∏ i ∈ range (k-P), rankBound (i+1) := by
  let d := k-P-1492
  have hD : 109*k ≤ 120*d := by dsimp [d]; omega
  have hS : d+(P+1492) = k := by dsimp [d]; omega
  have hUpper : (k-1).factorial ≤ d.factorial*k^(P+1492) :=
    (Nat.factorial_le (by omega)).trans (factorial_le_factorial_mul_pow d (P+1492) k hS.le)
  have hBase : (5000:ℚ)^109*2^230 < 21701^109 := by norm_num
  have hStep : (2:ℚ)^230 < (21701/5000)^109 := by
    rw [div_pow]
    exact (lt_div_iff₀ (by positivity)).2 (by simpa only [mul_comm] using hBase)
  have hPowerQ : ((k:ℚ)^(P+1492))^12 ≤ (2:ℚ)^(23*k) := by exact_mod_cast hPower
  have hStrict : (k:ℚ)^(P+1492) < (21701/5000 : ℚ)^d := by
    apply lt_of_pow_lt_pow_left₀ 120 (by positivity)
    calc
      ((k:ℚ)^(P+1492))^120 = (((k:ℚ)^(P+1492))^12)^10 := by rw [← pow_mul]; rfl
      _ ≤ ((2:ℚ)^(23*k))^10 := pow_le_pow_left₀ (by positivity) hPowerQ _
      _ = ((2:ℚ)^230)^k := by simp only [← pow_mul]; congr 1; omega
      _ < ((21701/5000 : ℚ)^109)^k := pow_lt_pow_left₀ hStep (by positivity) (by omega)
      _ = (21701/5000 : ℚ)^(109*k) := by rw [pow_mul]
      _ ≤ (21701/5000 : ℚ)^(d*120) := pow_le_pow_right₀ (by norm_num) (by omega)
      _ = ((21701/5000 : ℚ)^d)^120 := pow_mul _ _ _
  have hRank := rank_factorial_product (k-P) (by omega : 1492 ≤ k-P)
  have hRankQ : (21701/5000 : ℚ)^d*(d.factorial : ℚ) ≤
      (∏ i ∈ range (k-P), rankBound (i+1) : ℕ) := by
    rw [div_pow, div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity)).2
    exact_mod_cast (show 21701^d*d.factorial ≤
      (∏ i ∈ range (k-P), rankBound (i+1))*5000^d by simpa only [d, mul_comm] using hRank)
  have hFinal : ((k-1).factorial : ℚ) < (∏ i ∈ range (k-P), rankBound (i+1) : ℕ) :=
    (show ((k-1).factorial : ℚ) ≤ (d.factorial : ℚ)*(k:ℚ)^(P+1492) by exact_mod_cast hUpper).trans_lt
      ((mul_lt_mul_of_pos_left hStrict (by exact_mod_cast Nat.factorial_pos d)).trans_le
        (by simpa only [mul_comm] using hRankQ))
  exact_mod_cast hFinal

end Erdos137OddTail
