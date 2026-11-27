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

set_option maxRecDepth 10000 in
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
  have h' := h (r-1492)
  rwa [show 1492+(r-1492) = r by omega] at h'

lemma factorial_le_factorial_mul_pow (d s k : ℕ) (h : d+s ≤ k) :
    (d+s).factorial ≤ d.factorial*k^s := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [show d+s.succ = d+s+1 by omega, Nat.factorial_succ, pow_succ]
    exact (Nat.mul_le_mul h (ih (by omega))).trans_eq (by ac_rfl)

set_option maxRecDepth 10000 in
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
      ((k:ℚ)^(P+1492))^120 = (((k:ℚ)^(P+1492))^12)^10 := by
        simp only [← pow_mul, Nat.mul_assoc]
      _ ≤ ((2:ℚ)^(23*k))^10 := pow_le_pow_left₀ (by positivity) hPowerQ _
      _ = ((2:ℚ)^230)^k := by rw [← pow_mul, ← pow_mul]; congr 1; omega
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

lemma dyadic_exists (k p : ℕ) (hp : 0 < p) : ∃ j : ℕ, k ≤ 2^j*p :=
  ⟨k.log2+1, Nat.lt_log2_self.le.trans (Nat.le_mul_of_pos_right _ hp)⟩

noncomputable def dyadicHeight (k p : ℕ) : ℕ :=
  if hp : 0 < p then Nat.find (dyadic_exists k p hp) else 0

lemma le_dyadic_height (k p : ℕ) (hp : 0 < p) : k ≤ 2^(dyadicHeight k p)*p := by
  unfold dyadicHeight
  rw [dif_pos hp]
  exact Nat.find_spec (dyadic_exists k p hp)

lemma dyadic_height_le (k p i : ℕ) (hp : 0 < p) (hi : k ≤ 2^i*p) : dyadicHeight k p ≤ i := by
  unfold dyadicHeight
  rw [dif_pos hp]
  exact Nat.find_min' (dyadic_exists k p hp) hi

lemma filter_sum_one (S : Finset ℕ) (f : ℕ → Prop) [DecidablePred f] :
    (∑ j ∈ S, if f j then 1 else 0) = (S.filter f).card := by
  rw [← sum_filter]
  simp

lemma height_sum_bound (k : ℕ) :
    (∑ p ∈ (k-1).primesLE, dyadicHeight k p) ≤
      ∑ i ∈ range (k.log2+1), (k/2^i).primesLE.card := by
  let P := (k-1).primesLE
  let J := range (k.log2+1)
  have hHeight (p : ℕ) (hp : p ∈ P) : dyadicHeight k p =
      ∑ i ∈ J, if i < dyadicHeight k p then 1 else 0 := by
    have hp' := (mem_filter.mp hp).2
    have hb := dyadic_height_le k p (k.log2+1) hp'.pos
      (Nat.lt_log2_self.le.trans (Nat.le_mul_of_pos_right _ hp'.pos))
    have hEq : J.filter (· < dyadicHeight k p) = range (dyadicHeight k p) := by
      ext i
      simp only [J, mem_filter, mem_range]
      omega
    rw [filter_sum_one, hEq, card_range]
  calc
    _ = ∑ p ∈ P, ∑ i ∈ J, if i < dyadicHeight k p then 1 else 0 :=
      sum_congr rfl hHeight
    _ = ∑ i ∈ J, ∑ p ∈ P, if i < dyadicHeight k p then 1 else 0 := sum_comm
    _ ≤ _ := by
      apply sum_le_sum
      intro i _
      rw [filter_sum_one]
      apply card_le_card
      intro p hp
      have hp' := (mem_filter.mp (mem_filter.mp hp).1).2
      have hi := (mem_filter.mp hp).2
      have hPow : 2^i*p < k := by
        by_contra! h
        exact (not_le_of_gt hi) (dyadic_height_le k p i hp'.pos h)
      have hDiv : p ≤ k/2^i := (Nat.le_div_iff_mul_le (by positivity)).2 (by simpa [mul_comm] using hPow.le)
      exact mem_filter.mpr ⟨mem_range.mpr (by omega), hp'⟩

lemma sum_dyadic_div_le (k e : ℕ) : (∑ j ∈ range e, k/2^j) ≤ 2*k := by
  induction e generalizing k with
  | zero => simp
  | succ e ih =>
    rw [sum_range_succ']
    have h : (∑ j ∈ range e, k/2^(j+1)) = ∑ j ∈ range e, (k/2)/2^j := by
      apply sum_congr rfl
      intro j _
      rw [pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm 2]
    rw [h, pow_zero, Nat.div_one]
    have := ih (k/2)
    omega

lemma dyadic_exponential_absorption (C : ℕ) (hC : C*22 ≤ 2^21) (e : ℕ) (he : 21 ≤ e) :
    C*(e+1) ≤ 2^e := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le he
  clear he
  induction d with
  | zero => exact hC
  | succ d ih =>
    have hStep : C*(21+d+1+1) ≤ 2*(C*(21+d+1)) := by nlinarith
    rw [show 21+d.succ = (21+d)+1 by omega,pow_succ]
    exact hStep.trans (by simpa only [mul_comm] using Nat.mul_le_mul_left 2 ih)

lemma dyadic_budget_arithmetic {k P e w : ℕ} (hk : 2097152 ≤ k)
    (hw : 128*w ≤ 26*k+837376*(e+1)) (hA : 91588*(e+1) ≤ k)
    (hB : 89520*(e+1) ≤ k) (hP : 168*P ≤ 8*w+13*k) :
    120*(P+1492) ≤ 11*k ∧ 12*(8*w+13*k+11936*(e+1)) ≤ 184*k := by
  have hw' : 448*w ≤ 123*k := by omega
  have hp' : 9408*P ≤ 851*k := by omega
  exact ⟨by omega, by omega⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
lemma tail_from_prime_estimates (k : ℕ) (hk : 2^21 ≤ k)
    (hPrimorial : ∀ n : ℕ, (primorial n)^8 ≤ 2^(13*n))
    (hPrimeCount : ∀ n : ℕ, 128*n.primesLE.card ≤ 13*n+128*6542) :
    (k-1).factorial < ∏ i ∈ range (retainedCount k), rankBound (i+1) := by
  let P := ((range k).filter Nat.Prime).card
  let e := k.log2
  let w := ∑ p ∈ (k-1).primesLE, dyadicHeight k p
  have hK : 0 < k := by omega
  have hProd : (k-1).primesLE = (range k).filter Nat.Prime := by
    unfold Nat.primesLE Nat.primesBelow
    rw [show k-1+1 = k by omega]
  have hP : P ≤ k := by
    simpa only [P,card_range] using card_filter_le (s := range k) Nat.Prime
  have hBounds := (Nat.log2_eq_iff hK.ne').mp (show k.log2 = e from rfl)
  have he : 21 ≤ e := (Nat.le_log2 hK.ne').2 hk
  have hAbsorb : 14*6542*(e+1) ≤ k := (dyadic_exponential_absorption (14*6542) (by decide) e he).trans hBounds.1
  have hOffset : 60*1492*(e+1) ≤ k := (dyadic_exponential_absorption (60*1492) (by decide) e he).trans hBounds.1
  have hW : 128*w ≤ 26*k+128*6542*(e+1) := by
    calc
      _ ≤ 128*(∑ j ∈ range (e+1), (k/2^j).primesLE.card) :=
        Nat.mul_le_mul_left 128 (height_sum_bound k)
      _ = ∑ j ∈ range (e+1), 128*(k/2^j).primesLE.card := by rw [mul_sum]
      _ ≤ ∑ j ∈ range (e+1), (13*(k/2^j)+128*6542) := sum_le_sum (fun j _ => hPrimeCount _)
      _ = 13*(∑ j ∈ range (e+1), k/2^j)+128*6542*(e+1) := by
        simp only [sum_add_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul, Nat.cast_id]
        rw [Nat.mul_comm (e+1)]
      _ ≤ _ := Nat.add_le_add_right (Nat.mul_le_mul_left 13 (sum_dyadic_div_le k (e+1))) _
  have hKProd : k^P ≤ 2^w*primorial (k-1) := by
    rw [primorial_eq_prod_primesLE, show 2^w = ∏ p ∈ (k-1).primesLE, 2^(dyadicHeight k p) by
      exact (Finset.prod_pow_eq_pow_sum _ _ _).symm, ← Finset.prod_mul_distrib]
    calc
      _ = ∏ _ ∈ (k-1).primesLE, k := by rw [prod_const, hProd]
      _ ≤ _ := prod_le_prod' fun p hp => le_dyadic_height k p (mem_filter.mp hp).2.pos
  have hK8 : (k^P)^8 ≤ 2^(8*w+13*k) := by
    calc
      _ ≤ (2^w*primorial (k-1))^8 := pow_le_pow_left' hKProd _
      _ = 2^(w*8)*(primorial (k-1))^8 := by rw [mul_pow, ← pow_mul]
      _ ≤ 2^(w*8)*2^(13*(k-1)) := Nat.mul_le_mul_left _ (hPrimorial _)
      _ = 2^(w*8+13*(k-1)) := by rw [pow_add]
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
  have hPi : 168*P ≤ 8*w+13*k := by
    have hh : (2^21 : ℕ)^(P*8) ≤ 2^(8*w+13*k) :=
      (pow_le_pow_left' hk _).trans (by simpa only [pow_mul] using hK8)
    rw [← pow_mul] at hh
    by_contra! h
    exact (not_lt_of_ge hh) (Nat.pow_lt_pow_right (by decide) (by omega))
  obtain ⟨hCoeff,hExp⟩ := dyadic_budget_arithmetic (k := k) (P := P) (e := e) (w := w) hk
    hW hAbsorb hOffset hPi
  have hQ : (k^(P+1492))^8 ≤ 2^(8*w+13*k+8*1492*(e+1)) := by
    have hKExtra : (k^1492)^8 ≤ 2^(8*1492*(e+1)) := by
      calc
        _ ≤ ((2^(e+1))^1492)^8 := pow_le_pow_left' (pow_le_pow_left' hBounds.2.le _) _
        _ = _ := by simp only [← pow_mul]; congr 1; omega
    rw [pow_add, mul_pow, pow_add]
    exact Nat.mul_le_mul hK8 hKExtra
  have hPower : (k^(P+1492))^12 ≤ 2^(23*k) := by
    have hh : ((k^(P+1492))^12)^8 ≤ (2^(23*k))^8 := by
      calc
        _ = ((k^(P+1492))^8)^12 := by simp only [← pow_mul]; rfl
        _ ≤ (2^(8*w+13*k+8*1492*(e+1)))^12 := pow_le_pow_left' hQ _
        _ ≤ (2^(23*k))^8 := by
          rw [← pow_mul, ← pow_mul]
          exact Nat.pow_le_pow_right (by decide) (by omega)
    by_contra! h
    exact (not_lt_of_ge hh) (Nat.pow_lt_pow_left h (by decide))
  exact tail_rank_contradiction k P hk hP hCoeff hPower

end Erdos137OddTail
