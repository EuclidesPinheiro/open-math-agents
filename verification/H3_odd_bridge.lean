import Mathlib.NumberTheory.Primorial
import Mathlib.Tactic

namespace Erdos137OddBridge

open Finset

def rankBound (i : ℕ) : ℕ :=
  max i (max ((1260*(i-304)+352)/353) ((21701*(i-1492)+4999)/5000))

def retainedCount (k : ℕ) : ℕ := k - ((range k).filter Nat.Prime).card

lemma retained_count_mono : Monotone retainedCount := by
  have h (k : ℕ) : retainedCount k = ((range k).filter (fun p => ¬p.Prime)).card := by
    unfold retainedCount
    have hCount := card_filter_add_card_filter_not (s := range k) Nat.Prime
    rw [card_range] at hCount
    omega
  intro k m hm
  rw [h,h]
  exact card_le_card (filter_subset_filter _ (range_mono hm))

lemma rank_scaled_first (i : ℕ) : 1260*(i-304) ≤ 353*rankBound i := by
  have h : (1260*(i-304)+352)/353 ≤ rankBound i :=
    (le_max_left _ _).trans (le_max_right _ _)
  omega

lemma rank_scaled_second (i : ℕ) : 21701*(i-1492) ≤ 5000*rankBound i := by
  have h : (21701*(i-1492)+4999)/5000 ≤ rankBound i :=
    (le_max_right _ _).trans (le_max_right _ _)
  omega

lemma extend_rank_power {t i a b c j : ℕ} (ht : 0 < t) (hti : t ≤ i) (ha : a ≤ t)
    (hb : 0 < b) (hWitness : 2^j*(b*t)^64 ≤ (c*(t-a))^64)
    (hRank : c*(i-a) ≤ b*rankBound i) :
    2^j*i^64 ≤ (rankBound i)^64 := by
  have hSub : (t-a)*i ≤ (i-a)*t := by
    have hA := Nat.sub_add_cancel ha
    have hB := Nat.sub_add_cancel (ha.trans hti)
    have hProd := Nat.mul_le_mul_left a hti
    nlinarith
  have hSlope : c*(t-a)*i ≤ b*rankBound i*t :=
    (show c*(t-a)*i ≤ c*(i-a)*t by
      simpa only [mul_assoc] using Nat.mul_le_mul_left c hSub).trans (Nat.mul_le_mul_right t hRank)
  have hGoal : (b*t)^64*(2^j*i^64) ≤ (b*t)^64*(rankBound i)^64 := by
    calc
      _ = (2^j*(b*t)^64)*i^64 := by ac_rfl
      _ ≤ (c*(t-a))^64*i^64 := Nat.mul_le_mul_right _ hWitness
      _ = (c*(t-a)*i)^64 := by rw [mul_pow]
      _ ≤ (b*rankBound i*t)^64 := pow_le_pow_left' hSlope _
      _ = _ := by rw [show b*rankBound i*t = b*t*rankBound i by ac_rfl, mul_pow]
  exact Nat.le_of_mul_le_mul_left hGoal (by positivity)

lemma rank_power_at {t i j : ℕ} (ht : 0 < t) (hti : t ≤ i)
    (hW : (304 ≤ t ∧ 2^j*(353*t)^64 ≤ (1260*(t-304))^64) ∨
      (1492 ≤ t ∧ 2^j*(5000*t)^64 ≤ (21701*(t-1492))^64)) :
    2^j*i^64 ≤ (rankBound i)^64 := by
  rcases hW with ⟨hA,hW⟩ | ⟨hA,hW⟩
  · exact extend_rank_power ht hti hA (by decide) hW (rank_scaled_first i)
  · exact extend_rank_power ht hti hA (by decide) hW (rank_scaled_second i)

def gainedExponent (thresholds : List ℕ) (r : ℕ) : ℕ :=
  (thresholds.map fun t => r-(t-1)).sum

lemma sum_rank_gains (thresholds : List ℕ) (r : ℕ) :
    gainedExponent thresholds r =
      ∑ i ∈ range r, (thresholds.filter fun t => t ≤ i+1).length := by
  have hCount (t : ℕ) : (∑ i ∈ range r, if t ≤ i+1 then 1 else 0) = r-(t-1) := by
    rw [← sum_filter]
    simp only [sum_const, nsmul_eq_mul, mul_one]
    have hSet : (range r).filter (fun i => t ≤ i+1) = Ico (t-1) r := by
      ext i
      simp only [mem_filter,mem_range,mem_Ico]
      omega
    rw [hSet, Nat.card_Ico]
  induction thresholds with
  | nil => simp [gainedExponent]
  | cons t ts ih =>
    have hT := hCount t
    simp only [gainedExponent,List.map_cons,List.sum_cons] at ih ⊢
    have hStep (i : ℕ) : ((t::ts).filter fun v => v ≤ i+1).length =
        (if t ≤ i+1 then 1 else 0) + (ts.filter fun v => v ≤ i+1).length := by
      by_cases hti : t ≤ i+1 <;> simp [List.filter_cons, hti, Nat.add_comm]
    simp_rw [hStep,sum_add_distrib]
    rw [hT, ih]

def carriesRankPower (t j : ℕ) : Prop :=
  0 < t ∧ ((304 ≤ t ∧ 2^j*(353*t)^64 ≤ (1260*(t-304))^64) ∨
    (1492 ≤ t ∧ 2^j*(5000*t)^64 ≤ (21701*(t-1492))^64))

instance (t j : ℕ) : Decidable (carriesRankPower t j) := by
  unfold carriesRankPower
  infer_instance

def RankThresholds (thresholds : List ℕ) (offset : ℕ) : Prop := match thresholds with
  | [] => True
  | t :: ts => carriesRankPower t (offset+1) ∧ RankThresholds ts (offset+1)

instance (thresholds : List ℕ) (offset : ℕ) : Decidable (RankThresholds thresholds offset) := by
  induction thresholds generalizing offset with
  | nil => unfold RankThresholds; infer_instance
  | cons t ts ih =>
    unfold RankThresholds
    letI := ih (offset+1)
    infer_instance

lemma rank_power_of_thresholds (ts : List ℕ) (j i : ℕ) (hT : RankThresholds ts j)
    (hN : 0 < (ts.filter fun t => t ≤ i).length) :
    2^(j+(ts.filter fun t => t ≤ i).length)*i^64 ≤ (rankBound i)^64 := by
  induction ts generalizing j with
  | nil => simpa using hN
  | cons t ts ih =>
    obtain ⟨hW,hTs⟩ := hT
    let r := (ts.filter fun t => t ≤ i).length
    have hCount : ((t::ts).filter fun t => t ≤ i).length = (if t ≤ i then 1 else 0)+r := by
      by_cases h : t ≤ i <;> simp [List.filter_cons,h,r,Nat.add_comm]
    rw [hCount] at hN ⊢
    by_cases hR : 0 < r
    · apply (Nat.mul_le_mul_right (i^64) (Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) ?_)).trans
        (ih (j+1) hTs hR)
      split <;> omega
    · have hLE : t ≤ i := by by_contra! hh; simp [hh, show r = 0 by omega] at hN
      simp only [if_pos hLE, show r = 0 by omega, Nat.add_zero]
      exact rank_power_at hW.1 hLE hW.2

lemma rank_product_power (ts : List ℕ) (r : ℕ) (hT : RankThresholds ts 0) :
    2^(gainedExponent ts r)*(r.factorial)^64 ≤
      (∏ i ∈ range r, rankBound (i+1))^64 := by
  let g := fun i : ℕ => (ts.filter fun t => t ≤ i+1).length
  have hFact : (∏ i ∈ range r, (i+1)) = r.factorial := by
    induction r with
    | zero => simp
    | succ r ih => rw [prod_range_succ, ih, Nat.factorial_succ, Nat.mul_comm]
  rw [sum_rank_gains, ← Finset.prod_pow_eq_pow_sum, ← hFact, ← Finset.prod_pow,
    ← Finset.prod_mul_distrib, ← Finset.prod_pow]
  apply prod_le_prod'
  intro i _
  by_cases hi : 0 < g i
  · simpa only [g,Nat.zero_add] using rank_power_of_thresholds ts 0 (i+1) hT hi
  · simpa [g, show g i = 0 by omega] using
      (pow_le_pow_left' (show i+1 ≤ rankBound (i+1) from le_max_left _ _) 64)

lemma factorial_mul_bound (r d U : ℕ) (h : r+d ≤ U) :
    (r+d).factorial ≤ r.factorial*U^d := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [show r+d.succ = r+d+1 by omega, Nat.factorial_succ,pow_succ]
    exact (Nat.mul_le_mul h (ih (by omega))).trans_eq (by ac_rfl)

lemma rank_product_on_interval (ts : List ℕ) (lo hi P B k : ℕ)
    (hT : RankThresholds ts 0) (hLo : 3 ≤ lo) (hk₁ : lo ≤ k) (hk₂ : k ≤ hi)
    (hCount : ((range lo).filter Nat.Prime).card ≤ P)
    (hBudget : (hi-1)^64 ≤ 2^B)
    (hGain : (hi-1-(lo-P))*B < gainedExponent ts (lo-P)) :
    (k-1).factorial < ∏ i ∈ range (retainedCount k), rankBound (i+1) := by
  let r := lo-P
  have hrK : r ≤ retainedCount k := by
    apply le_trans _ (retained_count_mono hk₁)
    unfold retainedCount
    dsimp [r]
    omega
  have hProd := rank_product_power ts r hT
  by_cases hr : r ≤ hi-1
  · have hUpper : (k-1).factorial ≤ r.factorial*(hi-1)^(hi-1-r) := by
      apply (Nat.factorial_le (by omega : k-1 ≤ hi-1)).trans
      have h := factorial_mul_bound r (hi-1-r) (hi-1) (by omega)
      rwa [show r+(hi-1-r) = hi-1 by omega] at h
    have hRaised : ((k-1).factorial)^64 ≤ 2^((hi-1-r)*B)*(r.factorial)^64 := by
      calc
        _ ≤ (r.factorial*(hi-1)^(hi-1-r))^64 := pow_le_pow_left' hUpper _
        _ = ((hi-1)^64)^(hi-1-r)*(r.factorial)^64 := by
          rw [mul_pow, mul_comm]; congr 1
          rw [← pow_mul, ← pow_mul, Nat.mul_comm]
        _ ≤ (2^B)^(hi-1-r)*(r.factorial)^64 :=
          Nat.mul_le_mul_right _ (pow_le_pow_left' hBudget _)
        _ = _ := by rw [← pow_mul, Nat.mul_comm B]
    have hL : ((k-1).factorial)^64 < (∏ i ∈ range r, rankBound (i+1))^64 :=
      hRaised.trans_lt ((Nat.mul_lt_mul_of_pos_right (Nat.pow_lt_pow_right (by decide) hGain)
        (by positivity)).trans_le hProd)
    exact (lt_of_pow_lt_pow_left' 64 hL).trans_le (prod_le_prod_of_subset_of_one_le'
      (range_mono hrK) (fun i _ _ => (Nat.succ_pos i).trans_le (le_max_left _ _)))
  · have hFac : (k-1).factorial < r.factorial :=
      Nat.factorial_lt (by omega) (by omega)
    have hProd' : r.factorial ≤ ∏ i ∈ range r, rankBound (i+1) := by
      apply le_of_pow_le_pow_left' (by decide : 64 ≠ 0)
      exact (Nat.le_mul_of_pos_left _ (by positivity)).trans hProd
    exact hFac.trans_le (hProd'.trans (prod_le_prod_of_subset_of_one_le'
      (range_mono hrK) (fun i _ _ => (Nat.succ_pos i).trans_le (le_max_left _ _))))

end Erdos137OddBridge
