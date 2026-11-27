import Mathlib.NumberTheory.Primorial
import Mathlib.FieldTheory.Finite.Basic
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
      _ = (c*(t-a)*i)^64 := by rw [← mul_pow]
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
  have hCount (t : ℕ) : (∑ i ∈ range r, if t ≤ i+1 then (1:ℕ) else 0) = r-(t-1) := by
    rw [← sum_filter]
    simp only [sum_const, nsmul_eq_mul, mul_one]
    have hSet : (range r).filter (fun i => t ≤ i+1) = Ico (t-1) r := by
      ext i
      simp only [mem_filter,mem_range,mem_Ico]
      omega
    rw [hSet, Nat.card_Ico]
    simp
  induction thresholds with
  | nil => simp [gainedExponent]
  | cons t ts ih =>
    have hT := hCount t
    simp only [gainedExponent,List.map_cons,List.sum_cons] at ih ⊢
    have hStep (i : ℕ) : ((t::ts).filter fun v => v ≤ i+1).length =
        (if t ≤ i+1 then 1 else 0) + (ts.filter fun v => v ≤ i+1).length := by
      by_cases hti : t ≤ i+1 <;> simp [hti, Nat.add_comm]
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
      by_cases h : t ≤ i <;> simp [h,r,Nat.add_comm]
    rw [hCount] at hN ⊢
    by_cases hR : 0 < r
    · apply (Nat.mul_le_mul_right (i^64) (Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) ?_)).trans
        (ih (j+1) hTs hR)
      split <;> omega
    · have hLE : t ≤ i := by
        by_contra hh
        rw [if_neg hh] at hN
        omega
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
      Nat.factorial_lt_of_lt (by omega) (by omega)
    have hProd' : r.factorial ≤ ∏ i ∈ range r, rankBound (i+1) := by
      by_contra! h
      have hI := Nat.pow_lt_pow_left h (by decide : (64:ℕ) ≠ 0)
      exact (not_lt_of_ge ((Nat.le_mul_of_pos_left _ (by positivity)).trans hProd)) hI
    exact hFac.trans_le (hProd'.trans (prod_le_prod_of_subset_of_one_le'
      (range_mono hrK) (fun i _ _ => (Nat.succ_pos i).trans_le (le_max_left _ _))))

private def modPowByBits (a e m : ℕ) : ℕ → ℕ
  | 0 => 1 % m
  | fuel+1 =>
      if e = 0 then 1 % m else
        let next := modPowByBits (a*a%m) (e/2) m fuel
        if e%2 = 0 then next else a*next%m

private lemma mod_pow_by_bits_eq (a e m fuel : ℕ) (h : e < 2^fuel) :
    modPowByBits a e m fuel = a^e%m := by
  induction fuel generalizing a e with
  | zero =>
    have he : e = 0 := by simp at h; omega
    simp [modPowByBits,he]
  | succ fuel ih =>
    by_cases he : e = 0
    · simp [modPowByBits,he]
    have hHalf : e/2 < 2^fuel := by rw [pow_succ] at h; omega
    have hRest := ih (a*a%m) (e/2) hHalf
    have hRest' : (a*a%m)^(e/2)%m = a^(2*(e/2))%m := by
      rw [pow_mul, pow_two, ← Nat.pow_mod]
    simp only [modPowByBits,if_neg he,hRest,hRest']
    by_cases hEven : e%2 = 0
    · rw [if_pos hEven, show 2*(e/2) = e by omega]
    · rw [if_neg hEven]
      conv_rhs => rw [show e = 2*(e/2)+1 by omega, pow_succ' a]
      calc
        _ = (a%m*(a^(2*(e/2))%m))%m := by rw [Nat.mul_mod a, Nat.mod_mod]
        _ = _ := (Nat.mul_mod a _ m).symm

def fermatCandidate (n : ℕ) : Prop :=
  n = 2 ∨ n = 3 ∨ n = 5 ∨ n = 7 ∨
    (7 < n ∧ n.Coprime 210 ∧ modPowByBits 2 (n-1) n n.log2.succ = 1)

instance (n : ℕ) : Decidable (fermatCandidate n) := by
  unfold fermatCandidate
  infer_instance

lemma prime_is_fermat_candidate {p : ℕ} (hp : p.Prime) : fermatCandidate p := by
  by_cases h : p ≤ 7
  · interval_cases p <;> first | decide | exact False.elim ((show ¬Nat.Prime _ by decide) hp)
  unfold fermatCandidate
  right; right; right; right
  have hC : ∀ d : ℕ, 0 < d → d < p → p.Coprime d := fun d hd hd' =>
    (hp.coprime_iff_not_dvd).2 (fun hD => (not_le_of_gt hd') (Nat.le_of_dvd hd hD))
  have hSmall : p.Coprime 210 := by
    change p.Coprime (2*3*5*7)
    exact (((hC 2 (by decide) (by omega)).mul_right (hC 3 (by decide) (by omega))).mul_right
      (hC 5 (by decide) (by omega))).mul_right (hC 7 (by decide) (by omega))
  refine ⟨by omega,hSmall,?_⟩
  have hF : 2^(p-1)%p = 1%p := Nat.ModEq.pow_card_sub_one_eq_one hp (hC 2 (by decide) (by omega)).symm
  rw [mod_pow_by_bits_eq _ _ _ _ (by have := Nat.lt_log2_self (n := p); omega),
    hF, Nat.mod_eq_of_lt (by omega : 1 < p)]

def candidatePrefix (n : ℕ) : Finset ℕ := (range n).filter fermatCandidate

def candidateCount (a b : ℕ) : ℕ := ((Ico a b).filter fermatCandidate).card

lemma candidate_prefix_add {a b : ℕ} (hab : a ≤ b) :
    (candidatePrefix b).card = (candidatePrefix a).card + candidateCount a b := by
  have hEq : candidatePrefix b = candidatePrefix a ∪ (Ico a b).filter fermatCandidate := by
    ext n
    simp only [candidatePrefix,mem_filter,mem_range,mem_union,mem_Ico]
    grind
  have hDis : Disjoint (candidatePrefix a) ((Ico a b).filter fermatCandidate) := by
    rw [Finset.disjoint_left]
    intro n h₁ h₂
    simp only [candidatePrefix,mem_filter,mem_range,mem_Ico] at h₁ h₂
    omega
  rw [hEq, Finset.card_union_of_disjoint hDis, candidateCount]

structure RankInterval where
  upper : ℕ
  budget : ℕ
  increment : ℕ

def RankIntervals (ts : List ℕ) (start stop available : ℕ) (rows : List RankInterval) : Prop :=
  match rows with
  | [] => stop < start
  | row :: rest =>
      start ≤ row.upper ∧ (row.upper-1)^64 ≤ 2^row.budget ∧
      (row.upper-1-(start-available))*row.budget < gainedExponent ts (start-available) ∧
      candidateCount start (row.upper+1) ≤ row.increment ∧
      RankIntervals ts (row.upper+1) stop (available+row.increment) rest

instance (ts : List ℕ) (start stop available : ℕ) (rows : List RankInterval) :
    Decidable (RankIntervals ts start stop available rows) := by
  induction rows generalizing start available with
  | nil => unfold RankIntervals; infer_instance
  | cons row rest ih =>
    unfold RankIntervals
    letI := ih (row.upper+1) (available+row.increment)
    infer_instance

lemma rank_intervals_bound (ts : List ℕ) (start stop available k : ℕ) (rows : List RankInterval)
    (hT : RankThresholds ts 0) (hStart : 3 ≤ start) (hk : start ≤ k) (hStop : k ≤ stop)
    (hP : (candidatePrefix start).card ≤ available)
    (hRows : RankIntervals ts start stop available rows) :
    (k-1).factorial < ∏ i ∈ range (retainedCount k), rankBound (i+1) := by
  induction rows generalizing start available with
  | nil => exact (not_lt_of_ge (hk.trans hStop) hRows).elim
  | cons row rows ih =>
    obtain ⟨hUpper,hBudget,hGain,hInc,hNext⟩ := hRows
    by_cases hK : k ≤ row.upper
    · have hCount : ((range start).filter Nat.Prime).card ≤ available :=
        (card_le_card (show (range start).filter Nat.Prime ⊆ candidatePrefix start from
          fun p hp => mem_filter.mpr ⟨(mem_filter.mp hp).1,prime_is_fermat_candidate (mem_filter.mp hp).2⟩)).trans hP
      exact rank_product_on_interval ts start row.upper available row.budget k hT hStart hk hK
        hCount hBudget hGain
    · apply ih (row.upper+1) (available+row.increment) (by omega) (by omega) _ hNext
      rw [candidate_prefix_add (by omega : start ≤ row.upper+1)]
      exact Nat.add_le_add hP hInc

private def dyadicRankThresholds : List ℕ := [
  425, 426, 428, 430, 432, 434, 436, 438, 440, 442, 445, 447, 449, 452, 454,
  456, 459, 461, 464, 467, 469, 472, 475, 478, 481, 484, 487, 490, 494, 497,
  500, 504, 508, 511, 515, 519, 523, 527, 531, 536, 540, 545, 550, 554, 559,
  565, 570, 575, 581, 587, 593, 599, 605, 612, 619, 626, 633, 641, 648, 656,
  665, 674, 683, 692, 702, 712, 722, 733, 745, 757, 769, 782, 796, 810, 825,
  840, 857, 874, 892, 912, 932, 953, 976, 1000, 1025, 1053, 1082, 1113, 1146, 1181,
  1220, 1261, 1306, 1354, 1407, 1465, 1528, 1598, 1676, 1763, 1860, 1970, 2094, 2238, 2404,
  2600, 2833, 3115, 3463, 3905, 4483, 5273, 6414, 7172, 7482, 7824, 8203, 8626, 9099, 9634,
  10243, 10941, 11752, 12703, 13835, 15205, 16895, 19035, 21830, 25635, 31118, 39702, 55056, 90393, 257409
]

private def dyadicRankIntervals : List RankInterval := [
  ⟨30041, 952, 3⟩, ⟨30081, 953, 3⟩, ⟨30123, 953, 7⟩, ⟨30162, 953, 4⟩,
  ⟨30202, 953, 4⟩, ⟨30243, 953, 4⟩, ⟨30285, 953, 4⟩, ⟨30328, 953, 5⟩,
  ⟨30372, 953, 3⟩, ⟨30415, 954, 3⟩, ⟨30460, 954, 3⟩, ⟨30508, 954, 5⟩,
  ⟨30557, 954, 6⟩, ⟨30606, 954, 3⟩, ⟨30658, 954, 4⟩, ⟨30709, 955, 7⟩,
  ⟨30759, 955, 3⟩, ⟨30812, 955, 5⟩, ⟨30867, 955, 7⟩, ⟨30921, 955, 6⟩,
  ⟨30976, 955, 5⟩, ⟨31033, 955, 5⟩, ⟨31088, 956, 6⟩, ⟨31144, 956, 4⟩,
  ⟨31203, 956, 9⟩, ⟨31260, 956, 8⟩, ⟨31315, 956, 4⟩, ⟨31373, 956, 6⟩,
  ⟨31429, 957, 6⟩, ⟨31485, 957, 3⟩, ⟨31546, 957, 7⟩, ⟨31607, 957, 6⟩,
  ⟨31670, 957, 8⟩, ⟨31728, 958, 5⟩, ⟨31789, 958, 5⟩, ⟨31852, 958, 5⟩,
  ⟨31918, 958, 5⟩, ⟨31987, 958, 4⟩, ⟨32061, 958, 8⟩, ⟨32132, 959, 8⟩,
  ⟨32204, 959, 8⟩, ⟨32277, 959, 6⟩, ⟨32353, 959, 9⟩, ⟨32425, 960, 10⟩,
  ⟨32495, 960, 6⟩, ⟨32568, 960, 8⟩, ⟨32642, 960, 9⟩, ⟨32716, 960, 6⟩,
  ⟨32789, 961, 7⟩, ⟨32864, 961, 7⟩, ⟨32941, 961, 8⟩, ⟨33020, 961, 8⟩,
  ⟨33100, 961, 9⟩, ⟨33177, 962, 6⟩, ⟨33258, 962, 8⟩, ⟨33340, 962, 7⟩,
  ⟨33426, 962, 10⟩, ⟨33508, 963, 8⟩, ⟨33592, 963, 10⟩, ⟨33676, 963, 10⟩,
  ⟨33760, 963, 8⟩, ⟨33846, 963, 9⟩, ⟨33930, 964, 8⟩, ⟨34016, 964, 6⟩,
  ⟨34107, 964, 6⟩, ⟨34203, 964, 9⟩, ⟨34298, 965, 11⟩, ⟨34393, 965, 11⟩,
  ⟨34489, 965, 9⟩, ⟨34587, 965, 9⟩, ⟨34685, 966, 11⟩, ⟨34783, 966, 11⟩,
  ⟨34882, 966, 8⟩, ⟨34981, 967, 9⟩, ⟨35083, 967, 8⟩, ⟨35190, 967, 11⟩,
  ⟨35299, 967, 9⟩, ⟨35409, 968, 12⟩, ⟨35520, 968, 9⟩, ⟨35636, 968, 13⟩,
  ⟨35749, 969, 5⟩, ⟨35871, 969, 13⟩, ⟨35995, 969, 12⟩, ⟨36122, 969, 13⟩,
  ⟨36247, 970, 10⟩, ⟨36378, 970, 13⟩, ⟨36512, 970, 11⟩, ⟨36647, 971, 15⟩,
  ⟨36784, 971, 15⟩, ⟨36918, 972, 14⟩, ⟨37054, 972, 15⟩, ⟨37191, 972, 11⟩,
  ⟨37330, 973, 12⟩, ⟨37474, 973, 13⟩, ⟨37623, 973, 20⟩, ⟨37765, 974, 10⟩,
  ⟨37915, 974, 14⟩, ⟨38069, 974, 13⟩, ⟨38225, 975, 12⟩, ⟨38388, 975, 17⟩,
  ⟨38549, 975, 9⟩, ⟨38722, 976, 20⟩, ⟨38895, 976, 17⟩, ⟨39068, 977, 15⟩,
  ⟨39247, 977, 22⟩, ⟨39420, 978, 16⟩, ⟨39598, 978, 14⟩, ⟨39784, 978, 17⟩,
  ⟨39972, 979, 19⟩, ⟨40163, 979, 19⟩, ⟨40354, 980, 14⟩, ⟨40554, 980, 18⟩,
  ⟨40756, 981, 15⟩, ⟨40968, 981, 23⟩, ⟨41178, 982, 19⟩, ⟨41394, 982, 23⟩,
  ⟨41608, 983, 19⟩, ⟨41829, 983, 22⟩, ⟨42050, 984, 25⟩, ⟨42272, 984, 21⟩,
  ⟨42495, 984, 28⟩, ⟨42716, 985, 20⟩, ⟨42944, 985, 24⟩, ⟨43170, 986, 19⟩,
  ⟨43405, 986, 18⟩, ⟨43646, 987, 21⟩, ⟨43895, 987, 21⟩, ⟨44148, 988, 27⟩,
  ⟨44399, 989, 23⟩, ⟨44658, 989, 25⟩, ⟨44918, 990, 24⟩, ⟨45185, 990, 23⟩,
  ⟨45457, 991, 24⟩, ⟨45738, 991, 24⟩, ⟨46024, 992, 24⟩, ⟨46321, 992, 28⟩,
  ⟨46620, 993, 27⟩, ⟨46923, 994, 31⟩, ⟨47232, 994, 23⟩, ⟨47550, 995, 32⟩,
  ⟨47872, 995, 32⟩, ⟨48197, 996, 29⟩, ⟨48527, 997, 29⟩, ⟨48868, 997, 33⟩,
  ⟨49211, 998, 36⟩, ⟨49554, 999, 32⟩, ⟨49906, 999, 31⟩, ⟨50264, 1000, 37⟩,
  ⟨50621, 1001, 32⟩, ⟨50989, 1001, 30⟩, ⟨51366, 1002, 34⟩, ⟨51749, 1003, 40⟩,
  ⟨52137, 1003, 35⟩, ⟨52531, 1004, 33⟩, ⟨52933, 1005, 37⟩, ⟨53346, 1005, 40⟩,
  ⟨53762, 1006, 37⟩, ⟨54185, 1007, 39⟩, ⟨54614, 1008, 41⟩, ⟨55052, 1008, 38⟩,
  ⟨55499, 1009, 37⟩, ⟨55956, 1010, 48⟩, ⟨56413, 1011, 38⟩, ⟨56886, 1011, 48⟩,
  ⟨57361, 1012, 50⟩, ⟨57835, 1013, 43⟩, ⟨58316, 1014, 45⟩, ⟨58809, 1014, 44⟩,
  ⟨59310, 1015, 47⟩, ⟨59816, 1016, 51⟩, ⟨60324, 1017, 40⟩, ⟨60846, 1018, 47⟩,
  ⟨61383, 1018, 45⟩, ⟨61932, 1019, 48⟩, ⟨62492, 1020, 50⟩, ⟨63061, 1021, 49⟩,
  ⟨63642, 1022, 56⟩, ⟨64229, 1023, 53⟩, ⟨64831, 1023, 47⟩, ⟨65452, 1024, 61⟩,
  ⟨66078, 1025, 59⟩, ⟨66712, 1026, 51⟩, ⟨67363, 1027, 61⟩, ⟨68022, 1028, 65⟩,
  ⟨68686, 1029, 53⟩, ⟨69369, 1030, 58⟩, ⟨70067, 1031, 59⟩, ⟨70781, 1032, 65⟩,
  ⟨71506, 1033, 75⟩, ⟨72240, 1033, 67⟩, ⟨72985, 1034, 67⟩, ⟨73742, 1035, 64⟩,
  ⟨74517, 1036, 68⟩, ⟨75306, 1037, 70⟩, ⟨76110, 1038, 75⟩, ⟨76924, 1039, 69⟩,
  ⟨77756, 1040, 81⟩, ⟨78595, 1041, 70⟩, ⟨79454, 1042, 74⟩, ⟨80331, 1043, 79⟩,
  ⟨81222, 1044, 84⟩, ⟨82124, 1045, 79⟩, ⟨83043, 1046, 81⟩, ⟨83979, 1047, 80⟩,
  ⟨84935, 1048, 83⟩, ⟨85910, 1049, 88⟩, ⟨86891, 1051, 83⟩, ⟨87894, 1052, 93⟩,
  ⟨88910, 1053, 81⟩, ⟨89954, 1054, 95⟩, ⟨91013, 1055, 97⟩, ⟨92087, 1056, 91⟩,
  ⟨93184, 1057, 106⟩, ⟨94290, 1058, 92⟩, ⟨95422, 1059, 106⟩, ⟨96567, 1060, 101⟩,
  ⟨97732, 1061, 96⟩, ⟨98915, 1063, 101⟩, ⟨100122, 1064, 104⟩, ⟨101353, 1065, 106⟩,
  ⟨102609, 1066, 119⟩, ⟨103879, 1067, 95⟩, ⟨105191, 1068, 116⟩, ⟨106526, 1069, 117⟩,
  ⟨107875, 1071, 112⟩, ⟨109256, 1072, 123⟩, ⟨110660, 1073, 120⟩, ⟨112094, 1074, 119⟩,
  ⟨113561, 1075, 130⟩, ⟨115054, 1076, 120⟩, ⟨116574, 1078, 136⟩, ⟨118119, 1079, 133⟩,
  ⟨119694, 1080, 129⟩, ⟨121308, 1081, 141⟩, ⟨122939, 1083, 146⟩, ⟨124596, 1084, 142⟩,
  ⟨126286, 1085, 145⟩, ⟨128009, 1086, 142⟩, ⟨129759, 1088, 156⟩, ⟨131537, 1089, 147⟩,
  ⟨133356, 1090, 159⟩, ⟨135207, 1091, 146⟩, ⟨137094, 1093, 172⟩, ⟨139006, 1094, 162⟩,
  ⟨140957, 1095, 168⟩, ⟨142936, 1096, 164⟩, ⟨144953, 1098, 160⟩, ⟨147023, 1099, 174⟩,
  ⟨149135, 1100, 180⟩, ⟨151274, 1102, 187⟩, ⟨153449, 1103, 189⟩, ⟨155661, 1104, 183⟩,
  ⟨157906, 1106, 186⟩, ⟨160199, 1107, 187⟩, ⟨162545, 1108, 190⟩, ⟨164930, 1110, 201⟩,
  ⟨167362, 1111, 200⟩, ⟨169847, 1112, 195⟩, ⟨172381, 1114, 216⟩, ⟨174961, 1115, 214⟩,
  ⟨177578, 1117, 215⟩, ⟨180251, 1118, 233⟩, ⟨182967, 1119, 220⟩, ⟨185727, 1121, 229⟩,
  ⟨188543, 1122, 235⟩, ⟨191414, 1123, 231⟩, ⟨194333, 1125, 250⟩, ⟨197302, 1126, 241⟩,
  ⟨200318, 1128, 246⟩, ⟨203398, 1129, 250⟩, ⟨206545, 1130, 257⟩, ⟨209739, 1132, 267⟩,
  ⟨212993, 1133, 262⟩, ⟨216299, 1135, 264⟩, ⟨219680, 1136, 275⟩, ⟨223112, 1138, 287⟩,
  ⟨226607, 1139, 281⟩, ⟨230178, 1140, 305⟩, ⟨233786, 1142, 281⟩, ⟨237482, 1143, 286⟩,
  ⟨241248, 1145, 302⟩, ⟨245095, 1146, 321⟩, ⟨248989, 1148, 324⟩, ⟨252953, 1149, 316⟩,
  ⟨256980, 1151, 319⟩, ⟨261097, 1152, 330⟩, ⟨265277, 1154, 332⟩, ⟨269548, 1155, 356⟩,
  ⟨273869, 1157, 336⟩, ⟨278291, 1158, 358⟩, ⟨282791, 1159, 364⟩, ⟨287364, 1161, 362⟩,
  ⟨292039, 1162, 364⟩, ⟨296799, 1164, 371⟩, ⟨301671, 1165, 379⟩, ⟨306631, 1167, 404⟩,
  ⟨311687, 1168, 389⟩, ⟨316838, 1170, 415⟩, ⟨322065, 1172, 432⟩, ⟨327384, 1173, 420⟩,
  ⟨332789, 1175, 430⟩, ⟨338307, 1176, 441⟩, ⟨343907, 1178, 432⟩, ⟨349638, 1179, 454⟩,
  ⟨355458, 1181, 465⟩, ⟨361394, 1182, 443⟩, ⟨367452, 1184, 486⟩, ⟨373628, 1185, 458⟩,
  ⟨379933, 1187, 499⟩, ⟨386366, 1188, 497⟩, ⟨392910, 1190, 514⟩, ⟨399591, 1191, 526⟩,
  ⟨406375, 1193, 501⟩, ⟨413300, 1195, 542⟩, ⟨420369, 1196, 550⟩, ⟨427552, 1198, 552⟩,
  ⟨434894, 1199, 584⟩, ⟨442339, 1201, 571⟩, ⟨449949, 1202, 578⟩, ⟨457695, 1204, 598⟩,
  ⟨465567, 1206, 589⟩, ⟨473627, 1207, 626⟩, ⟨481813, 1209, 639⟩, ⟨490162, 1210, 634⟩,
  ⟨498657, 1212, 653⟩, ⟨507331, 1213, 660⟩, ⟨516152, 1215, 659⟩, ⟨525136, 1217, 702⟩,
  ⟨534293, 1218, 702⟩, ⟨543598, 1220, 696⟩, ⟨553115, 1221, 714⟩, ⟨562800, 1223, 729⟩,
  ⟨572653, 1225, 747⟩, ⟨582716, 1226, 759⟩, ⟨592949, 1228, 778⟩, ⟨603396, 1229, 789⟩,
  ⟨614017, 1231, 808⟩, ⟨624807, 1233, 815⟩, ⟨635823, 1234, 808⟩, ⟨647046, 1236, 819⟩,
  ⟨658482, 1238, 856⟩, ⟨670163, 1239, 873⟩, ⟨682042, 1241, 902⟩, ⟨694159, 1242, 897⟩,
  ⟨706488, 1244, 923⟩, ⟨719020, 1246, 921⟩, ⟨731832, 1247, 968⟩, ⟨744842, 1249, 950⟩,
  ⟨758088, 1251, 961⟩, ⟨771640, 1252, 1035⟩, ⟨785385, 1254, 1012⟩, ⟨799428, 1255, 1034⟩,
  ⟨813711, 1257, 1049⟩, ⟨828240, 1259, 1088⟩, ⟨843058, 1260, 1072⟩, ⟨858146, 1262, 1100⟩,
  ⟨873497, 1264, 1132⟩, ⟨889168, 1265, 1157⟩, ⟨905094, 1267, 1143⟩, ⟨921313, 1269, 1191⟩,
  ⟨937869, 1270, 1206⟩, ⟨954707, 1272, 1211⟩, ⟨971920, 1273, 1250⟩, ⟨989428, 1275, 1239⟩,
  ⟨1007269, 1277, 1307⟩, ⟨1025475, 1278, 1340⟩, ⟨1043968, 1280, 1320⟩, ⟨1062795, 1282, 1325⟩,
  ⟨1082060, 1283, 1412⟩, ⟨1101629, 1285, 1407⟩, ⟨1121534, 1287, 1458⟩, ⟨1141832, 1288, 1447⟩,
  ⟨1162489, 1290, 1485⟩, ⟨1183495, 1292, 1540⟩, ⟨1204907, 1293, 1524⟩, ⟨1226693, 1295, 1549⟩,
  ⟨1248859, 1297, 1562⟩, ⟨1271516, 1298, 1638⟩, ⟨1294534, 1300, 1622⟩, ⟨1317962, 1302, 1656⟩,
  ⟨1341895, 1303, 1700⟩, ⟨1366236, 1305, 1705⟩, ⟨1391015, 1307, 1768⟩, ⟨1416302, 1308, 1783⟩,
  ⟨1442027, 1310, 1831⟩, ⟨1468175, 1312, 1847⟩, ⟨1494870, 1313, 1902⟩, ⟨1521998, 1315, 1910⟩,
  ⟨1549586, 1317, 1923⟩, ⟨1577771, 1318, 1974⟩, ⟨1606441, 1320, 1992⟩, ⟨1635619, 1322, 2058⟩,
  ⟨1665392, 1323, 2038⟩, ⟨1695721, 1325, 2132⟩, ⟨1726551, 1327, 2142⟩, ⟨1758036, 1328, 2203⟩,
  ⟨1790047, 1330, 2192⟩, ⟨1822641, 1332, 2275⟩, ⟨1855906, 1333, 2334⟩, ⟨1889710, 1335, 2364⟩,
  ⟨1924065, 1337, 2372⟩, ⟨1959144, 1338, 2431⟩, ⟨1994814, 1340, 2439⟩, ⟨2031116, 1342, 2534⟩,
  ⟨2068141, 1343, 2545⟩, ⟨2097151, 1344, 1977⟩
]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma dyadic_rank_thresholds_valid : RankThresholds dyadicRankThresholds 0 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma candidate_count_30001 : (candidatePrefix 30001).card ≤ 3265 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma dyadic_rank_intervals_valid :
    RankIntervals dyadicRankThresholds 30001 (2^21-1) 3265 dyadicRankIntervals := by decide +kernel

theorem bridge_rank_product (k : ℕ) (hk₁ : 30001 ≤ k) (hk₂ : k < 2^21) :
    (k-1).factorial < ∏ i ∈ range (retainedCount k), rankBound (i+1) :=
  rank_intervals_bound _ 30001 (2^21-1) 3265 k _ dyadic_rank_thresholds_valid
    (by decide) hk₁ (by omega) candidate_count_30001 dyadic_rank_intervals_valid

end Erdos137OddBridge
