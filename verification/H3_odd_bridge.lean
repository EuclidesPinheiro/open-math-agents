import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.PrimeCounting
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

def candidateCount (a b : ℕ) : ℕ := ((range (b-a)).filter fun t => fermatCandidate (a+t)).card

lemma candidate_count_eq (a b : ℕ) : candidateCount a b = ((Ico a b).filter fermatCandidate).card := by
  have hImage : (((range (b-a)).filter fun t => fermatCandidate (a+t)).image (a+·)) =
      (Ico a b).filter fermatCandidate := by
    ext n
    simp only [mem_image,mem_filter,mem_range,mem_Ico]
    constructor
    · rintro ⟨t, ⟨ht,hC⟩,rfl⟩
      exact ⟨⟨by omega,by omega⟩,hC⟩
    · rintro ⟨⟨hA,hB⟩,hC⟩
      exact ⟨n-a,⟨by omega,by simpa only [Nat.add_sub_of_le hA] using hC⟩,Nat.add_sub_of_le hA⟩
  rw [← hImage, card_image_of_injective _ (fun t u he => by omega), candidateCount]

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
  rw [hEq, Finset.card_union_of_disjoint hDis, candidate_count_eq]

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

def countFromIntervals (n start available : ℕ) : List RankInterval → ℕ
  | [] => available
  | row :: rows =>
      if n ≤ start then available else
        countFromIntervals n (row.upper+1) (available+row.increment) rows

lemma count_from_intervals_valid (ts : List ℕ) (start stop available n : ℕ) (rows : List RankInterval)
    (hn : n ≤ stop+1) (hP : (candidatePrefix start).card ≤ available)
    (hRows : RankIntervals ts start stop available rows) :
    (candidatePrefix n).card ≤ countFromIntervals n start available rows := by
  have hMono : Monotone (fun t => (candidatePrefix t).card) := fun a b hab =>
    card_le_card (filter_subset_filter _ (range_mono hab))
  induction rows generalizing start available with
  | nil =>
    have hEnd : stop < start := hRows
    exact (hMono (by omega : n ≤ start)).trans hP
  | cons row rs ih =>
    obtain ⟨hUpper,_,_,hInc,hNext⟩ := hRows
    by_cases h : n ≤ start
    · exact (hMono h).trans (by simpa only [countFromIntervals, if_pos h] using hP)
    · rw [countFromIntervals, if_neg h]
      apply ih (row.upper+1) (available+row.increment) _ hNext
      rw [candidate_prefix_add (by omega : start ≤ row.upper+1)]
      exact Nat.add_le_add hP hInc

lemma primes_le_candidates (n : ℕ) : n.primesLE.card ≤ (candidatePrefix (n+1)).card := by
  apply card_le_card
  intro p hp
  obtain ⟨hU,hPrime⟩ := Nat.mem_primesLE.mp hp
  exact mem_filter.mpr ⟨mem_range.mpr (by omega), prime_is_fermat_candidate hPrime⟩

lemma wheel_prime_count_upper (n : ℕ) : n.primesLE.card ≤ 211+48*((n+1)/210+1) := by
  have hBase : (211:ℕ).primeCounting' ≤ 211 := by
    rw [← Nat.primesBelow_card_eq_primeCounting',Nat.primesBelow_eq_filter_range]
    exact (card_filter_le (s := range 211) Nat.Prime).trans_eq (card_range _)
  by_cases h : 211 ≤ n+1
  · have hAdd := Nat.primeCounting'_add_le (a := 210) (k := 211) (by decide) (by decide) (n+1-211)
    have hTotient : Nat.totient 210 = 48 := by decide
    rw [show 211+(n+1-211) = n+1 by omega,hTotient] at hAdd
    rw [Nat.primesLE,Nat.primesBelow_card_eq_primeCounting']
    have hQ := Nat.div_le_div_right (show n+1-211 ≤ n+1 by omega)
    omega
  · have hMono := Nat.monotone_primeCounting' (show n+1 ≤ 211 by omega)
    rw [Nat.primesLE,Nat.primesBelow_card_eq_primeCounting']
    omega

def NumericRankIntervals (ts : List ℕ) (estimate : ℕ → ℕ) (start stop : ℕ) : List (ℕ × ℕ) → Prop
  | [] => stop < start
  | row :: rest =>
      start ≤ row.1 ∧ (row.1-1)^64 ≤ 2^row.2 ∧
      (row.1-1-(start-estimate start))*row.2 < gainedExponent ts (start-estimate start) ∧
      NumericRankIntervals ts estimate (row.1+1) stop rest

instance (ts : List ℕ) (estimate : ℕ → ℕ) (start stop : ℕ) (rows : List (ℕ × ℕ)) :
    Decidable (NumericRankIntervals ts estimate start stop rows) := by
  induction rows generalizing start with
  | nil => unfold NumericRankIntervals; infer_instance
  | cons row rest ih =>
    unfold NumericRankIntervals
    letI := ih (row.1+1)
    infer_instance

lemma numeric_rank_intervals_bound (ts : List ℕ) (estimate : ℕ → ℕ) (start stop k : ℕ)
    (rows : List (ℕ × ℕ)) (hT : RankThresholds ts 0) (hStart : 3 ≤ start) (hk : start ≤ k) (hStop : k ≤ stop)
    (hEstimate : ∀ n, 3 ≤ n → ((range n).filter Nat.Prime).card ≤ estimate n)
    (hRows : NumericRankIntervals ts estimate start stop rows) :
    (k-1).factorial < ∏ i ∈ range (retainedCount k), rankBound (i+1) := by
  induction rows generalizing start with
  | nil => exact (not_lt_of_ge (hk.trans hStop) hRows).elim
  | cons row rows ih =>
    obtain ⟨hUpper,hBudget,hGain,hNext⟩ := hRows
    by_cases h : k ≤ row.1
    · exact rank_product_on_interval ts start row.1 (estimate start) row.2 k hT hStart hk h
        (hEstimate _ hStart) hBudget hGain
    · exact ih (row.1+1) (by omega) (by omega) hNext

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
  ⟨292039, 1162, 364⟩, ⟨296799, 1164, 371⟩, ⟨300000, 1165, 240⟩
]

set_option maxRecDepth 10000 in
private def analyticRankIntervals : List (ℕ × ℕ) := [
  (300060, 1165), (300121, 1165), (300182, 1165), (300243, 1165), (300306, 1165), (300370, 1165),
  (300434, 1165), (300499, 1165), (300564, 1165), (300630, 1165), (300697, 1165), (300765, 1165),
  (300833, 1165), (300902, 1165), (300971, 1165), (301041, 1165), (301112, 1165), (301183, 1165),
  (301254, 1165), (301321, 1165), (301389, 1165), (301458, 1165), (301528, 1165), (301598, 1165),
  (301670, 1165), (301742, 1165), (301788, 1166), (301865, 1166), (301943, 1166), (302023, 1166),
  (302103, 1166), (302184, 1166), (302265, 1166), (302347, 1166), (302430, 1166), (302510, 1166),
  (302592, 1166), (302662, 1166), (302732, 1166), (302804, 1166), (302876, 1166), (302949, 1166),
  (303022, 1166), (303096, 1166), (303171, 1166), (303247, 1166), (303324, 1166), (303402, 1166),
  (303480, 1166), (303558, 1166), (303637, 1166), (303716, 1166), (303797, 1166), (303878, 1166),
  (303961, 1166), (304044, 1166), (304128, 1166), (304213, 1166), (304299, 1166), (304386, 1166),
  (304474, 1166), (304558, 1166), (304642, 1166), (304727, 1166), (304813, 1166), (304900, 1166),
  (304987, 1166), (305064, 1166), (305158, 1167), (305253, 1167), (305349, 1167), (305446, 1167),
  (305544, 1167), (305643, 1167), (305743, 1167), (305844, 1167), (305945, 1167), (306047, 1167),
  (306150, 1167), (306255, 1167), (306361, 1167), (306468, 1167), (306576, 1167), (306684, 1167),
  (306794, 1167), (306905, 1167), (307006, 1167), (307107, 1167), (307210, 1167), (307312, 1167),
  (307416, 1167), (307521, 1167), (307627, 1167), (307734, 1167), (307837, 1167), (307942, 1167),
  (308048, 1167), (308155, 1167), (308262, 1167), (308370, 1167), (308453, 1168), (308568, 1168),
  (308684, 1168), (308801, 1168), (308919, 1168), (309038, 1168), (309158, 1168), (309274, 1168),
  (309391, 1168), (309509, 1168), (309627, 1168), (309747, 1168), (309868, 1168), (309990, 1168),
  (310113, 1168), (310236, 1168), (310361, 1168), (310487, 1168), (310615, 1168), (310744, 1168),
  (310875, 1168), (311007, 1168), (311140, 1168), (311271, 1168), (311401, 1168), (311520, 1168),
  (311641, 1168), (311744, 1168), (311873, 1169), (312002, 1169), (312133, 1169), (312265, 1169),
  (312398, 1169), (312533, 1169), (312669, 1169), (312805, 1169), (312942, 1169), (313081, 1169),
  (313221, 1169), (313363, 1169), (313507, 1169), (313652, 1169), (313799, 1169), (313947, 1169),
  (314097, 1169), (314248, 1169), (314399, 1169), (314548, 1169), (314698, 1169), (314850, 1169),
  (315003, 1169), (315139, 1169), (315300, 1170), (315463, 1170), (315627, 1170), (315792, 1170),
  (315959, 1170), (316113, 1170), (316268, 1170), (316424, 1170), (316583, 1170), (316743, 1170),
  (316905, 1170), (317067, 1170), (317231, 1170), (317397, 1170), (317564, 1170), (317733, 1170),
  (317904, 1170), (318072, 1170), (318241, 1170), (318412, 1170), (318570, 1170), (318748, 1171),
  (318927, 1171), (319109, 1171), (319293, 1171), (319478, 1171), (319666, 1171), (319855, 1171),
  (320045, 1171), (320237, 1171), (320431, 1171), (320615, 1171), (320801, 1171), (320988, 1171),
  (321178, 1171), (321370, 1171), (321557, 1171), (321747, 1171), (321939, 1171), (322105, 1172),
  (322302, 1172), (322501, 1172), (322693, 1172), (322883, 1172), (323074, 1172), (323267, 1172),
  (323462, 1172), (323659, 1172), (323858, 1172), (324060, 1172), (324264, 1172), (324470, 1172),
  (324676, 1172), (324885, 1172), (325096, 1172), (325291, 1172), (325488, 1172), (325660, 1173),
  (325866, 1173), (326075, 1173), (326284, 1173), (326495, 1173), (326708, 1173), (326923, 1173),
  (327141, 1173), (327361, 1173), (327583, 1173), (327807, 1173), (328033, 1173), (328261, 1173),
  (328492, 1173), (328725, 1173), (328955, 1173), (329160, 1174), (329399, 1174), (329638, 1174),
  (329878, 1174), (330107, 1174), (330339, 1174), (330573, 1174), (330810, 1174), (331049, 1174),
  (331291, 1174), (331534, 1174), (331780, 1174), (332028, 1174), (332279, 1174), (332528, 1174),
  (332750, 1175), (333008, 1175), (333267, 1175), (333529, 1175), (333794, 1175), (334061, 1175),
  (334331, 1175), (334604, 1175), (334881, 1175), (335146, 1175), (335414, 1175), (335685, 1175),
  (335959, 1175), (336226, 1175), (336465, 1176), (336738, 1176), (337015, 1176), (337294, 1176),
  (337576, 1176), (337861, 1176), (338149, 1176), (338440, 1176), (338732, 1176), (339028, 1176),
  (339327, 1176), (339629, 1176), (339934, 1176), (340194, 1177), (340489, 1177), (340787, 1177),
  (341088, 1177), (341392, 1177), (341700, 1177), (342011, 1177), (342323, 1177), (342638, 1177),
  (342957, 1177), (343276, 1177), (343598, 1177), (343893, 1178), (344221, 1178), (344552, 1178),
  (344886, 1178), (345210, 1178), (345537, 1178), (345867, 1178), (346200, 1178), (346537, 1178),
  (346877, 1178), (347221, 1178), (347538, 1179), (347892, 1179), (348243, 1179), (348599, 1179),
  (348958, 1179), (349321, 1179), (349683, 1179), (350043, 1179), (350393, 1179), (350747, 1179),
  (351104, 1179), (351435, 1180), (351803, 1180), (352170, 1180), (352541, 1180), (352915, 1180),
  (353293, 1180), (353674, 1180), (354059, 1180), (354448, 1180), (354841, 1180), (355207, 1181),
  (355596, 1181), (355990, 1181), (356382, 1181), (356774, 1181), (357171, 1181), (357572, 1181),
  (357975, 1181), (358383, 1181), (358795, 1181), (359180, 1182), (359605, 1182), (360034, 1182),
  (360461, 1182), (360892, 1182), (361314, 1182), (361740, 1182), (362169, 1182), (362602, 1182),
  (363009, 1183), (363450, 1183), (363896, 1183), (364345, 1183), (364793, 1183), (365245, 1183),
  (365702, 1183), (366164, 1183), (366614, 1183), (367039, 1184), (367504, 1184), (367973, 1184),
  (368448, 1184), (368919, 1184), (369395, 1184), (369876, 1184), (370360, 1184), (370817, 1185),
  (371314, 1185), (371815, 1185), (372307, 1185), (372804, 1185), (373300, 1185), (373799, 1185),
  (374304, 1185), (374782, 1186), (375302, 1186), (375828, 1186), (376358, 1186), (376882, 1186),
  (377411, 1186), (377924, 1186), (378440, 1186), (378929, 1187), (379461, 1187), (379998, 1187),
  (380542, 1187), (381089, 1187), (381642, 1187), (382200, 1187), (382758, 1187), (383289, 1188),
  (383843, 1188), (384403, 1188), (384969, 1188), (385541, 1188), (386119, 1188), (386700, 1188),
  (387249, 1189), (387841, 1189), (388440, 1189), (389043, 1189), (389637, 1189), (390238, 1189),
  (390839, 1189), (391413, 1190), (392023, 1190), (392639, 1190), (393261, 1190), (393890, 1190),
  (394524, 1190), (395164, 1190), (395762, 1191), (396399, 1191), (397042, 1191), (397687, 1191),
  (398338, 1191), (398996, 1191), (399662, 1191), (400299, 1192), (400981, 1192), (401648, 1192),
  (402321, 1192), (403000, 1192), (403686, 1192), (404336, 1193), (405033, 1193), (405735, 1193),
  (406436, 1193), (407145, 1193), (407846, 1193), (408554, 1193), (409233, 1194), (409958, 1194),
  (410689, 1194), (411421, 1194), (412158, 1194), (412903, 1194), (413621, 1195), (414369, 1195),
  (415124, 1195), (415886, 1195), (416649, 1195), (417414, 1195), (418150, 1196), (418934, 1196),
  (419727, 1196), (420511, 1196), (421301, 1196), (422093, 1196), (422857, 1197), (423670, 1197),
  (424488, 1197), (425314, 1197), (426149, 1197), (426933, 1198), (427765, 1198), (428605, 1198),
  (429450, 1198), (430302, 1198), (431148, 1198), (431967, 1199), (432829, 1199), (433683, 1199),
  (434543, 1199), (435411, 1199), (436253, 1200), (437145, 1200), (438037, 1200), (438939, 1200),
  (439850, 1200), (440753, 1200), (441626, 1201), (442551, 1201), (443485, 1201), (444419, 1201),
  (445360, 1201), (446274, 1202), (447223, 1202), (448181, 1202), (449147, 1202), (450116, 1202),
  (451057, 1203), (452051, 1203), (453052, 1203), (454065, 1203), (455069, 1203), (456038, 1204),
  (457058, 1204), (458082, 1204), (459117, 1204), (460160, 1204), (461177, 1205), (462222, 1205),
  (463278, 1205), (464343, 1205), (465405, 1205), (466497, 1206), (467592, 1206), (468679, 1206),
  (469777, 1206), (470848, 1207), (471969, 1207), (473102, 1207), (474239, 1207), (475388, 1207),
  (476488, 1208), (477645, 1208), (478814, 1208), (479984, 1208), (481127, 1209), (482327, 1209),
  (483539, 1209), (484740, 1209), (485945, 1209), (487113, 1210), (488336, 1210), (489571, 1210),
  (490819, 1210), (492020, 1211), (493268, 1211), (494528, 1211), (495801, 1211), (497043, 1212),
  (498344, 1212), (499636, 1212), (500932, 1212), (502198, 1213), (503523, 1213), (504861, 1213),
  (506209, 1213), (507527, 1213), (508881, 1214), (510248, 1214), (511626, 1214), (513013, 1214),
  (514362, 1215), (515749, 1215), (517150, 1215), (518566, 1215), (519955, 1216), (521392, 1216),
  (522844, 1216), (524289, 1216), (525734, 1217), (527195, 1217), (528660, 1217), (530093, 1218),
  (531591, 1218), (533083, 1218), (534590, 1218), (536056, 1219), (537587, 1219), (539121, 1219),
  (540646, 1219), (542143, 1220), (543694, 1220), (545261, 1220), (546842, 1220), (548395, 1221),
  (549982, 1221), (551582, 1221), (553195, 1221), (554780, 1222), (556433, 1222), (558088, 1222),
  (559693, 1223), (561366, 1223), (563051, 1223), (564754, 1223), (566413, 1224), (568114, 1224),
  (569833, 1224), (571570, 1224), (573279, 1225), (575043, 1225), (576803, 1225), (578535, 1226),
  (580330, 1226), (582133, 1226), (583955, 1226), (585745, 1227), (587584, 1227), (589441, 1227),
  (591259, 1228), (593139, 1228), (595036, 1228), (596938, 1228), (598796, 1229), (600728, 1229),
  (601191, 1229), (601658, 1229), (602128, 1229), (602602, 1229), (603075, 1229), (603552, 1229),
  (603985, 1230), (604476, 1230), (604971, 1230), (605467, 1230), (605955, 1230), (606447, 1230),
  (606943, 1230), (607443, 1230), (607946, 1230), (608452, 1230), (608963, 1230), (609473, 1230),
  (609987, 1230), (610457, 1231), (610987, 1231), (611521, 1231), (612059, 1231), (612601, 1231),
  (613147, 1231), (613697, 1231), (614252, 1231), (614799, 1231), (615350, 1231), (615906, 1231),
  (616461, 1231), (616972, 1232), (617543, 1232), (618118, 1232), (618695, 1232), (619274, 1232),
  (619858, 1232), (620445, 1232), (621036, 1232), (621632, 1232), (622233, 1232), (622835, 1232),
  (623429, 1232), (623978, 1233), (624589, 1233), (625205, 1233), (625824, 1233), (626448, 1233),
  (627077, 1233), (627711, 1233), (628350, 1233), (628993, 1233), (629637, 1233), (630277, 1233),
  (630939, 1234), (631605, 1234), (632277, 1234), (632940, 1234), (633608, 1234), (634280, 1234),
  (634958, 1234), (635641, 1234), (636325, 1234), (637014, 1234), (637657, 1235), (638363, 1235),
  (639076, 1235), (639794, 1235), (640517, 1235), (641245, 1235), (641968, 1235), (642696, 1235),
  (643424, 1235), (644108, 1236), (644853, 1236), (645601, 1236), (646346, 1236), (647096, 1236),
  (647851, 1236), (648612, 1236), (649380, 1236), (650153, 1236), (650927, 1236), (651644, 1237),
  (652426, 1237), (653213, 1237), (654006, 1237), (654805, 1237), (655611, 1237), (656422, 1237),
  (657240, 1237), (658060, 1237), (658834, 1238), (659671, 1238), (660513, 1238), (661350, 1238),
  (662193, 1238), (663044, 1238), (663900, 1238), (664763, 1238), (665576, 1239), (666455, 1239),
  (667340, 1239), (668233, 1239), (669132, 1239), (670039, 1239), (670940, 1239), (671848, 1239),
  (672706, 1240), (673625, 1240), (674551, 1240), (675483, 1240), (676424, 1240), (677371, 1240),
  (678324, 1240), (679286, 1240), (680201, 1241), (681166, 1241), (682138, 1241), (683119, 1241),
  (684108, 1241), (685102, 1241), (686105, 1241), (687112, 1241), (688074, 1242), (689100, 1242),
  (690134, 1242), (691163, 1242), (692200, 1242), (693245, 1242), (694298, 1242), (695305, 1243),
  (696376, 1243), (697456, 1243), (698544, 1243), (699640, 1243), (700736, 1243), (701827, 1243),
  (702873, 1244), (703988, 1244), (705108, 1244), (706236, 1244), (707374, 1244), (708519, 1244),
  (709674, 1244), (710782, 1245), (711947, 1245), (713115, 1245), (714290, 1245), (715475, 1245),
  (716668, 1245), (717815, 1246), (719035, 1246), (720263, 1246), (721496, 1246), (722725, 1246),
  (723964, 1246), (725212, 1246), (726413, 1247), (727683, 1247), (728961, 1247), (730245, 1247),
  (731539, 1247), (732843, 1247), (734085, 1248), (735403, 1248), (736732, 1248), (738064, 1248),
  (739406, 1248), (740755, 1248), (742058, 1249), (743436, 1249), (744811, 1249), (746197, 1249),
  (747587, 1249), (748988, 1249), (750342, 1250), (751774, 1250), (753215, 1250), (754657, 1250),
  (756091, 1250), (757534, 1250), (758931, 1251), (760405, 1251), (761892, 1251), (763389, 1251),
  (764891, 1251), (766346, 1252), (767861, 1252), (769389, 1252), (770928, 1252), (772480, 1252),
  (774044, 1252), (775555, 1253), (777145, 1253), (778747, 1253), (780347, 1253), (781954, 1253),
  (783506, 1254), (785139, 1254), (786785, 1254), (788445, 1254), (790116, 1254), (791726, 1255),
  (793411, 1255), (795106, 1255), (796815, 1255), (798537, 1255), (800209, 1256), (801966, 1256),
  (803715, 1256), (805478, 1256), (807254, 1256), (808974, 1257), (810778, 1257), (812595, 1257),
  (814420, 1257), (816244, 1257), (818018, 1258), (819878, 1258), (821750, 1258), (823631, 1258),
  (825526, 1258), (827373, 1259), (829291, 1259), (831223, 1259), (833164, 1259), (835117, 1259),
  (837017, 1260), (839006, 1260), (840995, 1260), (842998, 1260), (844946, 1261), (846983, 1261),
  (849032, 1261), (851098, 1261), (853181, 1261), (855193, 1262), (857293, 1262), (859408, 1262),
  (861534, 1262), (863601, 1263), (865752, 1263), (867904, 1263), (870071, 1263), (872246, 1263),
  (874458, 1264), (876678, 1264), (878916, 1264), (881155, 1264), (883344, 1265), (885626, 1265),
  (887920, 1265), (890230, 1265), (892489, 1266), (894826, 1266), (897182, 1266), (899547, 1266),
  (901864, 1267), (904277, 1267), (906706, 1267), (909137, 1267), (911513, 1268), (913982, 1268),
  (916466, 1268), (918970, 1268), (921422, 1269), (923949, 1269), (926496, 1269), (929062, 1269),
  (931579, 1270), (934195, 1270), (936823, 1270), (939456, 1270), (942039, 1271), (944717, 1271),
  (947417, 1271), (950132, 1271), (952777, 1272), (955524, 1272), (958293, 1272), (961074, 1272),
  (963806, 1273), (966641, 1273), (969477, 1273), (972254, 1274), (975128, 1274), (978022, 1274),
  (980940, 1274), (983788, 1275), (986731, 1275), (989698, 1275), (992688, 1275), (995625, 1276),
  (998666, 1276), (1001705, 1276), (1004691, 1277), (1007785, 1277), (1010904, 1277), (1014036, 1277),
  (1017099, 1278), (1020272, 1278), (1023467, 1278), (1026606, 1279), (1029848, 1279), (1033094, 1279),
  (1036365, 1279), (1039586, 1280), (1042908, 1280), (1046255, 1280), (1049532, 1281), (1052902, 1281),
  (1056290, 1281), (1059705, 1281), (1063065, 1282), (1066521, 1282), (1070005, 1282), (1073425, 1283),
  (1076961, 1283), (1080515, 1283), (1083995, 1284), (1087582, 1284), (1091198, 1284), (1094840, 1284),
  (1098431, 1285), (1102111, 1285), (1105815, 1285), (1109467, 1286), (1113241, 1286), (1117010, 1286),
  (1120728, 1287), (1124568, 1287), (1128435, 1287), (1132242, 1288), (1136146, 1288), (1140077, 1288),
  (1143956, 1289), (1147951, 1289), (1151974, 1289), (1155932, 1289), (1160003, 1290), (1164095, 1290),
  (1168221, 1290), (1172270, 1291), (1176448, 1291), (1180650, 1291), (1184795, 1292), (1189061, 1292),
  (1193348, 1292), (1197568, 1293), (1201920, 1293), (1204903, 1293), (1207818, 1294), (1210848, 1294),
  (1213885, 1294), (1216943, 1294), (1220022, 1294), (1223029, 1295), (1226158, 1295), (1229307, 1295),
  (1232467, 1295), (1235555, 1296), (1238765, 1296), (1241992, 1296), (1245240, 1296), (1248416, 1297),
  (1251705, 1297), (1255016, 1297), (1258351, 1297), (1261613, 1298), (1265000, 1298), (1268397, 1298),
  (1271817, 1298), (1275164, 1299), (1278637, 1299), (1282134, 1299), (1285645, 1299), (1289081, 1300),
  (1292643, 1300), (1296218, 1300), (1299818, 1300), (1303345, 1301), (1306991, 1301), (1310661, 1301),
  (1314357, 1301), (1317979, 1302), (1321728, 1302), (1325493, 1302), (1329283, 1302), (1332999, 1303),
  (1336847, 1303), (1340723, 1303), (1344614, 1303), (1348425, 1304), (1352370, 1304), (1356344, 1304),
  (1360247, 1305), (1364268, 1305), (1368317, 1305), (1372393, 1305), (1376396, 1306), (1380533, 1306),
  (1384687, 1306), (1388869, 1306), (1392981, 1307), (1397228, 1307), (1401503, 1307), (1405688, 1308),
  (1410014, 1308), (1414365, 1308), (1418745, 1308), (1423055, 1309), (1427489, 1309), (1431952, 1309),
  (1436343, 1310), (1440879, 1310), (1445441, 1310), (1450023, 1310), (1454532, 1311), (1459184, 1311),
  (1463862, 1311), (1468455, 1312), (1473197, 1312), (1477971, 1312), (1482773, 1312), (1487499, 1313),
  (1492364, 1313), (1497256, 1313), (1502076, 1314), (1507048, 1314), (1512045, 1314), (1516948, 1315),
  (1522006, 1315), (1527098, 1315), (1532113, 1316), (1537266, 1316), (1542456, 1316), (1547681, 1316),
  (1552829, 1317), (1558135, 1317), (1563463, 1317), (1568714, 1318), (1574118, 1318), (1579559, 1318),
  (1584913, 1319), (1590422, 1319), (1595967, 1319), (1601438, 1320), (1607072, 1320), (1612726, 1320),
  (1618297, 1321), (1624034, 1321), (1629804, 1321), (1635486, 1322), (1641334, 1322), (1647221, 1322),
  (1653027, 1323), (1658988, 1323), (1664990, 1323), (1670912, 1324), (1676998, 1324), (1683128, 1324),
  (1689161, 1325), (1695368, 1325), (1701615, 1325), (1707788, 1326), (1714114, 1326), (1720482, 1326),
  (1726761, 1327), (1733211, 1327), (1739692, 1327), (1746096, 1328), (1752681, 1328), (1759304, 1328),
  (1765836, 1329), (1772549, 1329), (1779303, 1329), (1785977, 1330), (1792820, 1330), (1799710, 1330),
  (1806518, 1331), (1813510, 1331), (1820536, 1331), (1827476, 1332), (1834603, 1332), (1841652, 1333),
  (1848866, 1333), (1856132, 1333), (1863320, 1334), (1870702, 1334), (1878110, 1334), (1885443, 1335),
  (1892967, 1335), (1900537, 1335), (1908012, 1336), (1915685, 1336), (1923272, 1337), (1931059, 1337),
  (1938880, 1337), (1946616, 1338), (1954547, 1338), (1962531, 1338), (1970420, 1339), (1978504, 1339),
  (1986607, 1339), (1994817, 1340), (2003057, 1340), (2011217, 1341), (2019586, 1341), (2028012, 1341),
  (2036334, 1342), (2044868, 1342), (2053316, 1343), (2061969, 1343), (2070663, 1343), (2079278, 1344),
  (2088099, 1344), (2096983, 1344), (2097151, 1344)
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
    RankIntervals dyadicRankThresholds 30001 300000 3265 dyadicRankIntervals := by decide +kernel

def countingBound (n : ℕ) : ℕ :=
  if n ≤ 300000 then
    min (countFromIntervals (n+1) 30001 3265 dyadicRankIntervals) (211+48*((n+1)/210+1))
  else 23350+(13*n)/144

lemma counting_bound_small {n : ℕ} (hn : n ≤ 300000) : n.primesLE.card ≤ countingBound n := by
  rw [countingBound, if_pos hn]
  exact le_min ((primes_le_candidates n).trans
    (count_from_intervals_valid _ 30001 300000 3265 (n+1) _ (by omega)
      candidate_count_30001 dyadic_rank_intervals_valid)) (wheel_prime_count_upper n)

set_option maxRecDepth 100000 in
lemma prime_count_at_65536 : (Nat.primesLE (2^16)).card ≤ 6700 :=
  (counting_bound_small (by decide)).trans (by decide +kernel)

set_option maxRecDepth 100000 in
lemma prime_count_at_262144 : (Nat.primesLE (2^18)).card ≤ 23350 :=
  (counting_bound_small (by decide)).trans (by decide +kernel)

lemma counting_bound_valid (hLinear : ∀ n, 144*n.primesLE.card ≤ 13*n+144*23350)
    (n : ℕ) : n.primesLE.card ≤ countingBound n := by
  by_cases h : n ≤ 300000
  · exact counting_bound_small h
  · rw [countingBound, if_neg h]
    have hL := hLinear n
    omega

def analyticCountingBound (n : ℕ) : ℕ :=
  (104*(n-1) + 64*(∑ j ∈ range n.log2, countingBound (n/2^(j+1)))) / ((n^64).log2-64)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma analytic_rank_intervals_valid :
    NumericRankIntervals dyadicRankThresholds analyticCountingBound 300001 (2^21-1) analyticRankIntervals := by
  decide +kernel

theorem bridge_rank_product (k : ℕ) (hk₁ : 30001 ≤ k) (hk₂ : k ≤ 300000) :
    (k-1).factorial < ∏ i ∈ range (retainedCount k), rankBound (i+1) :=
  rank_intervals_bound _ 30001 300000 3265 k _ dyadic_rank_thresholds_valid
    (by decide) hk₁ hk₂ candidate_count_30001 dyadic_rank_intervals_valid

theorem analytic_rank_product (k : ℕ) (hk₁ : 300001 ≤ k) (hk₂ : k < 2^21)
    (hEstimate : ∀ n, 3 ≤ n → ((range n).filter Nat.Prime).card ≤ analyticCountingBound n) :
    (k-1).factorial < ∏ i ∈ range (retainedCount k), rankBound (i+1) :=
  numeric_rank_intervals_bound _ _ 300001 (2^21-1) k _ dyadic_rank_thresholds_valid
    (by decide) hk₁ (by omega) hEstimate analytic_rank_intervals_valid

end Erdos137OddBridge
