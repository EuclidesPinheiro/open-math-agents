import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

/-! Integer certificates for the range between the residue count and the uniform tail.

The rank thresholds record powers of two gained over the factorial bound.
A Fermat test gives the initial prime count bound. The first intervals use
divisor witnesses on a wheel modulo 210, with 10 bits per candidate. The
subsequent intervals use the dyadic estimate from the primorial.
-/

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

private def wheelResidues : List ℕ :=
  [1, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101,
    103, 107, 109, 113, 121, 127, 131, 137, 139, 143, 149, 151, 157, 163, 167, 169, 173, 179, 181, 187, 191, 193, 197, 199, 209]

private lemma wheel_residues_exact :
    wheelResidues = (List.range 210).filter (fun r => decide (r.Coprime 210)) := by decide

private def possiblePrimesInBlock (lo hi q code : ℕ) : List ℕ → List ℕ
  | [] => []
  | r :: residues =>
      let n := 210*q+r
      let factor := code%1024
      let rest := possiblePrimesInBlock lo hi q (code/1024) residues
      if lo ≤ n ∧ n < hi ∧ ¬ (1 < factor ∧ factor < n ∧ factor ∣ n) then n :: rest else rest

private lemma prime_in_wheel_block {lo hi q r : ℕ} (residues : List ℕ) (code : ℕ)
    (hr : r ∈ residues) (hlo : lo ≤ 210*q+r) (hhi : 210*q+r < hi)
    (hp : (210*q+r).Prime) : 210*q+r ∈ possiblePrimesInBlock lo hi q code residues := by
  induction residues generalizing code with
  | nil => simp at hr
  | cons t rs ih =>
    rcases List.mem_cons.mp hr with ht | hr
    · subst t
      have hNo : ¬ (1 < code%1024 ∧ code%1024 < 210*q+r ∧ code%1024 ∣ 210*q+r) := by
        rintro ⟨h₁,h₂,hD⟩
        rcases (Nat.dvd_prime hp).mp hD with h | h <;> omega
      simp [possiblePrimesInBlock,hlo,hhi,hNo]
    · have hTail := ih (code/1024) hr
      unfold possiblePrimesInBlock
      split
      · exact List.mem_cons_of_mem _ hTail
      · exact hTail

private def possiblePrimesInBlocks (lo hi q : ℕ) : List ℕ → List ℕ
  | [] => []
  | code :: codes =>
    possiblePrimesInBlock lo hi q code wheelResidues ++ possiblePrimesInBlocks lo hi (q+1) codes

private lemma prime_in_wheel_blocks {lo hi n : ℕ} (q : ℕ) (codes : List ℕ)
    (hlo : lo ≤ n) (hhi : n < hi) (hp : n.Prime) (hR : n%210 ∈ wheelResidues)
    (hq : q ≤ n/210) (hqU : n/210 < q+codes.length) :
    n ∈ possiblePrimesInBlocks lo hi q codes := by
  induction codes generalizing q with
  | nil => simp at hqU; omega
  | cons code codes ih =>
    unfold possiblePrimesInBlocks
    rw [List.mem_append]
    by_cases h : n/210 = q
    · have hN : 210*q+n%210 = n := by have := Nat.mod_add_div n 210; omega
      have hp' : (210*q+n%210).Prime := by rwa [hN]
      have hMem := prime_in_wheel_block (lo := lo) (hi := hi) wheelResidues code hR (by omega) (by omega) hp'
      left
      simpa only [hN] using hMem
    · right
      apply ih (q+1) (by omega)
      simp only [List.length_cons] at hqU
      omega

private def witnessCount (lo hi : ℕ) (codes : List ℕ) : ℕ :=
  (possiblePrimesInBlocks lo hi (lo/210) codes).length

private lemma prime_interval_le_witness_count {lo hi : ℕ} (codes : List ℕ) (hl : 8 ≤ lo)
    (hCover : hi/210 < lo/210 + codes.length) :
    ((Ico lo hi).filter Nat.Prime).card ≤ witnessCount lo hi codes := by
  let L := possiblePrimesInBlocks lo hi (lo/210) codes
  apply (card_le_card (t := L.toFinset) ?_).trans (List.toFinset_card_le L)
  intro n hn
  obtain ⟨hnI,hp⟩ := mem_filter.mp hn
  obtain ⟨hlo,hhi⟩ := mem_Ico.mp hnI
  have hCop : n.Coprime 210 := by
    rcases prime_is_fermat_candidate hp with h | h | h | h | h <;> try omega
    exact h.2.1
  have hR : n%210 ∈ wheelResidues := by
    rw [wheel_residues_exact,List.mem_filter,List.mem_range,decide_eq_true_eq]
    refine ⟨Nat.mod_lt _ (by decide),?_⟩
    apply (Nat.add_coprime_iff_left (c := 210) (by exact dvd_mul_right 210 (n/210))).mp
    rwa [Nat.mod_add_div]
  have hq := Nat.div_le_div_right (c := 210) hlo
  have hqU := Nat.div_le_div_right (c := 210) hhi.le
  exact List.mem_toFinset.mpr (prime_in_wheel_blocks (lo/210) codes hlo hhi hp hR hq (by omega))

lemma prime_prefix_add {a b : ℕ} (hab : a ≤ b) :
    b.primesBelow.card = a.primesBelow.card + ((Ico a b).filter Nat.Prime).card := by
  have hEq : b.primesBelow = a.primesBelow ∪ (Ico a b).filter Nat.Prime := by
    ext n
    simp only [Nat.mem_primesBelow,mem_filter,mem_union,mem_Ico]
    grind
  have hDis : Disjoint a.primesBelow ((Ico a b).filter Nat.Prime) := by
    rw [Finset.disjoint_left]
    intro n h₁ h₂
    simp only [Nat.mem_primesBelow,mem_filter,mem_Ico] at h₁ h₂
    omega
  rw [hEq, Finset.card_union_of_disjoint hDis]

structure RankInterval where
  upper : ℕ
  budget : ℕ
  increment : ℕ
  divisors : List ℕ

def RankIntervals (ts : List ℕ) (start stop available : ℕ) (rows : List RankInterval) : Prop :=
  match rows with
  | [] => stop < start
  | row :: rest =>
      start ≤ row.upper ∧ (row.upper-1)^64 ≤ 2^row.budget ∧
      (row.upper-1-(start-available))*row.budget < gainedExponent ts (start-available) ∧
      (row.upper+1)/210 < start/210 + row.divisors.length ∧
      witnessCount start (row.upper+1) row.divisors ≤ row.increment ∧
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
    (hT : RankThresholds ts 0) (hStart : 8 ≤ start) (hk : start ≤ k) (hStop : k ≤ stop)
    (hP : start.primesBelow.card ≤ available)
    (hRows : RankIntervals ts start stop available rows) :
    (k-1).factorial < ∏ i ∈ range (retainedCount k), rankBound (i+1) := by
  induction rows generalizing start available with
  | nil => exact (not_lt_of_ge (hk.trans hStop) hRows).elim
  | cons row rows ih =>
    obtain ⟨hUpper,hBudget,hGain,hCover,hInc,hNext⟩ := hRows
    by_cases hK : k ≤ row.upper
    · exact rank_product_on_interval ts start row.upper available row.budget k hT (by omega) hk hK
        hP hBudget hGain
    · apply ih (row.upper+1) (available+row.increment) (by omega) (by omega) _ hNext
      rw [prime_prefix_add (by omega : start ≤ row.upper+1)]
      exact Nat.add_le_add hP ((prime_interval_le_witness_count _ hStart hCover).trans hInc)

def countFromIntervals (n start available : ℕ) : List RankInterval → ℕ
  | [] => available
  | row :: rows =>
      if n ≤ start then available else
        countFromIntervals n (row.upper+1) (available+row.increment) rows

lemma count_from_intervals_valid (ts : List ℕ) (start stop available n : ℕ) (rows : List RankInterval)
    (hStart : 8 ≤ start) (hn : n ≤ stop+1) (hP : start.primesBelow.card ≤ available)
    (hRows : RankIntervals ts start stop available rows) :
    n.primesBelow.card ≤ countFromIntervals n start available rows := by
  have hMono : Monotone (fun t => t.primesBelow.card) := fun a b hab =>
    card_le_card (Nat.primesBelow_mono hab)
  induction rows generalizing start available with
  | nil =>
    have hEnd : stop < start := hRows
    exact (hMono (by omega : n ≤ start)).trans hP
  | cons row rs ih =>
    obtain ⟨hUpper,_,_,hCover,hInc,hNext⟩ := hRows
    by_cases h : n ≤ start
    · exact (hMono h).trans (by simpa only [countFromIntervals, if_pos h] using hP)
    · rw [countFromIntervals, if_neg h]
      apply ih (row.upper+1) (available+row.increment) (by omega) _ hNext
      rw [prime_prefix_add (by omega : start ≤ row.upper+1)]
      exact Nat.add_le_add hP ((prime_interval_le_witness_count _ hStart hCover).trans hInc)

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
    have hQ := Nat.div_le_div_right (c := 210) (show n+1-211 ≤ n+1 by omega)
    omega
  · have hMono := Nat.monotone_primeCounting' (show n+1 ≤ 211 by omega)
    rw [Nat.primesLE,Nat.primesBelow_card_eq_primeCounting']
    omega

structure NumericRankInterval where
  upper : ℕ
  budget : ℕ
  exponent : ℕ

def NumericRankIntervals (ts : List ℕ) (estimate : ℕ → ℕ → ℕ) (start stop : ℕ) :
    List NumericRankInterval → Prop
  | [] => stop < start
  | row :: rest =>
      start ≤ row.upper ∧ (row.upper-1)^64 ≤ 2^row.budget ∧
      64 < row.exponent ∧ 2^row.exponent ≤ start^64 ∧
      (row.upper-1-(start-estimate start row.exponent))*row.budget <
        gainedExponent ts (start-estimate start row.exponent) ∧
      NumericRankIntervals ts estimate (row.upper+1) stop rest

instance (ts : List ℕ) (estimate : ℕ → ℕ → ℕ) (start stop : ℕ) (rows : List NumericRankInterval) :
    Decidable (NumericRankIntervals ts estimate start stop rows) := by
  induction rows generalizing start with
  | nil => unfold NumericRankIntervals; infer_instance
  | cons row rest ih =>
    unfold NumericRankIntervals
    letI := ih (row.upper+1)
    infer_instance

lemma numeric_rank_intervals_bound (ts : List ℕ) (estimate : ℕ → ℕ → ℕ) (start stop k : ℕ)
    (rows : List NumericRankInterval) (hT : RankThresholds ts 0) (hStart : 3 ≤ start)
    (hk : start ≤ k) (hStop : k ≤ stop)
    (hEstimate : ∀ n f, 64 < f → 2^f ≤ n^64 → ((range n).filter Nat.Prime).card ≤ estimate n f)
    (hRows : NumericRankIntervals ts estimate start stop rows) :
    (k-1).factorial < ∏ i ∈ range (retainedCount k), rankBound (i+1) := by
  induction rows generalizing start with
  | nil => exact (not_lt_of_ge (hk.trans hStop) hRows).elim
  | cons row rows ih =>
    obtain ⟨hUpper,hBudget,hExp,hPow,hGain,hNext⟩ := hRows
    by_cases h : k ≤ row.upper
    · exact rank_product_on_interval ts start row.upper (estimate start row.exponent) row.budget k hT hStart hk h
        (hEstimate _ _ hExp hPow) hBudget hGain
    · exact ih (row.upper+1) (by omega) (by omega) hNext

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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1500000 in
private def dyadicRankIntervals : List RankInterval := [
  ⟨30041, 952, 3, [
    0xb034000002504c83164002740007c1105c130001d0f40013c252b40005c000000b0441d29c4702c000000000000034490001302c350000005c0b,
    0x2c1329c000bc0b000110000d0006d0000019c0b000610003502c2b000000001d0bc00000000001f000000004304c110006b05c000a4970000d02c3b]⟩,
  ⟨30081, 953, 3, [
    0x2c1329c000bc0b000110000d0006d0000019c0b000610003502c2b000000001d0bc00000000001f000000004304c110006b05c000a4970000d02c3b]⟩,
  ⟨30123, 953, 7, [
    0x2c1329c000bc0b000110000d0006d0000019c0b000610003502c2b000000001d0bc00000000001f000000004304c110006b05c000a4970000d02c3b]⟩,
  ⟨30162, 953, 4, [
    0x2c1329c000bc0b000110000d0006d0000019c0b000610003502c2b000000001d0bc00000000001f000000004304c110006b05c000a4970000d02c3b]⟩,
  ⟨30202, 953, 4, [
    0x2c1329c000bc0b000110000d0006d0000019c0b000610003502c2b000000001d0bc00000000001f000000004304c110006b05c000a4970000d02c3b]⟩,
  ⟨30243, 953, 4, [
    0x2c1329c000bc0b000110000d0006d0000019c0b000610003502c2b000000001d0bc00000000001f000000004304c110006b05c000a4970000d02c3b,
    0x3d02c0d00000074130442f034001c400000170442502c001847f02c0004c0005c0d00000000110009d0a40007c0b1ac0d000000d40013c0003400]⟩,
  ⟨30285, 953, 4, [
    0x3d02c0d00000074130442f034001c400000170442502c001847f02c0004c0005c0d00000000110009d0a40007c0b1ac0d000000d40013c0003400]⟩,
  ⟨30328, 953, 5, [
    0x3d02c0d00000074130442f034001c400000170442502c001847f02c0004c0005c0d00000000110009d0a40007c0b1ac0d000000d40013c0003400]⟩,
  ⟨30372, 953, 3, [
    0x3d02c0d00000074130442f034001c400000170442502c001847f02c0004c0005c0d00000000110009d0a40007c0b1ac0d000000d40013c0003400]⟩,
  ⟨30415, 954, 3, [
    0x3d02c0d00000074130442f034001c400000170442502c001847f02c0004c0005c0d00000000110009d0a40007c0b1ac0d000000d40013c0003400]⟩,
  ⟨30460, 954, 3, [
    0x3d02c0d00000074130442f034001c400000170442502c001847f02c0004c0005c0d00000000110009d0a40007c0b1ac0d000000d40013c0003400,
    0x5c0004c00034000006d1c4430440b1fc4709400034490d40004c0d000000008902c0004c0020c170000d0000b000000002b02c1d07c000002914c25]⟩,
  ⟨30508, 954, 5, [
    0x5c0004c00034000006d1c4430440b1fc4709400034490d40004c0d000000008902c0004c0020c170000d0000b000000002b02c1d07c000002914c25]⟩,
  ⟨30557, 954, 6, [
    0x5c0004c00034000006d1c4430440b1fc4709400034490d40004c0d000000008902c0004c0020c170000d0000b000000002b02c1d07c000002914c25]⟩,
  ⟨30606, 954, 3, [
    0x5c0004c00034000006d1c4430440b1fc4709400034490d40004c0d000000008902c0004c0020c170000d0000b000000002b02c1d07c000002914c25]⟩,
  ⟨30658, 954, 4, [
    0x5c0004c00034000006d1c4430440b1fc4709400034490d40004c0d000000008902c0004c0020c170000d0000b000000002b02c1d07c000002914c25]⟩,
  ⟨30709, 955, 7, [
    0x5c0004c00034000006d1c4430440b1fc4709400034490d40004c0d000000008902c0004c0020c170000d0000b000000002b02c1d07c000002914c25,
    0xec000006d0000002c000740d0000b0000004c0d0a411000000740b000130006111c3b1244f0001f034000000002c000bc000f40b0002500000]⟩,
  ⟨30759, 955, 3, [
    0xec000006d0000002c000740d0000b0000004c0d0a411000000740b000130006111c3b1244f0001f034000000002c000bc000f40b0002500000]⟩,
  ⟨30812, 955, 5, [
    0xec000006d0000002c000740d0000b0000004c0d0a411000000740b000130006111c3b1244f0001f034000000002c000bc000f40b0002500000]⟩,
  ⟨30867, 955, 7, [
    0xec000006d0000002c000740d0000b0000004c0d0a411000000740b000130006111c3b1244f0001f034000000002c000bc000f40b0002500000]⟩,
  ⟨30921, 955, 6, [
    0xec000006d0000002c000740d0000b0000004c0d0a411000000740b000130006111c3b1244f0001f034000000002c000bc000f40b0002500000,
    0xbc001640d0003d094000a40004c430000002c650748b04400034000bc002b4530340002c0000000274110ac130001f0340b0001110c5900000]⟩,
  ⟨30976, 955, 5, [
    0xbc001640d0003d094000a40004c430000002c650748b04400034000bc002b4530340002c0000000274110ac130001f0340b0001110c5900000]⟩,
  ⟨31033, 955, 5, [
    0xbc001640d0003d094000a40004c430000002c650748b04400034000bc002b4530340002c0000000274110ac130001f0340b0001110c5900000]⟩,
  ⟨31088, 956, 6, [
    0xbc001640d0003d094000a40004c430000002c650748b04400034000bc002b4530340002c0000000274110ac130001f0340b0001110c5900000,
    0x10c1f0000b000000ac00000000009d0000002c000001305c0b0a4000000d000000004702c00000000000b000a3044000001d0d40d04c8902c1100000]⟩,
  ⟨31144, 956, 4, [
    0x10c1f0000b000000ac00000000009d0000002c000001305c0b0a4000000d000000004702c00000000000b000a3044000001d0d40d04c8902c1100000]⟩,
  ⟨31203, 956, 9, [
    0x10c1f0000b000000ac00000000009d0000002c000001305c0b0a4000000d000000004702c00000000000b000a3044000001d0d40d04c8902c1100000]⟩,
  ⟨31260, 956, 8, [
    0x10c1f0000b000000ac00000000009d0000002c000001305c0b0a4000000d000000004702c00000000000b000a3044000001d0d40d04c8902c1100000]⟩,
  ⟨31315, 956, 4, [
    0x10c1f0000b000000ac00000000009d0000002c000001305c0b0a4000000d000000004702c00000000000b000a3044000001d0d40d04c8902c1100000,
    0x340005c130000002c00124a314c4703417254110d40b034591941f0440000000000002240d13c0b0006b05c0d0000004400000002b483000171c40d]⟩,
  ⟨31373, 956, 6, [
    0x340005c130000002c00124a314c4703417254110d40b034591941f0440000000000002240d13c0b0006b05c0d0000004400000002b483000171c40d]⟩,
  ⟨31429, 957, 6, [
    0x340005c130000002c00124a314c4703417254110d40b034591941f0440000000000002240d13c0b0006b05c0d0000004400000002b483000171c40d]⟩,
  ⟨31485, 957, 3, [
    0x340005c130000002c00124a314c4703417254110d40b034591941f0440000000000002240d13c0b0006b05c0d0000004400000002b483000171c40d]⟩,
  ⟨31546, 957, 7, [
    0x340005c130000002c00124a314c4703417254110d40b034591941f0440000000000002240d13c0b0006b05c0d0000004400000002b483000171c40d,
    0x94000742902c000344f04c0b000000001f00000074110bc0019c651240002c0004c1f00017000830002502c8b000000000b000290742b0000000011]⟩,
  ⟨31607, 957, 6, [
    0x94000742902c000344f04c0b000000001f00000074110bc0019c651240002c0004c1f00017000830002502c8b000000000b000290742b0000000011]⟩,
  ⟨31670, 957, 8, [
    0x94000742902c000344f04c0b000000001f00000074110bc0019c651240002c0004c1f00017000830002502c8b000000000b000290742b0000000011]⟩,
  ⟨31728, 958, 5, [
    0x94000742902c000344f04c0b000000001f00000074110bc0019c651240002c0004c1f00017000830002502c8b000000000b000290742b0000000011,
    0xec110003d04ca70000b000471fc0002c9700035000000440d22c0b0bc000740d04400000530943d0ac000001702c710003500011034000000000013]⟩,
  ⟨31789, 958, 5, [
    0xec110003d04ca70000b000471fc0002c9700035000000440d22c0b0bc000740d04400000530943d0ac000001702c710003500011034000000000013]⟩,
  ⟨31852, 958, 5, [
    0xec110003d04ca70000b000471fc0002c9700035000000440d22c0b0bc000740d04400000530943d0ac000001702c710003500011034000000000013]⟩,
  ⟨31918, 958, 5, [
    0xec110003d04ca70000b000471fc0002c9700035000000440d22c0b0bc000740d04400000530943d0ac000001702c710003500011034000000000013]⟩,
  ⟨31987, 958, 4, [
    0xec110003d04ca70000b000471fc0002c9700035000000440d22c0b0bc000740d04400000530943d0ac000001702c710003500011034000000000013,
    0x4c000001128c610bc0010c0002c000000d0000000000000492cc670000007c0b194000000b03400074001c4000340007c001642b044131b40b09489]⟩,
  ⟨32061, 958, 8, [
    0x4c000001128c610bc0010c0002c000000d0000000000000492cc670000007c0b194000000b03400074001c4000340007c001642b044131b40b09489]⟩,
  ⟨32132, 959, 8, [
    0x4c000001128c610bc0010c0002c000000d0000000000000492cc670000007c0b194000000b03400074001c4000340007c001642b044131b40b09489,
    0x1240b000000001113c00000000002b14c130343b05c29000000001319c00000a70340b0001f0000d02c000000005c000d4130740002c0d044000000b]⟩,
  ⟨32204, 959, 8, [
    0x1240b000000001113c00000000002b14c130343b05c29000000001319c00000a70340b0001f0000d02c000000005c000d4130740002c0d044000000b]⟩,
  ⟨32277, 959, 6, [
    0x1240b000000001113c00000000002b14c130343b05c29000000001319c00000a70340b0001f0000d02c000000005c000d4130740002c0d044000000b]⟩,
  ⟨32353, 959, 9, [
    0x1240b000000001113c00000000002b14c130343b05c29000000001319c00000a70340b0001f0000d02c000000005c000d4130740002c0d044000000b,
    0x2c0d000000000b0441f0341300000000000d40b0002f04c0002c11094470000028c00000110000005c002cc1d22c0d0000000000000000340002c00]⟩,
  ⟨32425, 960, 10, [
    0x2c0d000000000b0441f0341300000000000d40b0002f04c0002c11094470000028c00000110000005c002cc1d22c0d0000000000000000340002c00]⟩,
  ⟨32495, 960, 6, [
    0x2c0d000000000b0441f0341300000000000d40b0002f04c0002c11094470000028c00000110000005c002cc1d22c0d0000000000000000340002c00]⟩,
  ⟨32568, 960, 8, [
    0x2c0d000000000b0441f0341300000000000d40b0002f04c0002c11094470000028c00000110000005c002cc1d22c0d0000000000000000340002c00,
    0x440002c890741311c170ac00000000003504c001840002c290945902c11000670007f000430440003400000000940b0340007c0000000074000002b]⟩,
  ⟨32642, 960, 9, [
    0x440002c890741311c170ac00000000003504c001840002c290945902c11000670007f000430440003400000000940b0340007c0000000074000002b]⟩,
  ⟨32716, 960, 6, [
    0x440002c890741311c170ac00000000003504c001840002c290945902c11000670007f000430440003400000000940b0340007c0000000074000002b]⟩,
  ⟨32789, 961, 7, [
    0x440002c890741311c170ac00000000003504c001840002c290945902c11000670007f000430440003400000000940b0340007c0000000074000002b,
    0x170001f14c2f000000000d04c0b000000000d29c4307c0020c47000170ec1102c6b0000000000044170940b0d4000000002c00000001240d000b5]⟩,
  ⟨32864, 961, 7, [
    0x170001f14c2f000000000d04c0b000000000d29c4307c0020c47000170ec1102c6b0000000000044170940b0d4000000002c00000001240d000b5]⟩,
  ⟨32941, 961, 8, [
    0x170001f14c2f000000000d04c0b000000000d29c4307c0020c47000170ec1102c6b0000000000044170940b0d4000000002c00000001240d000b5]⟩,
  ⟨33020, 961, 8, [
    0x170001f14c2f000000000d04c0b000000000d29c4307c0020c47000170ec1102c6b0000000000044170940b0d4000000002c00000001240d000b5,
    0x290440d000470000002c1f034112740b000001c40013c170000004c0b000000ac0d000002b41300011000002240002c0d0f4000000b0000003400]⟩,
  ⟨33100, 961, 9, [
    0x290440d000470000002c1f034112740b000001c40013c170000004c0b000000ac0d000002b41300011000002240002c0d0f4000000b0000003400]⟩,
  ⟨33177, 962, 6, [
    0x290440d000470000002c1f034112740b000001c40013c170000004c0b000000ac0d000002b41300011000002240002c0d0f4000000b0000003400]⟩,
  ⟨33258, 962, 8, [
    0x290440d000470000002c1f034112740b000001c40013c170000004c0b000000ac0d000002b41300011000002240002c0d0f4000000b0000003400,
    0x2b41d000170343d124000000000000044000002f02c00000130000d0000014c171ac110744f02c290000d0aca72540022c3b0000b000001641300000]⟩,
  ⟨33340, 962, 7, [
    0x2b41d000170343d124000000000000044000002f02c00000130000d0000014c171ac110744f02c290000d0aca72540022c3b0000b000001641300000]⟩,
  ⟨33426, 962, 10, [
    0x2b41d000170343d124000000000000044000002f02c00000130000d0000014c171ac110744f02c290000d0aca72540022c3b0000b000001641300000,
    0xb000000ec000002505c0d0001102c000000d0000b05c0022c130006b0000002c001b4000000b03435074431940004c170000002c001fc00]⟩,
  ⟨33508, 963, 8, [
    0xb000000ec000002505c0d0001102c000000d0000b05c0022c130006b0000002c001b4000000b03435074431940004c170000002c001fc00]⟩,
  ⟨33592, 963, 10, [
    0xb000000ec000002505c0d0001102c000000d0000b05c0022c130006b0000002c001b4000000b03435074431940004c170000002c001fc00]⟩,
  ⟨33676, 963, 10, [
    0xb000000ec000002505c0d0001102c000000d0000b05c0022c130006b0000002c001b4000000b03435074431940004c170000002c001fc00,
    0x490002f0000d02c11000000001300000000290000b1641d00000034250004307c3b0340025c0b20c2918449000110000003400000000000004c00]⟩,
  ⟨33760, 963, 8, [
    0x490002f0000d02c11000000001300000000290000b1641d00000034250004307c3b0340025c0b20c2918449000110000003400000000000004c00]⟩,
  ⟨33846, 963, 9, [
    0x490002f0000d02c11000000001300000000290000b1641d00000034250004307c3b0340025c0b20c2918449000110000003400000000000004c00,
    0x4707c2502c0004c290440b0f43500000074130445300000000001ac0d02c000a46d0000007c1104c0002c00000610000b0ac0d05c000009507c00]⟩,
  ⟨33930, 964, 8, [
    0x4707c2502c0004c290440b0f43500000074130445300000000001ac0d02c000a46d0000007c1104c0002c00000610000b0ac0d05c000009507c00]⟩,
  ⟨34016, 964, 6, [
    0x4707c2502c0004c290440b0f43500000074130445300000000001ac0d02c000a46d0000007c1104c0002c00000610000b0ac0d05c000009507c00]⟩,
  ⟨34107, 964, 6, [
    0x4707c2502c0004c290440b0f43500000074130445300000000001ac0d02c000a46d0000007c1104c0002c00000610000b0ac0d05c000009507c00,
    0x3413000000004f05c0b07cb30440002c000bc7f00000034000000b00000000951b41710c0d19c49164ad0d40d02c17000000444f0ec00194000000d]⟩,
  ⟨34203, 964, 9, [
    0x3413000000004f05c0b07cb30440002c000bc7f00000034000000b00000000951b41710c0d19c49164ad0d40d02c17000000444f0ec00194000000d]⟩,
  ⟨34298, 965, 11, [
    0x3413000000004f05c0b07cb30440002c000bc7f00000034000000b00000000951b41710c0d19c49164ad0d40d02c17000000444f0ec00194000000d,
    0x2b41d0007f034130002902ca32240007c2500000000110003d05c000340b000000000b00000000350440025c000ac00000000001d05c0b18400]⟩,
  ⟨34393, 965, 11, [
    0x2b41d0007f034130002902ca32240007c2500000000110003d05c000340b000000000b00000000350440025c000ac00000000001d05c0b18400]⟩,
  ⟨34489, 965, 9, [
    0x2b41d0007f034130002902ca32240007c2500000000110003d05c000340b000000000b00000000350440025c000ac00000000001d05c0b18400,
    0xb04c3b0001f1640d0003500000074000000025c472d40d0446d000b30000d0000b04c000000002c000001100000074170000002c11000830bc0b]⟩,
  ⟨34587, 965, 9, [
    0xb04c3b0001f1640d0003500000074000000025c472d40d0446d000b30000d0000b04c000000002c000001100000074170000002c11000830bc0b]⟩,
  ⟨34685, 966, 11, [
    0xb04c3b0001f1640d0003500000074000000025c472d40d0446d000b30000d0000b04c000000002c000001100000074170000002c11000830bc0b,
    0x2c00000000000b0f41d184000941f0000d0440b04c2b0005302c000000005c13000000bc0003400254670f400034001c40013c00000250001102c00]⟩,
  ⟨34783, 966, 11, [
    0x2c00000000000b0f41d184000941f0000d0440b04c2b0005302c000000005c13000000bc0003400254670f400034001c40013c00000250001102c00]⟩,
  ⟨34882, 966, 8, [
    0x2c00000000000b0f41d184000941f0000d0440b04c2b0005302c000000005c13000000bc0003400254670f400034001c40013c00000250001102c00,
    0x2c000006510c250d4170000004c9d0341107c4f02c3b0002902c49000000340014c002d40d0d42f0000010c0b0440005c8b0000d0002b00047]⟩,
  ⟨34981, 967, 9, [
    0x2c000006510c250d4170000004c9d0341107c4f02c3b0002902c49000000340014c002d40d0d42f0000010c0b0440005c8b0000d0002b00047]⟩,
  ⟨35083, 967, 8, [
    0x2c000006510c250d4170000004c9d0341107c4f02c3b0002902c49000000340014c002d40d0d42f0000010c0b0440005c8b0000d0002b00047,
    0xd000b309400000650348329c0b000000a417224110003d034971fc1d0440002c00000001c4000a4130000b0000d0000002c0004c000340000011]⟩,
  ⟨35190, 967, 11, [
    0xd000b309400000650348329c0b000000a417224110003d034971fc1d0440002c00000001c4000a4130000b0000d0000002c0004c000340000011]⟩,
  ⟨35299, 967, 9, [
    0xd000b309400000650348329c0b000000a417224110003d034971fc1d0440002c00000001c4000a4130000b0000d0000002c0004c000340000011,
    0x5c110341313c1d0003b02c00000170000b11c000006b04400000000ac0b0a4000447100013000170343b000590000002c00000110ac0b0bc1d00000]⟩,
  ⟨35409, 968, 12, [
    0x5c110341313c1d0003b02c00000170000b11c000006b04400000000ac0b0a4000447100013000170343b000590000002c00000110ac0b0bc1d00000]⟩,
  ⟨35520, 968, 9, [
    0x5c110341313c1d0003b02c00000170000b11c000006b04400000000ac0b0a4000447100013000170343b000590000002c00000110ac0b0bc1d00000,
    0x74591fc1107c000003504c0d2d4650ac1d2740d02c172cc0025400184000000004c2f0000002c2b07c4904c0000000000000000b044000000d20c00]⟩,
  ⟨35636, 968, 13, [
    0x74591fc1107c000003504c0d2d4650ac1d2740d02c172cc0025400184000000004c2f0000002c2b07c4904c0000000000000000b044000000d20c00]⟩,
  ⟨35749, 969, 5, [
    0x74591fc1107c000003504c0d2d4650ac1d2740d02c172cc0025400184000000004c2f0000002c2b07c4904c0000000000000000b044000000d20c00,
    0x254000000b04c110d400074000340005c0002c49000000000b1c43b0003d000000000d02c2514c000bc0b000000001f19c0d0000022c1702c4703413]⟩,
  ⟨35871, 969, 13, [
    0x254000000b04c110d400074000340005c0002c49000000000b1c43b0003d000000000d02c2514c000bc0b000000001f19c0d0000022c1702c4703413]⟩,
  ⟨35995, 969, 12, [
    0x254000000b04c110d400074000340005c0002c49000000000b1c43b0003d000000000d02c2514c000bc0b000000001f19c0d0000022c1702c4703413,
    0x4c000004f0340002c970006d0ac00000001ac1f0340b05c002240d2d4000000000000000110000b0000d000000a49d000671fc53000130940004400]⟩,
  ⟨36122, 969, 13, [
    0x4c000004f0340002c970006d0ac00000001ac1f0340b05c002240d2d4000000000000000110000b0000d000000a49d000671fc53000130940004400,
    0x440005c0002c0007c000000b20c0d00013000001940d00043000130001102c1d000000a435044000006102c3d0ec1d0000b000250bc470001700029]⟩,
  ⟨36247, 970, 10, [
    0x440005c0002c0007c000000b20c0d00013000001940d00043000130001102c1d000000a435044000006102c3d0ec1d0000b000250bc470001700029]⟩,
  ⟨36378, 970, 13, [
    0x440005c0002c0007c000000b20c0d00013000001940d00043000130001102c1d000000a435044000006102c3d0ec1d0000b000250bc470001700029,
    0xf400000000ec0d0740b2b4110000002cbf000000000004c000000b03453000111244f034170ec59044970000002c000942903467000a304c000002f]⟩,
  ⟨36512, 970, 11, [
    0xf400000000ec0d0740b2b4110000002cbf000000000004c000000b03453000111244f034170ec59044970000002c000942903467000a304c000002f]⟩,
  ⟨36647, 971, 15, [
    0xf400000000ec0d0740b2b4110000002cbf000000000004c000000b03453000111244f034170ec59044970000002c000942903467000a304c000002f,
    0x446d05c13000490000002c110000004c000ac00000250f40010c0d0000b000000d40b04c1f0001100017000002744f0000d0000022c0b00000]⟩,
  ⟨36784, 971, 15, [
    0x446d05c13000490000002c110000004c000ac00000250f40010c0d0000b000000d40b04c1f0001100017000002744f0000d0000022c0b00000,
    0x340b000000442b000000000004c00034000004f0940003400000bf074002242b0000b0000d05c0002c830000d07c00000000000002c53000610000b]⟩,
  ⟨36918, 972, 14, [
    0x340b000000442b000000000004c00034000004f0940003400000bf074002242b0000b0000d05c0002c830000d07c00000000000002c53000610000b]⟩,
  ⟨37054, 972, 15, [
    0x340b000000442b000000000004c00034000004f0940003400000bf074002242b0000b0000d05c0002c830000d07c00000000000002c53000610000b,
    0x2c00124351840b0340011c6b22400000110ac0b05c000740002c8304c65034000000004400074130f4000000005c0028c0011c2f07c0019c0002c17]⟩,
  ⟨37191, 972, 11, [
    0x2c00124351840b0340011c6b22400000110ac0b05c000740002c8304c65034000000004400074130f4000000005c0028c0011c2f07c0019c0002c17,
    0x2c00000000a40d1ac000002528c0010c000000002c0d1641702c000000d14c13000c1000a705c1f0ec000000b1fc1d00000034000a41300000]⟩,
  ⟨37330, 973, 12, [
    0x2c00000000a40d1ac000002528c0010c000000002c0d1641702c000000d14c13000c1000a705c1f0ec000000b1fc1d00000034000a41300000]⟩,
  ⟨37474, 973, 13, [
    0x2c00000000a40d1ac000002528c0010c000000002c0d1641702c000000d14c13000c1000a705c1f0ec000000b1fc1d00000034000a41300000,
    0xd4000000000017044000000b0000d0009d044000000000000000130002502c590002f03411000000740b0340005c1102c001c4950003d22c1d]⟩,
  ⟨37623, 973, 20, [
    0xd4000000000017044000000b0000d0009d044000000000000000130002502c590002f03411000000740b0340005c1102c001c4950003d22c1d,
    0x1707400000251acb302c3d044130000b034610741f10c000ac250000b00000034291948b0000d00017000000f40002cbf044000740b0001f04c00]⟩,
  ⟨37765, 974, 10, [
    0x1707400000251acb302c3d044130000b034610741f10c000ac250000b00000034291948b0000d00017000000f40002cbf044000740b0001f04c00]⟩,
  ⟨37915, 974, 14, [
    0x1707400000251acb302c3d044130000b034610741f10c000ac250000b00000034291948b0000d00017000000f40002cbf044000740b0001f04c00,
    0x2fc0d000000000004ca30342b00000000002241302c3b14c110341f29c0007497000000ac0002c0004c00044000000d13c9d0000b1b43b0340000067]⟩,
  ⟨38069, 974, 13, [
    0x2fc0d000000000004ca30342b00000000002241302c3b14c110341f29c0007497000000ac0002c0004c00044000000d13c9d0000b1b43b0340000067,
    0x130340b000002d400000490003b0001f02c00000250ac0b044430002f000170d41f02c29000710340b0001104c00034001b4001241102c2f30400]⟩,
  ⟨38225, 975, 12, [
    0x130340b000002d400000490003b0001f02c00000250ac0b044430002f000170d41f02c29000710340b0001104c00034001b4001241102c2f30400,
    0x14c670a46b11cc102c130000d05c83000000440d1640b0001f05c000000004c000001d000002540b000001940004453000430741729c000000d00025]⟩,
  ⟨38388, 975, 17, [
    0x14c670a46b11cc102c130000d05c83000000440d1640b0001f05c000000004c000001d000002540b000001940004453000430741729c000000d00025]⟩,
  ⟨38549, 975, 9, [
    0x14c670a46b11cc102c130000d05c83000000440d1640b0001f05c000000004c000001d000002540b000001940004453000430741729c000000d00025,
    0x4c0d02c17000000000b034000bc292b411000000000004c000445902c350ec0d04c6122c002243d02c1d1b44f0440b00000000000002503400]⟩,
  ⟨38722, 976, 20, [
    0x4c0d02c17000000000b034000bc292b411000000000004c000445902c350ec0d04c6122c002243d02c1d1b44f0440b00000000000002503400,
    0xd40011c00034290000b094c525c0002c0013c00034112240014c0b0000004413000000001f000000000d0000002c650bc000000005c430740000011]⟩,
  ⟨38895, 976, 17, [
    0xd40011c00034290000b094c525c0002c0013c00034112240014c0b0000004413000000001f000000000d0000002c650bc000000005c430740000011,
    0x22c11000000006705c1f0000002c0d04c2b0ec001fc0d044000002f000a30000b044170000b00000000a70340018413000250ec110002f0000b00000]⟩,
  ⟨39068, 977, 15, [
    0x22c11000000006705c1f0000002c0d04c2b0ec001fc0d044000002f000a30000b044170000b00000000a70340018413000250ec110002f0000b00000,
    0x1ac0b094110000d00000000000003d00071000c500013000950002b03435000000000b034000006d02c1300000000000f4000340002c0005c291640b]⟩,
  ⟨39247, 977, 22, [
    0x1ac0b094110000d00000000000003d00071000c500013000950002b03435000000000b034000006d02c1300000000000f4000340002c0005c291640b]⟩,
  ⟨39420, 978, 16, [
    0x1ac0b094110000d00000000000003d00071000c500013000950002b03435000000000b034000006d02c1300000000000f4000340002c0005c291640b,
    0x2c1d0f4130000b00067000001c42f1644f0000b0009d07c0002c000d40d000000000005c130000022c2510c000000004c170000d00065044a302cad]⟩,
  ⟨39598, 978, 14, [
    0x2c1d0f4130000b00067000001c42f1644f0000b0009d07c0002c000d40d000000000005c130000022c2510c000000004c170000d00065044a302cad,
    0x340002c61000000440004c1f0a41d0340005c00000ad02c0031c1102c1f05c0004c000000d0940011c0004c0d0740b0002b00000000001fc490440d]⟩,
  ⟨39784, 978, 17, [
    0x340002c61000000440004c1f0a41d0340005c00000ad02c0031c1102c1f05c0004c000000d0940011c0004c0d0740b0002b00000000001fc490440d,
    0x44710000004c0003400000170000b000000003d000000001d0a435000110340002c0007c000440014c7f0000b13c0010c0002c0025c000ec0007413]⟩,
  ⟨39972, 979, 19, [
    0x44710000004c0003400000170000b000000003d000000001d0a435000110340002c0007c000440014c7f0000b13c0010c0002c0025c000ec0007413,
    0x4c00194000bc002540d02c1119c000a40b07417000000000d07c000000b1b40d05c000000011c000445907c000ac3b02c00124000340b2cca71ac00]⟩,
  ⟨40163, 979, 19, [
    0x4c00194000bc002540d02c1119c000a40b07417000000000d07c000000b1b40d05c000000011c000445907c000ac3b02c00124000340b2cca71ac00,
    0x5cad044292fc3b0ac000002f0001110c0d1fc0002ca70000000013094830004f07c3d0000002c17000110000003400000132240b10c00000000d400]⟩,
  ⟨40354, 980, 14, [
    0x5cad044292fc3b0ac000002f0001110c0d1fc0002ca70000000013094830004f07c3d0000002c17000110000003400000132240b10c00000000d400,
    0x7c0b044001940000013000000440002c2b0001704c0b0940000000000530341102c4707c0d0000b2542f094b5000000009d0000d02c3507c3d]⟩,
  ⟨40554, 980, 18, [
    0x7c0b044001940000013000000440002c2b0001704c0b0940000000000530341102c4707c0d0000b2542f094b5000000009d0000d02c3507c3d,
    0xd22cc10ac1302c00034000000005c1104c5910c0b1246d03461000002cc29000970440004c0b00000094000000d074710bc001ac170340011c00]⟩,
  ⟨40756, 981, 15, [
    0xd22cc10ac1302c00034000000005c1104c5910c0b1246d03461000002cc29000970440004c0b00000094000000d074710bc001ac170340011c00,
    0x340002c0025c1128c0b04c000006707c000002905c00074000000002c001840000000000250340002c13000110340b0003b000000d45300083]⟩,
  ⟨40968, 981, 23, [
    0x340002c0025c1128c0b04c000006707c000002905c00074000000002c001840000000000250340002c13000110340b0003b000000d45300083,
    0x13c0005c000001f0000b0440d0000002c171240d044b50000010c0b04c000f4000000009459000110000005c8302c002cc111ac2b0003511c0d0001f]⟩,
  ⟨41178, 982, 19, [
    0x13c0005c000001f0000b0440d0000002c171240d044b50000010c0b04c000f4000000009459000110000005c8302c002cc111ac2b0003511c0d0001f,
    0xa43b0000d000ad000430002502c1f13c6d194670003d27413000950001d0000b0000d0000b00000000000bc00164000000d04400000000000b03400]⟩,
  ⟨41394, 982, 23, [
    0xa43b0000d000ad000430002502c1f13c6d194670003d27413000950001d0000b0000d0000b00000000000bc00164000000d04400000000000b03400,
    0xb314590341d09400000001242920c0000000034000bc110000d0001310c710000b000b50001d02c0d0441714c000002f04c0002c000001d0000b]⟩,
  ⟨41608, 983, 19, [
    0xb314590341d09400000001242920c0000000034000bc110000d0001310c710000b000b50001d02c0d0441714c000002f04c0002c000001d0000b,
    0x2c29000250000b000000ac531b40d0001d0000b0000d0d4b302cad0bc001240011c000f40005c0000000034110006b0000000000000110000002c2b]⟩,
  ⟨41829, 983, 22, [
    0x2c29000250000b000000ac531b40d0001d0000b0000d0d4b302cad0bc001240011c000f40005c0000000034110006b0000000000000110000002c2b,
    0xc702c000000d04c000740000000000000441305c0002ca70000002c00000a300000034950002904c00000000440b0ec9703413000001841100017]⟩,
  ⟨42050, 984, 25, [
    0xc702c000000d04c000740000000000000441305c0002ca70000002c00000a300000034950002904c00000000440b0ec9703413000001841100017,
    0x130000007c00000002d4002540b0003d1c4110001d00067124170440d11c0002c000001d0000005c002240b04c000447f02c0d00000000000ac61]⟩,
  ⟨42272, 984, 21, [
    0x130000007c00000002d4002540b0003d1c4110001d00067124170440d11c0002c000001d0000005c002240b04c000447f02c0d00000000000ac61,
    0x3400000001b4000001302c0007c000340b000290001103400000001940b0441d000000000d0000010c290ac0d0001d02c530d4002740b000000000d]⟩,
  ⟨42495, 984, 28, [
    0x3400000001b4000001302c0007c000340b000290001103400000001940b0441d000000000d0000010c290ac0d0001d02c530d4002740b000000000d,
    0xbc1104c2b00089034292fc0009461000000001f02c000449d04c0011c17034650440004c0002c00000171ac0000000000000000b0001f0000025c3b]⟩,
  ⟨42716, 985, 20, [
    0xbc1104c2b00089034292fc0009461000000001f02c000449d04c0011c17034650440004c0002c00000171ac0000000000000000b0001f0000025c3b,
    0x1c40b0002f07c0d05c7f00000000b302c0004c000f40b0000013c0025c0d0000002c00000000000b000000008b11c000941d0340002c0000059]⟩,
  ⟨42944, 985, 24, [
    0x1c40b0002f07c0d05c7f00000000b302c0004c000f40b0000013c0025c0d0000002c00000000000b000000008b11c000941d0340002c0000059,
    0xc1000170941102c00000290740004c0d000350000b1840000000074430001700000000a70340b1ac000003b03413224350aca3000000440012400]⟩,
  ⟨43170, 986, 19, [
    0xc1000170941102c00000290740004c0d000350000b1840000000074430001700000000a70340b1ac000003b03413224350aca3000000440012400,
    0x2d43d0ec5302c000448b0000b05c4f000000342f000130740005c110006702c00034b3000110740d0001302c0011c000a40b10c1704c0d0000004400]⟩,
  ⟨43405, 986, 18, [
    0x2d43d0ec5302c000448b0000b05c4f000000342f000130740005c110006702c00034b3000110740d0001302c0011c000a40b10c1704c0d0000004400,
    0x440d00013000170000b03489000ad02c0014c00000000002b0340b07c1119c832fc431641304400094000000002c0d04c1d00049000710346d00000]⟩,
  ⟨43646, 987, 21, [
    0x440d00013000170000b03489000ad02c0014c00000000002b0340b07c1119c832fc431641304400094000000002c0d04c1d00049000710346d00000,
    0x7c000342f000950000004c1102c00000b50d400000000ec0000029000000000b04c2b1840b000000346504c47000350348b0a40005c9d0000b0001d]⟩,
  ⟨43895, 987, 21, [
    0x7c000342f000950000004c1102c00000b50d400000000ec0000029000000000b04c2b1840b000000346504c47000350348b0a40005c9d0000b0001d,
    0xb0444904c0005c3d0000d28c110ec350a40d0742b304470000000000000000000b1ac000004302c112fc6512417000000006d02c590940d0000b,
    0x2c000000d0440b0007f22c0003400044000bc0b000000000002c4f05c00074000000d00000000001c40011c000d4003140d29c250001305c2b02c00]⟩,
  ⟨44148, 988, 27, [
    0x2c000000d0440b0007f22c0003400044000bc0b000000000002c4f05c00074000000d00000000001c40011c000d4003140d29c250001305c2b02c00,
    0xec1f02c000344300000000000000000011000970341f02c2f0000d02c0000000304000440028c000740d0004320c0b0941300000000002741f00000]⟩,
  ⟨44399, 989, 23, [
    0xec1f02c000344300000000000000000011000970341f02c2f0000d02c0000000304000440028c000740d0004320c0b0941300000000002741f00000,
    0x2f000bf00000000110001313c0b0d4ad05c000000d04c252741f0ac0005c5902c1d19c000000031c000340b000110003d02c650ac6104c7f05c49]⟩,
  ⟨44658, 989, 25, [
    0x2f000bf00000000110001313c0b0d4ad05c000000d04c252741f0ac0005c5902c1d19c000000031c000340b000110003d02c650ac6104c7f05c49,
    0xc51843d0000d0000002c17000000ac0b04c3b0440000000000000340b000000001f0346704c110006d0001d0a40002c11034000000b00000000d3]⟩,
  ⟨44918, 990, 24, [
    0xc51843d0000d0000002c17000000ac0b04c3b0440000000000000340b000000001f0346704c110006d0001d0a40002c11034000000b00000000d3,
    0xb3000a7074001840014c3b04400000250001702c001c41f000000000d1ac7f05c000a40002c470002f0001300000000590440b000490746500029]⟩,
  ⟨45185, 990, 23, [
    0xb3000a7074001840014c3b04400000250001702c001c41f000000000d1ac7f05c000a40002c470002f0001300000000590440b000490746500029,
    0x34000000b00000000003144f0ac170344302c000f4000340b0000004c6b07c490742502c0d000130000b0440d0000007c29000c10000002c0013c0d,
    0x10c65224000000002c000f4000007100059184000000b0001304400000a703425000130001f0a40b19c1d0d4110002b000490000031c1107c13000a3]⟩,
  ⟨45457, 991, 24, [
    0x10c65224000000002c000f4000007100059184000000b0001304400000a703425000130001f0a40b19c1d0d4110002b000490000031c1107c13000a3,
    0x1d0000002c250000d0000b0d40005c47044002b4000000d000250a41302c0d20c2f07400000b50003502c000440014c0b04c0003417000110ec00]⟩,
  ⟨45738, 991, 24, [
    0x1d0000002c250000d0000b0d40005c47044002b4000000d000250a41302c0d20c2f07400000b50003502c000440014c0b04c0003417000110ec00,
    0x250000010c000000b254350001302c0d20c110ac0005c000000b044000006d0000011cbf034000bc0019c2b02c000443b07c001fc000004f04cc7]⟩,
  ⟨46024, 992, 24, [
    0x250000010c000000b254350001302c0d20c110ac0005c000000b044000006d0000011cbf034000bc0019c2b02c000443b07c001fc000004f04cc7,
    0x5c1f0002b04c000000002c0011c17034130bc1107c1d314001b4000440b034000000b0000d04c0005c0000000000000f41328c0d0a40b07411,
    0xb000000003d000890341f19400000000740028cc10446b034000001f000000440b000171240002c000002904c0d2fc000001102c8b034b32740b]⟩,
  ⟨46321, 992, 28, [
    0xb000000003d000890341f19400000000740028cc10446b034000001f000000440b000171240002c000002904c0d2fc000001102c8b034b32740b,
    0x2c000341105c0b0001313c5931c4725c000000b254001ac0002c1d0000004c0010c2907c00000000340029c1719c830340014c00044001c42502c2f]⟩,
  ⟨46620, 993, 27, [
    0x2c000341105c0b0001313c5931c4725c000000b254001ac0002c1d0000004c0010c2907c00000000340029c1719c830340014c00044001c42502c2f,
    0x7f02c1d00011000000940d0bc00000650000d0005902cad04c0002cb5304000000004c0005c350000007c610000b00000000000ec1d0440d0f400,
    0xd0000004435124470340b074000006504c00000000ac1114c000001302c0d000110d400000000000b05c000740d02c00000002540003417]⟩,
  ⟨46923, 994, 31, [
    0xd0000004435124470340b074000006504c00000000ac1114c000001302c0d000110d400000000000b05c000740d02c00000002540003417,
    0x448307c3b034000d41d02c2b0000004c0b1b46b0344325c000740d1240b0004729c000ac3d0440005c0d000ad0001302c000002f0000b13c8b07c00]⟩,
  ⟨47232, 994, 23, [
    0x448307c3b034000d41d02c2b0000004c0b1b46b0344325c000740d1240b0004729c000ac3d0440005c0d000ad0001302c000002f0000b13c8b07c00,
    0x946100095124530001707c110000d1b4290001d02c0d0ac650003d0000000011000000000002c000441303400000c505cb319c0b04c00000d300000]⟩,
  ⟨47550, 995, 32, [
    0x946100095124530001707c110000d1b4290001d02c0d0ac650003d0000000011000000000002c000441303400000c505cb319c0b04c00000d300000,
    0x170440b0000d0002b0bc00000110006b02c53000000000b1fc0003417000001c40002c130944f0000b000000000004c00034000a40002c9729c00,
    0x12400000000441d02c0004c00184000442f000b50000b00017000710000d000c704c11000890000b0000004c0000043000000000d19c4f3141d0941f]⟩,
  ⟨47872, 995, 32, [
    0x12400000000441d02c0004c00184000442f000b50000b00017000710000d000c704c11000890000b0000004c0000043000000000d19c4f3141d0941f,
    0x340025c1702c001b43b0000b0001f03411000890000003400000470000002c17094a30440d000000003b02c0d000000000b00000094670ac290000d]⟩,
  ⟨48197, 996, 29, [
    0x340025c1702c001b43b0000b0001f03411000890000003400000470000002c17094a30440d000000003b02c0d000000000b00000094670ac290000d,
    0x4c0020c000d4470340b0740005c6b02c2b0000007c000a43d05c0b0942f0340000000000c713c00000bf0000002c112b400000170001334c2f14c00,
    0x2b1b435000170000d0440002c49000130008b0441d0000d09413274000000b0000010c0b00011000b31641f0947f0001100000034001240b19c00]⟩,
  ⟨48527, 997, 29, [
    0x2b1b435000170000d0440002c49000130008b0441d0000d09413274000000b0000010c0b00011000b31641f0947f0001100000034001240b19c00,
    0x2cc0b00047000000000000013044000bc0d000c10ec0004c4f0a400000001841d0000b000650340002c89094000341d000000441f02cd304c000000b,
    0x2c430d47107c0b05cb516400000000a4000340b000001fc1102c000003d2b400034170000004c0d07c00044000ec170bc2b000000000d0000002c8b]⟩,
  ⟨48868, 997, 33, [
    0x2c430d47107c0b05cb516400000000a4000340b000001fc1102c000003d2b400034170000004c0d07c00044000ec170bc2b000000000d0000002c8b,
    0x1c40d02c290ec0013c6b0340004c0009400000830000002c000342f02c9d0000000000094000ec6100000000110000b000000001d13c110340000053]⟩,
  ⟨49211, 998, 36, [
    0x1c40d02c290ec0013c6b0340004c0009400000830000002c000342f02c9d0000000000094000ec6100000000110000b000000001d13c110340000053,
    0x49034000000010c00000250740b2fc000441f0008b11c002d40004c000000002c0005c0000013034000000b044000341702cad0001f000111b4a7,
    0xf40019c000006b07c9502c0d0002f0000b05c0d0000007413000000440b05c290d413000530740000000000001948902c000000034c0b0000d05c9d]⟩,
  ⟨49554, 999, 32, [
    0xf40019c000006b07c9502c0d0002f0000b05c0d0000007413000000440b05c290d413000530740000000000001948902c000000034c0b0000d05c9d,
    0xd1ac0000000000170344307c3b0002b02c11000000f40000013044003140d0000002c49000000007f0bc000000d04c0b184000000003411]⟩,
  ⟨49906, 999, 31, [
    0xd1ac0000000000170344307c3b0002b02c11000000f40000013044003140d0000002c49000000007f0bc000000d04c0b184000000003411,
    0x274110000b03400000000a4df0001314c0002c17034000440b0000d00000000350448302c000001f0000b074001c40030400194112cc2b02c5904c1d,
    0x5c6b074110bc0002cc7000000000d00000000130740b22c290005307c000d4000bc490004f0000b04c000340007c6d0000000013044000000010c47]⟩,
  ⟨50264, 1000, 37, [
    0x5c6b074110bc0002cc7000000000d00000000130740b22c290005307c000d4000bc490004f0000b04c000340007c6d0000000013044000000010c47,
    0x7c130008302c0d19c000000b000292d400000000001700059000000340002c3d000000347100000000a302c0004c000000b0342b07c000440000097,
    0x194290000014c000440b000000942b02c0011c000003b000430000b2cc0d04c000008900011000000741f1b42f02cbf000000000d254170003d04435]⟩,
  ⟨50621, 1001, 32, [
    0x194290000014c000440b000000942b02c0011c000003b000430000b2cc0d04c000008900011000000741f1b42f02cbf000000000d254170003d04435,
    0x340004c00000000002519c3d02c3b0340000000000610340004c000d4110000b0001d04c0b044291b4000000d0f4490001f074d30007f0000b0000d,
    0x1640b05c650944f034000ac1100000000173040004c1f000711840010c29034110000b28cad0003b02c0005c1d2cc25000001644f02cc50001737c0b]⟩,
  ⟨50989, 1001, 30, [
    0x1640b05c650944f034000ac1100000000173040004c1f000711840010c29034110000b28cad0003b02c0005c1d2cc25000001644f02cc50001737c0b,
    0x2ca30448b0740b0000d0000010c1104c000000b20c000000d02c1f0007f0000d0ec001b4170000025c1114c00000132d40034c00034000740002c00]⟩,
  ⟨51366, 1002, 34, [
    0x2ca30448b0740b0000d0000010c1104c000000b20c000000d02c1f0007f0000d0ec001b4170000025c1114c00000132d40034c00034000740002c00,
    0x2cb50440014c2900000000000440d0f4490001302c00000c702c00000000741113c0003489094130bc170340b000df0000004c47000000ac00,
    0x130000000000000650000b19c11034002fc530bc1f00059000000000002c000441305c0d0001d0ac0b0000004c2f02ca70000d0006b0d400]⟩,
  ⟨51749, 1003, 40, [
    0x130000000000000650000b19c11034002fc530bc1f00059000000000002c000441305c0d0001d0ac0b0000004c2f02ca70000d0006b0d400,
    0xd0002b1c4000001102c2911c000000b0000005c4f00000034000bc0b07c0004c00074e310c000000004c0005c0d02c00000000000b0343500017,
    0x340004c8b0bc00044000001d000c519c0002c0010c000d41700000094bf124000ec1f02c11034000000007495034110000b0000007c0028c13]⟩,
  ⟨52137, 1003, 35, [
    0x340004c8b0bc00044000001d000c519c0002c0010c000d41700000094bf124000ec1f02c11034000000007495034110000b0000007c0028c13,
    0x4c000000b13c000001711c0d0443d0000002c0d000832540b000e30ec0000000274df02c001fc0029c0b000893040005c00044000001302c0d07400,
    0x170f40d29c0002c000000003459000130740013c0b1b4110001300017000000000d0002b0000b00017044250002f0000d07c6b000350ec7103400]⟩,
  ⟨52531, 1004, 33, [
    0x170f40d29c0002c000000003459000130740013c0b1b4110001300017000000000d0002b0000b00017044250002f0000d07c6b000350ec7103400,
    0xbc001241f02c612244705c0b000002cce50a4000346704c170440d0f49702c000000014c00000000a40d02c1131c3b0ac0b000710001104cc100000,
    0x97000170001322c0b0001f0000d02c250443d0000d000001940b0001f0a4172542b0000004c00000000340002c000006b20c000d41d0001100000]⟩,
  ⟨52933, 1005, 37, [
    0x97000170001322c0b0001f0000d02c250443d0000d000001940b0001f0a4172542b0000004c00000000340002c000006b20c000d41d0001100000,
    0x9d2fc000000d38c000000002c2507400000110a42b0d40005c65034000000b000250340b0002f1647100013000470440003417000430000b00000,
    0xb000002b4170001d000000006d000490002f1841100000074b504c0d044250000b000003141302c0007c000000034c000000d02ca70002b0a40b]⟩,
  ⟨53346, 1005, 40, [
    0xb000002b4170001d000000006d000490002f1841100000074b504c0d044250000b000003141302c0007c000000034c000000d02ca70002b0a40b,
    0x2c110000011c0b1640025c0037c89034000000b000000341302c250008b00000044131fc0d14c000002b0000d0a4000004f0001105c000001302c0d,
    0x2502c1131c000346d0ec49000000f4951644f0003502c7f3040002c1303400000170a40007c000000010c6b3140b0000004c53044003940007c29]⟩,
  ⟨53762, 1006, 37, [
    0x2502c1131c000346d0ec49000000f4951644f0003502c7f3040002c1303400000170a40007c000000010c6b3140b0000004c53044003940007c29,
    0x3b11cdf0f4110000d07c000000b0ac53000000d4250000d2fc6705c000000d02c00000000001d000000000b000000002902c83034000441d04c00,
    0x740013ca3000490440002cc7000000000b07c1300000000000001119c0b0f4000000005c110340004c6b00000034ad02c17000130000b0000004425]⟩,
  ⟨54185, 1007, 39, [
    0x740013ca3000490440002cc7000000000b07c1300000000000001119c0b0f4000000005c110340004c6b00000034ad02c17000130000b0000004425,
    0x4413000000a41f000ad074000ac001c4000343502c3d0002f000000a41105c8b034002fc0002c0d000471845904c00000350000b0000d0002505c1f,
    0x2240d0000b0000000013034110001f10c0002c000001d0000b034003a40004c110000002c1d38c000440b124c134c0d0ec0005c9710c5302c000bc00]⟩,
  ⟨54614, 1008, 41, [
    0x2240d0000b0000000013034110001f10c0002c000001d0000b034003a40004c110000002c1d38c000440b124c134c0d0ec0005c9710c5302c000bc00,
    0x11c4f034000000002cc50000016411000000001707c0b0000004c00000000001d05c9d04c001ac0b03411000000001d0342500000000000a4000006d,
    0x5c000949d02c00074000000b00017044000d40d04c7f3940000000000e302c1314c1125400000170002f02c1f000351940b00000000c10000d18400]⟩,
  ⟨55052, 1008, 38, [
    0x5c000949d02c00074000000b00017044000d40d04c7f3940000000000e302c1314c1125400000170002f02c1f000351940b00000000c10000d18400,
    0x940010c0d0002b1fc0b000000340002c11000b3000170008928c0b000001642b0000d0448311c00000250005302c130000d2b41d000001b4490343b,
    0x340000011184e502c8b05c000ac000341320c0010c0d0740031c0b000000000b0945907c0d000000d411000000000004c170bc0b1c400]⟩,
  ⟨55499, 1009, 37, [
    0x340000011184e502c8b05c000ac000341320c0010c0d0740031c0b000000000b0945907c0d000000d411000000000004c170bc0b1c400,
    0xb0ac1327497000430440007c0d1840013c000440d05cc50000000000000000f40b000130741102c000343b29c1f04c111240002c00194000940b,
    0x2c0005c000000b0000004c00044000d4170000b000950f4b502c490340010c0004c000343b0ac000bc0004cd3000711b41d034000941f0001702c00]⟩,
  ⟨55956, 1010, 48, [
    0x2c0005c000000b0000004c00044000d4170000b000950f4b502c490340010c0004c000343b0ac000bc0004cd3000711b41d034000941f0001702c00,
    0x14c0002c0004c0007c00000000000000029000000bc0002c110ac0002c0d1fcc51ac8b0001719c0000000044350000b000e90000d000b30000000013,
    0x343d0740005c29000002242b2cc0b0344f000000740003400044df184002fc6b02c000ac0d000000000031c0b094000000002c000741111c3b0000d]⟩,
  ⟨56413, 1011, 38, [
    0x343d0740005c29000002242b2cc0b0344f000000740003400044df184002fc6b02c000ac0d000000000031c0b094000000002c000741111c3b0000d,
    0x29c00000001fc650340002c00000350ec0b04443000000ac0014c130000b03400000593a40005c1f12400094000440002c13000000000b000110002f,
    0x2540020c0d000130bc00000001241102c0004c0d00000044710000d000002740002c25074670d40005c97044c70000b0340004c292d417]⟩,
  ⟨56886, 1011, 48, [
    0x2540020c0d000130bc00000001241102c0004c0d00000044710000d000002740002c25074670d40005c97044c70000b0340004c292d417,
    0x7c530000b000130003d000000d4b50940d02c00000110a40b00017000000440011c1d02c00034a305c0b3040003400000000740007c0002c0000011,
    0x1100000000a302c170001d04c650008b034001c40b0440000000000000ac4f0346d000000000b0001f34c13000b305c000001120c0d0ac0000000]⟩,
  ⟨57361, 1012, 50, [
    0x1100000000a302c170001d04c650008b034001c40b0440000000000000ac4f0346d000000000b0001f34c13000b305c000001120c0d0ac0000000,
    0xd0001102c00094000340b000002542b0003b16400000000347f04c1702c2f1b400000000001338c1702c000000d0000b00061044000340000000,
    0x1f0342537c110000b05c3b0000002c00000ad0001f000130000b25c5900000074130002f00000034d30000002c000343d10c000000004413000ef,
    0x28c000001718471044830000d02c000002f3940d19400094001241111c1313c0b000430000b2243d0001d000002d40019c0004c2914c000000b04400]⟩,
  ⟨57835, 1013, 43, [
    0x28c000001718471044830000d02c000002f3940d19400094001241111c1313c0b000430000b2243d0001d000002d40019c0004c2914c000000b04400,
    0x440b0000d000003140000000034130001f00025000891940005c00000110ec000000b0749d0443502c003bc000005911c0d0001702c00000430340b,
    0x2ca7000000340b04c35000110001d13c000000b0346b0001f02c0d0002f000110000025c000d4430440d00000074000000000013000290f42f02c00]⟩,
  ⟨58316, 1014, 45, [
    0x2ca7000000340b04c35000110001d13c000000b0346b0001f02c0d0002f000110000025c000d4430440d00000074000000000013000290f42f02c00,
    0x1302c00000000d42f0f4000940d16400000610000d02c1d3c40002c0007c00000000007f20c00000110340004c0b07c3b0006705c250000007495,
    0x440d05c130a4e30000b0440007400000c72b46111ca70346504c0002c110341f0008b000000000b000170000002c000000007c5312400]⟩,
  ⟨58809, 1014, 44, [
    0x440d05c130a4e30000b0440007400000c72b46111ca70346504c0002c110341f0008b000000000b000170000002c000000007c5312400,
    0xa40004c00094002741f02c001fc000000b1ac2b22ca30002904c1d05c0b3a4000003b044350000034c00000470002502c000000d0000b05c000004f,
    0x34000001d0ac350001100043000290340025c0002c00034470002f0004f000130000005c0d02c000005937c0d2fc110001707c0b0001d19c000000d,
    0x290000b0003d034000446d0000004ca702c000440007c0b0000000000034000000002c611c4110940b11ce514c1307411000590ec8302c6705c7f]⟩,
  ⟨59310, 1015, 47, [
    0x290000b0003d034000446d0000004ca702c000440007c0b0000000000034000000002c611c4110940b11ce514c1307411000590ec8302c6705c7f,
    0x490d40002c0d000170442f00043000950000b0000d074000001f0000d00071000250000b000130000012400000890442b0340010c0000000,
    0x10c000001302c002fc000000b0002b0000d0001700000000110000013c2902c8905c7f07c13034d31940002c000340004c0b304b300000094000f400]⟩,
  ⟨59816, 1016, 51, [
    0x10c000001302c002fc000000b0002b0000d0001700000000110000013c2902c8905c7f07c13034d31940002c000340004c0b304b300000094000f400,
    0x5c000006d000000000b04c6b0f41702c000342911c00000000440b0001d0943b03435000002740d0002904c1102c0000000184250000d0000000067,
    0x1840d0d40004c1d28c290340002c4f00000044bf000170003b03400254000000b07c000000b34c1d000e3000000440d0945300000000000340b00013]⟩,
  ⟨60324, 1017, 40, [
    0x1840d0d40004c1d28c290340002c4f00000044bf000170003b03400254000000b07c000000b34c1d000e3000000440d0945300000000000340b00013,
    0x4c0b03461000002b4003042f0000005c1d000113bcdf000250003d0440029c0025c0b1240007c0002cb522c2516465034003a40002c1320c0007c0b,
    0x2c00000590000b1ac3b0740d39400000130000b0941105c8b02c1300000044000ac00224000009d0003b13c2f000000001300000000490000d02c11,
    0x3141102c0d19c000f40000013034df0001707c003041d02c0020c0002cad000490440d0001d000530000005cb30000b0a40d0bc110000004c1703400]⟩,
  ⟨60846, 1018, 47, [
    0x3141102c0d19c000f40000013034df0001707c003041d02c0020c0002cad000490440d0001d000530000005cb30000b0a40d0bc110000004c1703400,
    0xbc11034130000020c000000b0000004c0003400000000000d0002b0bc1d02c2511c1704c972fc0d0000b0001d0004902c0004465000003c41f,
    0x6b05c110740002c0004c0d11c0b14c7f0ec0d0003d0002928c0b0001f1640000043000000004f034130000002c000a4001b40b0440019489]⟩,
  ⟨61383, 1018, 45, [
    0x6b05c110740002c0004c0d11c0b14c7f0ec0d0003d0002928c0b0001f1640000043000000004f034130000002c000a4001b40b0440019489,
    0xd4001acc70000d04467274ad13ce3000000a40002c430000022c11034000d4002d4470341102c130a4000bc000ec00254000340b000000000004400,
    0x44251940b0ec00000a7000e9074473140002c0005c490bc0b000000740d0a4001841302c2b044c120c0b0001f05c000002f0000d1c40002c1300017,
    0x340038c890000002c59000110000003400000000a40b0342b000170bc133bc11000000000d0740b044000000d1b4000ac0004c1f0000014c000000d]⟩,
  ⟨61932, 1019, 48, [
    0x340038c890000002c59000110000003400000000a40b0342b000170bc133bc11000000000d0740b044000000d1b4000ac0004c1f0000014c000000d,
    0x1ac000440002c00034170000b19c11000000940014c0031400000000d40002c000002b00000000e507c1102c0022c4305c0b000000003d0000004c25,
    0x173c4000440004c0b1940007c6702c3b31c130002b0000d0000b1fc170000d0001134c000007104c170743d02c1f000a337c1303497000250001d]⟩,
  ⟨62492, 1020, 50, [
    0x173c4000440004c0b1940007c6702c3b31c130002b0000d0000b1fc170000d0001134c000007104c170743d02c1f000a337c1303497000250001d,
    0xf41307400000000000005c0002cb32b40d0001f0742f0001700035394000000b000000440b0346d000000ec000342f00000000000741f0000b00029,
    0xbc0b1fc170000007c1114c9d0000019400034000000029cc70f4001244704c170340b10c6d0000d02c2b0000000011000250000002c0d1844f0000b,
    0x2c0d04c001240b11c000340005c0007c671940b044000000002c000ac00000b30000004cc50a4110749528c000000d22c11000170ac590340002c61]⟩,
  ⟨63061, 1021, 49, [
    0x2c0d04c001240b11c000340005c0007c671940b044000000002c000ac00000b30000004cc50a4110749528c000000d22c11000170ac590340002c61,
    0x944302c000a4170006100083044000ac002540004c3b02c490004702c00000133a41d37c000001f03425000000000b03400044890003b0003500000,
    0x1240000000000470000013c0d2740b04c710000d00000000110d40007c001b43d02ce300000094003bc000440b07c1314c0002c0005c6b2d40d00000,
    0x7c000000d074b305c0002cb5034532240b000e919c13000000440037c0b000590000d31c000003b000130001110c1702c0d0000004c0b0743d034fb]⟩,
  ⟨63642, 1022, 56, [
    0x7c000000d074b305c0002cb5034532240b000e919c13000000440037c0b000590000d31c000003b000130001110c1702c0d0000004c0b0743d034fb,
    0x28c1303400000003c43d0007f000000440002c00184000000d05c00000000740029c1302c000000d25c290442b04c000000b0943505c112fc00,
    0x710000b000000000004c000000d0009702c110000d19c0b000000440022c0004c2902c00000ad0000b0340000000044171ac430000002ce522400,
    0x1d14c0004c0d02c000000020c0038c0005c000ac0b0006709400034000446500000034000000b000000002b0942900000034000d4000001f05c11]⟩,
  ⟨64229, 1023, 53, [
    0x1d14c0004c0d02c000000020c0038c0005c000ac0b0006709400034000446500000034000000b000000002b0942900000034000d4000001f05c11,
    0x4c110000002c2b124000000b0001d000590f46d224000442f29c1f0000d02c2b04400184290004f0000002cb5074c11fc0b05c0d000130000010c00,
    0x342f0a41138c000000b000950009d02c130ac17000000341d0000b14c000000005c1f0ec0d000251843d0000d02c6b000130008b0444f000000740d]⟩,
  ⟨64831, 1023, 47, [
    0x342f0a41138c000000b000950009d02c130ac17000000341d0000b14c000000005c1f0ec0d000251843d0000d02c6b000130008b0444f000000740d,
    0x5c490ac0000011034000001302c1709429074000004704c1f000000ecbf0340b22ce50940b0001700083000491ac00000713bc35000000440b000b3,
    0xb00000000130440d1fc251b4000000004c00000170000d000110000007c0d0000b0001104ce902c2f2b4712540007cfb0d40002c000ec000440b,
    0x2c000001d0000b0944f0000004c3d05c0d3c40b0d400000e502c0010c110000034cef0001f03449000650a4130343b0f40028c001641707c0002c47]⟩,
  ⟨65452, 1024, 61, [
    0x2c000001d0000b0944f0000004c3d05c0d3c40b0d400000e502c0010c110000034cef0001f03449000650a4130343b0f40028c001641707c0002c47,
    0x2c2525c3b0001f0001110c00074c1034000000002c4f0000002c0019c11034b50ac0029c0d044001ac650000b074000000022c0d0bc2900000,
    0xd044001b4001841d034000000b0001711c350005909413034000f4c50007102c1300000000000001105c0b0000d0003502c00000000341300000,
    0x6d0341f0440013c2b02c000a4e90440b10c1d0000007c000ec000000b00095000110001725c000340020ca30000002c6504cdf13c0b0000014cf1]⟩,
  ⟨66078, 1025, 59, [
    0x6d0341f0440013c2b02c000a4e90440b10c1d0000007c000ec000000b00095000110001725c000340020ca30000002c6504cdf13c0b0000014cf1,
    0x5c00000002cc0d00013000111840d02c00000000a4000001d224d3000000440002c6b00000000172b4000d4000000b000000000d04c00,
    0x3a4000000b0001d04c110ec00034830a40002c1331c0010c0b00000000000ac000000d02c0005c1d04c0b0009d000111640d000130bc2502c1d03400,
    0x7413000290345902c2504400000002741d000000340b0000007c0d4040034c000000019c6b3ec0b2540d07c0004c000001109429000470006500017]⟩,
  ⟨66712, 1026, 51, [
    0x7413000290345902c2504400000002741d000000340b0000007c0d4040034c000000019c6b3ec0b2540d07c0004c000001109429000470006500017,
    0x2b0000002c001c4130740b0440d0f40029c0025c0d13cbf000172b43b02c6107c001ac670bc0005c4902cef0d4250000b04400000001fc6d00053,
    0x6504c000f40d0000b0000011c0002ce3000490001d0001104c0b0340000029000000341d07c002d47f0440002c0005c43034c5000290000007c00,
    0xac172cc00194f10000007c0002c000d4002240004c29000000440020c0d0f40b28cbf0000b0006709417000110001d0ec2b0000d000110000b22c00]⟩,
  ⟨67363, 1027, 61, [
    0xac172cc00194f10000007c0002c000d4002240004c29000000440020c0d0f40b28cbf0000b0006709417000110001d0ec2b0000d000110000b22c00,
    0x340b00000304a70740005c000000003400044000003d0341725497000d30002f0000b0000d0000002c001640d044130006d11c0002c43000110000b,
    0x2c00000170000b034000bcef0000014c000000b000130002902c00044e503417124000002f31c0000013000000ac00044610001d04c710940002c1f,
    0x2c130004f0ac0d1640005c1f3042f000000001102c0d05c5302c000440d2b4000f413000002240019c6d0000b04c4700017034000000000011]⟩,
  ⟨68022, 1028, 65, [
    0x2c130004f0ac0d1640005c1f3042f000000001102c0d05c5302c000440d2b4000f413000002240019c6d0000b04c4700017034000000000011,
    0x1100043000174040004c000000b0000d0002b07c0004400000003ec6b2d40002c0000000034000006d04c0b034000940002c1100000000bf00000,
    0x1241104c000009702c000d4000000b034000000000025000001640b000f10340013c0022c0d1c4350001f2744702c1d0003d0440b3bc2f00013,
    0x4c0d0ec003ec1105c2f03435184000009d0006502c0000000034000002900000000171c43b02c000ac000740019c0d10c0013c0b00013034002cc1d]⟩,
  ⟨68686, 1029, 53, [
    0x4c0d0ec003ec1105c2f03435184000009d0006502c0000000034000002900000000171c43b02c000ac000740019c0d10c0013c0b00013034002cc1d,
    0x22c000340b07c000440000000000f10bc1302c290744f0000b0001105c0014c000f4c102c11000000340b0009500067034130002b0740002c0004400,
    0x4400000001640002c290d40d07c2510c490000d0000b04c650008931411074000a42505c000440b0d40014ca728c1f0bc170000010ce904c0d00083,
    0x11c0d02c1314c000000b034a30ec0004c1f2d4001c46b0002f2fc0002c112cc0d0000004c000440002c830003d0000b000000001f00000034df,
    0x3d044000342507c0b0ac1704c1102c0000000034531ac590000b1b400184000001d31400000350000d0001302c000007f05c0012495000002b42b]⟩,
  ⟨69369, 1030, 58, [
    0x3d044000342507c0b0ac1704c1102c0000000034531ac590000b1b400184000001d31400000350000d0001302c000007f05c0012495000002b42b,
    0xec2510c00044000003531c1d02c0d04400000170000d000970000004c951940b05c110000b0d413000470341d0009d0a40022400000000000b00000,
    0x5c0b3044f0740d0d471000000001700011000001ac250001310c0003400000000ac0b035070001702c00000000bd01124000340002c00074130ac0b,
    0x2c00000000000b000110007f00000000c70940b000170000002c2907c0d0000007400000002b40011c8b0acdf07c110000004c0d2d4670000002c25]⟩,
  ⟨70067, 1031, 59, [
    0x2c00000000000b000110007f00000000c70940b000170000002c2907c0d0000007400000002b40011c8b0acdf07c110000004c0d2d4670000002c25,
    0x340002c2b0bc00000e30443b00013034000a4000450102c532cc0002c2b10c970bc4f0000d254110a41d1240d0000b274113140007c173ec2504c0d,
    0x1d22c9700035034000942f0440b0006b1b4130000005c0034c00000000340002c00074df11c6504c1f0000b000000004f02c13184000008919c71,
    0x1305c00000000000d02c002fc1d1b40b0004f0a4000000d000590000b0ec0d3bc000d40000000000000442f04ca702c1f0ac000340b1c41700000]⟩,
  ⟨70781, 1032, 65, [
    0x1305c00000000000d02c002fc1d1b40b0004f0a4000000d000590000b0ec0d3bc000d40000000000000442f04ca702c1f0ac000340b1c41700000,
    0x19c1f0943d0d400000130000029ce50000d0004302c1f0001d044a3000c704c00000000001702c3d000000001103400000000bc0b000110001f07400,
    0x940004c0b05c003ec001b46125c6b0000002c9d000000000b04c1f000000bc000340002c000000d10c0b2d417044000ac3b000000000d02c1111c00,
    0xd2b40022d0702c7f034001acc50001f0001104c0b37c000341d04400000130001f0a40005c0b00000000f10000d044e312400000a30340000029,
    0x341d02c00000000f40b0005904c000000005c110001f000490000002c830003b0000000000034c102c0005c130340b194530001d11c0009411]⟩,
  ⟨71506, 1033, 75, [
    0x341d02c00000000f40b0005904c000000005c110001f000490000002c830003b0000000000034c102c0005c130340b194530001d11c0009411,
    0x404111b467000000000b0000d0000002c530000d00013044d31840b0004307c00044002cc000a4e305c13000fb02c000742f0001104c000000d00000,
    0xd0a489254170000002c000000000000000001240007471094530000b0000d41c0b000000002b000bf0000004c0d10ce50440007c0b03400,
    0x1940b00000034110bc1f04c000ec0028c000001d034003a4000940d0ac170007f04c0b000000000002c0d04c000940031c000f40002c00044000000b]⟩,
  ⟨72240, 1033, 67, [
    0x1940b00000034110bc1f04c000ec0028c000001d034003a4000940d0ac170007f04c0b000000000002c0d04c000940031c000f40002c00044000000b,
    0x2c000003b04c0b0440005cb30000d0ac001240b2740d0001702c110001d0000000000000111842b394000340020c4f2240007c47000530a44302c13,
    0x440002c171ac0d16400000c10000029c0013c0038c2f02c000000002c1111c1700000034000441d00000000290000b000b503400000130001d1b400,
    0x74000000000101000a319c1105c0b0941316400000000003b05c130000d0d41102c290940000000044000000b000001841302c0d0006d000000f400,
    0x346b04471000170008b02c130f4110340b2fc000009d034004340011c0b124000009707c0d000a7000113140d0002902c00000001fc0b04c000000d]⟩,
  ⟨72985, 1034, 67, [
    0x346b04471000170008b02c130f4110340b2fc000009d034004340011c0b124000009707c0d000a7000113140d0002902c00000001fc0b04c000000d,
    0x1c40000000044130343b00065000000444f04ce502c1d2d40007c950002503400000110001d02c2f1fc3b07c000000011cad0000b05c00000e900035,
    0xa40b41c6105c0d2b44304c000001102c2f0ac0014c0b1243d0d4000000d07c1702c00001010000b00013000170008b274000340002c0000000,
    0x5907c000002b02c1100000000c719c0d000000000b094000bc3b04c000002b20c00000000340b000003a40003411000000010d0000005c0007c00]⟩,
  ⟨73742, 1035, 64, [
    0x5907c000002b02c1100000000c719c0d000000000b094000bc3b04c000002b20c00000000340b000003a40003411000000010d0000005c0007c00,
    0x14c7f0002f02c290f4000440b164000004303425044d32cc1311c35000a302c000341305c952fc0d3040002c00000530000b1c41d0a40d10c130006b,
    0x10c0d0ac00314000000b034000440002d0f05c0018465000000340b0741305c4f000003bc00000001b4000a44702c0d000000449d29c000340005c00,
    0x34000ec1f000000001702c13124000bc0034c000741114c00000001640b000000000b074000340004400000fb0349705c00000250000b04c1f,
    0x3040b0010710c0004c250000d0001f000e90000d000000a42f044000006137c1f05c0b1b4710005902c0011c11000830001d0941302c110000d0000b]⟩,
  ⟨74517, 1036, 68, [
    0x3040b0010710c0004c250000d0001f000e90000d000000a42f044000006137c1f05c0b1b4710005902c0011c11000830001d0941302c110000d0000b,
    0x2c132240d0940b000000002b03417000000440b07c670000002c652d40013c000000d0ac000f4173c4a707400044250000d00049000001ac1102c1d,
    0x13cef02c00034000001310cbf000000003b000110341702c000a40d02c3d04c0031c000bc00000000000d0001f0000b0440000000074000d40025c00,
    0x1fc8304c49000000002b434000000b05ca3000d311c0d0007104c000006d0440002d0704c00000000942f0340b124000000002c1f000170000025411]⟩,
  ⟨75306, 1037, 70, [
    0x1fc8304c49000000002b434000000b05ca3000d311c0d0007104c000006d0440002d0704c00000000942f0340b124000000002c1f000170000025411,
    0x110002907c0d0000002c00000000000b0007104c0004435164c50340b00013044650342500047074000003d0006102c00034110000b000ad00000,
    0xf40005c113c495000890000007c0004c172b40002c000000019c000000d0ac000001d0004302c000000005c4f3bc1320c000740b044000941700000,
    0x34000000b0001137c0028c1d38c000342b02c1f000130340b0f400000c10942943c2f02c0d194000000b0000d000000006b2cc2504c1f02ca71840d,
    0x2b0001305c0002cb3000970003b00047000001b40b1fc00404110004f0345300000124110000b0bc43000170000004c00000002748b0740004400]⟩,
  ⟨76110, 1038, 75, [
    0x2b0001305c0002cb3000970003b00047000001b40b1fc00404110004f0345300000124110000b0bc43000170000004c00000002748b0740004400,
    0x450d20c0002c000000d04c0b0000007c00000000bc000000d0000019c1102c0d04c0011ca30443b0f4c502c25000f10000b31c35034490000000000,
    0xa4e50000004c000000b00011000ef02c0d34c0005c35000290000b00000000110ec00000000341f0441d0000002c430002b0d4000bc000005300013,
    0x4c1d0440000000000000000002c1100025034970d4ad000000001707c590000b034470740b0000d05c110006b07c0019449254b50000d2fc0b0002f,
    0x7c0b31c00044002d4170343d0bc1d044130ec000000043c00034130010d000a319c0b000000bc0002c000007f0740d05c130ec7102c000348b0000b]⟩,
  ⟨76924, 1039, 69, [
    0x7c0b31c00044002d4170343d0bc1d044130ec000000043c00034130010d000a319c0b000000bc0002c000007f0740d05c130ec7102c000348b0000b,
    0x2c17034000000b0ac6d000133c44f000110000b0000004c1d02c0018417000251fca70448900029034170000014c5903435000000000004c0002c00,
    0xad02cc5000133041105c0d00000000bf04c0d0004902c170002502c2900000000670ec0004c000007138c000000b0001f0002f0009d1940d16400,
    0x25c1f0000d0ac0000000044000340b164000f4290441f000000001d0ec000001702c0d00115124110002913c0b0010f0d40d02c000002b0001f03400,
    0x1073ec1d034000002902c00044000000b0d40003425000a705c0d04c0b000000a4000002f1ac130ac0d000000003502c83044170000b0ec0000065]⟩,
  ⟨77756, 1040, 81, [
    0x1073ec1d034000002902c00044000000b0d40003425000a705c0d04c0b000000a4000002f1ac130ac0d000000003502c83044170000b0ec0000065,
    0x1710c00000000000d0741f0940002c0d000110004f1c4473940000013000b302c0000089034e910c3b074530000b0007f2741300025,
    0xb0000d11c1d124290002b34c0002c8b0000031c0b044c103413000df0000002c0019c000000b000110d40029c000346105c1102c250006d,
    0x83000ad02c650940013c13000000441d2540b00000000471240d07c0000017000000000b00000000000441707c000000d000002cc1104c00,
    0x34000f40002c4704c2f0ac0b000000347f0001100115034df0ec000441d02c000006b0000d0005304c0002c0d000000440b000130000005c000000d]⟩,
  ⟨78595, 1041, 70, [
    0x34000f40002c4704c2f0ac0b000000347f0001100115034df0ec000441d02c000006b0000d0005304c0002c0d000000440b000130000005c000000d,
    0x2fc13094530001d0340b1c40028c6502cfb0005900011000490000b0f400034b50000005ca70001d000670003502c89000170a43b000002541d10c11,
    0x741100047000000000d0ec4f02c000001d05c3d0008b0440d000000008904c0b044c50000b000000a42500000000000bc0007c11034000000b05c00,
    0xb04c113a4000000007417000350000d0006120c0007c4304c2f000000a46b0000b04c590340002d150ac67034b51b40005c7f02c2f0009d0000b,
    0x2c470002b20c0b000df0001f000d3000000340b04c1d25c6102c000001f000130343d0001d1fc0d000530d400164002cc00000003ec0d0440002c00]⟩,
  ⟨79454, 1042, 74, [
    0x2c470002b20c0b000df0001f000d3000000340b04c1d25c6102c000001f000130343d0001d1fc0d000530d400164002cc00000003ec0d0440002c00,
    0x5c0d02c59000c104400034000d41704c00404000000002c000341102c000001d0940007c110001743435000000000b0000000000094e30344f0443d,
    0x44000340000000074000003510c0b0f4003bc0014c1322c0007c6b09411000ad02c8900000044000341307c0b0a4c7034c502c0004c000009727519,
    0x8b000130f4001240002c0d0000005c0b0000d00047000b3094000000b0001107c000a4131b40004400000e30947102c670001d0000b0000d00029,
    0x440d0bcfb0000004c00034110000010d1902c8305c2b1ac00074650f40004c0d394b502c000d41104c00000000ac0d0000b43c0000000034a3]⟩,
  ⟨80331, 1043, 79, [
    0x440d0bcfb0000004c00034110000010d1902c8305c2b1ac00074650f40004c0d394b502c000d41104c00000000ac0d0000b43c0000000034a3,
    0x31c4905c0b034003c40007c2f000ad0441702c470343d0740b13c0d00000000000001102c00074250000b05c491840000000000670000002c1700013,
    0x4c00000a70a40002c00000d30000d0941107c000000b10d013949d0a400000001b400044170000b000000342f000000001d18400000130000000000,
    0x184000008b02c0d000112d40b000000001311c00000000007f38c130347102c00000ad0351b0d4490000002c1737c110000b0340028cbf13c2b0001d,
    0x89074612fc000940b044130001f02cb3000000446b04c000000b0000d0bc1f0000020c3b05c110002b0000002c0014c110000d0740004c0000000]⟩,
  ⟨81222, 1044, 84, [
    0x89074612fc000940b044130001f02cb3000000446b04c000000b0000d0bc1f0000020c3b05c110002b0000002c0014c110000d0740004c0000000,
    0x34000002500013000950000002c530343d04cc505c00034001b4ef0ac000740b000490000b04c4f194000000d05c00000430443d0ac000000b4040d,
    0xb39400000830340034c0004c000acad0000000000094110001700000035070000b164350002b02c000441300000000000000002c4f0003b0000b,
    0x2c00000000000b0000d00000000000ec001ac0b0006d0bc0d02c0004c490000d0f41d000000001300000000110002905c2f0741f034113040002ce9,
    0x2d41702cc107c71224000001d0ac003c40d044000000002c130000002c1700115000130d4290340007c170001d0340b0000014c83000590001100067]⟩,
  ⟨82124, 1045, 79, [
    0x2d41702cc107c71224000001d0ac003c40d044000000002c130000002c1700115000130d4290340007c170001d0340b0000014c83000590001100067,
    0xed010a400074000bc4f05c0007c0b1ac00034110007f0001731c61044130000002c00000000000d28c0029c0b3a41f0440002c000000d0740000043,
    0xd00017000001fc2502c00000130000b0001f000110004f0348b14c0b044170740000000000000004910c000000d02c00094002540b034e304c11,
    0x11034000942904c0011c6d05c00000df0001302c2f0440005cb30009d41c59044350000002c000341d0002b000250340011c0b0a4650000000097,
    0xbc130d40b19c1713cd30000d0008907c0002c0d000000000b00000000000002b29ca302c49000000000b0a40004c0010c00000000440002c0d19400,
    0x41c350000d0001102c131ac000341d000000ac533a40b00000000000000004ce50000d000000000b094001fc00074001c40d0000005c00044290349d]⟩,
  ⟨83043, 1046, 81, [
    0x41c350000d0001102c131ac000341d000000ac533a40b00000000000000004ce50000d000000000b094001fc00074001c40d0000005c00044290349d,
    0xb304c6d02c00044000000b0000010c0000000034000a41d04c0d07c8b02c001241704c110002f0000d02c0007c170000b0000010c0022519044bf,
    0x440000000000b51ac0b2fc000a40d02c590742f04c0d20c000000b05c11000130d400000000440025c000350d02c47000000000007c0005cc50ec00,
    0x1b400314ef1fc0d1951b0001102c0004c000000010cb313cad0a41d034000940b000710340b000000441f00000000130001703425000000000b14c61,
    0x2240b0441d11c000ec611942b000110a40005c00000133ec00000000000d05c350000b0ac4f0003d02c1100000000950941f0000d02c1d28c0005c0b]⟩,
  ⟨83979, 1047, 80, [
    0x2240b0441d11c000ec611942b000110a40005c00000133ec00000000000d05c350000b0ac4f0003d02c1100000000950941f0000d02c1d28c0005c0b,
    0x2c1f000130440b0000029c1719c610340038c0b0001f0342502c00000000d48b000110000d00000000000000d0000004d0f05c29304df0001f02c0d,
    0xc102c00000000341d04c8b00067194110bc170947102c000741f02c000340004c0004400000b50000004c000000b3bc0000000164000f40031d07,
    0x5cc70000004cd30000d0f45914c0b0001f1941d000001840d0007f0003510c0d02c1f0010d000173a4000000b3c4110000002c0003429000b300013,
    0x4c2f000002244f20c0002c710ec251fc0b00000044170001f000000d40b0ac00254250000003411000472fc000340002c111b44f0000b0acb50bc00]⟩,
  ⟨84935, 1048, 83, [
    0x4c2f000002244f20c0002c710ec251fc0b00000044170001f000000d40b0ac00254250000003411000472fc000340002c111b44f0000b0acb50bc00,
    0x1ac004343b0001d000000a4490440005c130340002c0000000000133c49707c25034000bc5302c0d0000000000000e507c130440b1240d0001d000a7,
    0x740d0000b0002500000034130008b3bc1d02c430000004c0b03425000000003b0000002c1f1650f11c0b044001b40d2b4000f40020c0002c0000000,
    0x25034bf34c1302c1f074003ec2914c1704c670000b0003b04400224b50000037c000000004c0b0340005c11000000340013c00000110001700000,
    0xac290010f02c59000002240b04c00000950440d19c1d00083000531940002c00304000001711c000000002c130440038c0b07c00000000bc0d0d400,
    0x1150000d05c000000b25c00034a702c00094110000007c000000b044002b41d2740d28c00000133143b1241702c1d0440d000001c4000003503425]⟩,
  ⟨85910, 1049, 88, [
    0x1150000d05c000000b25c00034a702c00094110000007c000000b044002b41d2740d28c00000133143b1241702c1d0440d000001c4000003503425,
    0xa30000003400074000001f02c0022c00000000341119c130d40d0001f0440b000130000b05c000bc0d000000ac0000000000953c4614040b00011,
    0xb18400000000ac00094000000d3940037c2905c0d044670003b00013000000440b07c3d0000002c290340005c003140004c1102c6b0d50d11c0b,
    0x2c00000110000b184290000007413000000000b0ec000000002c170340014c000a4430340020c7105c0007c00000003a425034c1044350004902c7f,
    0x9d02c4f0ac1104c17001250000000000000130000002c353bc0002c0d1b40007cc722cbf0740004cb314c000ec0b05c000000d0002b044430002f,
    0x341307c000ec0004400164290bc0b0348b184e3000000340000011000171c40002c7f2540d07c430ac170f40b04c000001d02c970d40043c000440d]⟩,
  ⟨86891, 1051, 83, [
    0x341307c000ec0004400164290bc0b0348b184e3000000340000011000171c40002c7f2540d07c430ac170f40b04c000001d02c970d40043c000440d,
    0x44d300000000000341302c00464000000b00000000530d41725c490000b034000004f000000440031c00074654540002c000002b11c0b000000001d,
    0x3c40004c17000430000d314110002b0000007c0002c890000d04c00164670000d11c0004c0002c000440000043000000004f0000b034832b40009400,
    0x440b0001f454b50000005c110000d02c4f04cc11240b05c2900000074130950102c00034830000b000000346b000650a4170940002c000001f,
    0x441702ce90ac431c41f0451b0346d0000b00000000000940011c1f034110002f0f40b074e50ec001ac13000000d4650000d37c001fc2b]⟩,
  ⟨87894, 1052, 93, [
    0x441702ce90ac431c41f0451b0346d0000b00000000000940011c1f034110002f0f40b074e50ec001ac13000000d4650000d37c001fc2b,
    0xd13c0002c97000000340b000003ec111240007c1300053035070003d02c000001d044ad0000029c1302c000940d0000b0740004c0003459000e3,
    0x710341329c0005c0b0001d0000002c43000000a4bf000003140b11c00000000ac1714c1300000034000941d02c1103400000002cc3d10c650ac00,
    0x10c000000007400000000440d02c00000000000d0443b000590000005c2f2540b04c9d0000b000110000004c3d0000011c114641f0003b05c0b0a4c7,
    0xf40b0000d04c7f0002f000000343b09400000ef22ce500000000000002b124000740b05c000000002c00000000a40013c0d044fb02c00000000340b,
    0x2c61000000340b000004642507c000bc0005c0b034000001102c0d2cc0005c00000000a4670003b1ac0d0440011c1f0d48900115000130000002c29]⟩,
  ⟨88910, 1053, 81, [
    0x2c61000000340b000004642507c000bc0005c0b034000001102c0d2cc0005c00000000a4670003b1ac0d0440011c1f0d48900115000130000002c29,
    0x1641d02ca31b4000940020c1731c0d2d4130d41f0000d02c000441302c25000890ec000740014c6b2b4bf034110000b0bc1305c0046c110000000000,
    0x34c6d000252740d07c0010c131840b25435044170000004c000002f034e938c0002c000342b0a4670f4000000b0444f0000002c530002f04c11000c1,
    0x5c00000fb0a4130000002d1b1941707c0b04c11124000941d37c000440b0003d10c000006b04c1719c00000000d4c502cf10ec0d2fc0b0000007400,
    0x34000000000000000000000004c2f034000742502c110340000059000530440013c2b1ac0d02c1f20c0011c0d00000000000000b0008925c3d41c0d,
    0x434111fc0b00000034000003d0000005c6502cc10002b0440b0001d04c00034710440002c43000130000b19c0007c002d400000110001702c00124d3]⟩,
  ⟨89954, 1054, 95, [
    0x434111fc0b00000034000003d0000005c6502cc10002b0440b0001d04c00034710440002c43000130000b19c0007c002d400000110001702c00124d3,
    0x7ce9000110000002c0d00000094002fc4f000654040b05c0d28c000ecef1840d00013000000000b0000022c290000039519000000341d0001300000,
    0x5c0002c110002537c0b000000740d0000011c000008b000003041302cc70bc2927400034b30001f02c00034000740b04c49000000441700095,
    0x949d0440b0002f0001302c000340000000000650740b0ac00000000349525c110000d000000000002c250001f0006d0ac0d0008304489,
    0x440d0004905c3b04c000340002c000ac00000130001f1640003400000111ac0b000000000b0442b04c3d0d4171240d46c6d43c13404000340b00000,
    0xb03400000001c400000110d47f2cc003140000000000000001f0001d000110000b0000005d2502c350008b04c00034000bc0002c00000f10000b]⟩,
  ⟨91013, 1055, 97, [
    0xb03400000001c400000110d47f2cc003140000000000000001f0001d000110000b0000005d2502c350008b04c00034000bc0002c00000f10000b,
    0x2c00044890000b000130000d0ac110001f0000b05c0014c0002c000000004c000001f000250001d164110006d05cad30400000e3184fb0000d02c17,
    0x740002c0d04429000ad000000343d0441d25c950000002c1f04c1702c00000000000d04c000000005c6d0000029c0b0f40d19c3b0a4b50940003449,
    0x14c000f4000340016417074000000b11c110010d03400000e90000d0000007c1302c000449d000ef0d40d0a40b2245305c0002c25000000000020c00,
    0x13c17000e5000000001102c610000d04c0b164000ac0d0bc00000000f40b00000314470001d000a3000170342b22c1102c2f25c0019c0b07c2900101,
    0x1250000d2cc1f044000004713c000003d02c130a41714cb50343b0001d38c000340002c1100013000250001d000110340b04c67000c734c00]⟩,
  ⟨92087, 1056, 91, [
    0x1250000d2cc1f044000004713c000003d02c130a41714cb50343b0001d38c000340002c1100013000250001d000110340b04c67000c734c00,
    0x29cf12540b0010f074351fc00044000000002c00094611ac0b41c000000d000170000002c130d4c537c0b0000010c0004c490440d0000002c0000000,
    0x34530ac1f000ef02c0004c4705c0003425000002fc0b0341105c00000000006d04c3d0000d0000b1c4000440d000000ec000001700000000d319c0d,
    0x28c590000002c17034c70000b074250a400494001ac2f00115044000741f02c4725c251c4000ac000ec0002c111942f22c0b00043000110000000013,
    0x4c0000029000000000b000001649502c000446b000490740d0ac0b22c4f0000d0006107c3507400000833940002c0000000000290341341c1100000,
    0xf42505c9d0002b02c0031c0d2d411000fb0000007c13044470000b000170ac0b0340014c0007c00034170441319400000c50000b10c3b]⟩,
  ⟨93184, 1057, 106, [
    0xf42505c9d0002b02c0031c0d2d411000fb0000007c13044470000b000170ac0b0340014c0007c00034170441319400000c50000b10c3b,
    0xb000000000011c0000013000000006b034001fc1104c00000f105c00044290340b0d4004040d02c000740000000254000000002c0d04c002240b,
    0x2c0d074000d40b0002b03400000970000004c0b074250444302c4713c00000e90440005c0004c59000000003b3040d1841700011074000340002c00,
    0x1940002c11000470000007c0004c710000005c00224a302c000bc0002c0005c53000000003b0000003400000130000b0340000000044d30000005c25,
    0xa4a72fc2f46411000710000d0000b1b4ef07c0d0000000029000c704c000ac0002c350f400000130752520c0b000000000002c0038d070440d00000,
    0xd40d1241f0445302c00034290000b00017000970ec13000110000b0000005c0d000110009d0007f00000000a302c0d074000000b000130341f]⟩,
  ⟨94290, 1058, 92, [
    0xd40d1241f0445302c00034290000b00017000970ec13000110000b0000005c0d000110009d0007f00000000a302c0d074000000b000130341f,
    0x442937ce90340019c001b41d000170ec3d0bc0002c00000491640d454114341f000000000002c170000d13c1d000000002504c0b000b30000000000,
    0x124470940b074001b4003ec112cc0d0000002cad07c0d0000b22400000000001122c5902c00000290440b0340000000000000000034c9702c0004c71,
    0x942f0447f0000d02c6b19c650001105c00000131840b11c002fc4f0342900000074f10340010c0b04c110001f14c000002b03413000171c51b0bce5,
    0x131b40002c0028c002740b43c00044a7254290000005c00304000000d02c00000110bc00094000001d02c0004c000000b0000d00000000df43400,
    0x341d05c0007c6b0000b0013313c4902c110003b00047034000000b20c6104c350a4000440d0000007c2f05c0d02c3d000000000022c00124170940d,
    0xd43d04c001ac00034110003b02c1d0000000000164000010704c43000000340b0940004c0b3147f2740000000074110000000101094000000b2d400]⟩,
  ⟨95422, 1059, 106, [
    0xd43d04c001ac00034110003b02c1d0000000000164000010704c43000000340b0940004c0b3147f2740000000074110000000101094000000b2d400,
    0xb4640005c001240d04429224b519c000001f044652b40d00000094590000d0000b0010f0001102c000001700000000110000002c1f0bc000740b,
    0x2c6b000000ac0b07c003bc4f0440004c0d0740b000000000002c00000350ec001c42f000000340000000184c1034130a400044d30f42b0000002c35,
    0x3ec4902ce3000000003d000000000007c000340005c1302c111941d02c0029c0003400000000000d0ac130444905c0b0010d0000004c0d22c000ec17,
    0xd0001331c00000bf0349d3a40b00097000000bc000000003417000830000002c00000130001f05c000000b0000d04c3b02c2b000110340016400,
    0x3453000000ec1702c950002b0740b0440000133000000003507c0b0000004c0009400000490340004c000440002c7f46c000bc0b29c1118443]⟩,
  ⟨96567, 1060, 101, [
    0x3453000000ec1702c950002b0740b0440000133000000003507c0b0000004c0009400000490340004c000440002c7f46c000bc0b29c1118443,
    0x7c170004304c000001d0000d000000000014c0d02c6728cf10750f044170a4001943b0000002c000001710c000006d0443d0000b07c0038c0d00013,
    0x4c000000b39400094c505c00034000000002c1d0a4110000b0000000025045010000d02cef0bc3d13c0b00000254000000d000000001302c0003411,
    0x11000170340002c0013c7f000fb18413454df0340b044004cc0d0001d2fc17044000008b0000b2240d1b4830000010c13000110ec00000350a400,
    0x1c41f0001102c1d2b4a70000b05c0d00000000000f40d04cc105c000004902c000ac00000001941d1b49d02c000a4000000b000170440004c1d0ac00,
    0x74000003b0000d4340b0f4df0000002c1d04c2514c0041c0019c0b034000002f000000340004c00000000ac0002c49000d30340010ce50449500029]⟩,
  ⟨97732, 1061, 96, [
    0x74000003b0000d4340b0f4df0000002c1d04c2514c0041c0019c0b034000002f000000340004c00000000ac0002c49000d30340010ce50449500029,
    0x20c000002b25c00044000740002c000001f0005900000000c54dc111840d0000b0001f1b40b454000000028c131fc003c42911c0d05c3513c0b04400,
    0x340b000000000005c0049400094000342f0000010c1d0341f0006704c1131c000000b0000d0441302c492740d00017000001c4b302c25000000000b,
    0x2cbf10c000a40b0342514c110009d000000000b000000001302c8905c0003411000130005925c4f04400304001c41d07c470946b0d40005c1302c00,
    0x22c0002c000943d0740d404ad0001100000000000000002c0d10d3702c1320c0d0013305c1f000002541143c001640b34c1704c000344f07c2f00000,
    0xfb28c59044e90a41f000000000b0440d05c00000000002b000000000005c6702c110007103400464000000b034470ac6b02c1d000000a40004c00,
    0xe304c0002c17074000bc0b0341300000454000003b0740b10cef0342b0440013c0d04c0031c2925cd302c0005c130000b1947f0f400]⟩,
  ⟨98915, 1063, 101, [
    0xe304c0002c17074000bc0b0341300000454000003b0740b10cef0342b0440013c0d04c0031c2925cd302c0005c130000b1947f0f400,
    0x4640d0001f11c0000011034a70f453000000001702c2b07400034004e40028c0005c290002502c00000b5000b304c0d0bcdf0d40b000000346100000,
    0x5c000340b18400000130441f304170000002c000440046c0b2542f0001f04c7f1646702c3d000110340b000000ec2903411001073a42f02c2b00065,
    0x2540004c000ec0002c000000d044002b5010000d0000b0000004c3d00000094830000004c290ec0b0002b0746b000000000004425314000000d38c1d,
    0x394000740d02c6513c000000b0342f05c000003504c000001107c970ac0002c134dc0d000f10000010c8b02c0034c000940b14c00074170008903400,
    0x34000f40b000000006d02c29000610340005c250440b000000740007cdf2b4000002b46c0d0f41102c134940000000434110000000059,
    0x5c001c429314000000002c0d27417044000940d0006129c0014c000000b2d4000000b07c000741303400044000d40028c0004c000000b07c00]⟩,
  ⟨100122, 1064, 104, [
    0x5c001c429314000000002c0d27417044000940d0006129c0014c000000b2d4000000b07c000741303400044000d40028c0004c000000b07c00,
    0x11c0b000130bc0d31c6d07c000ac65000250d411000000003d0000003443001390bc0b034134640002c000a40020c35044e50340002c00000000000b,
    0x2c000000005c0b2fc9704c1d000250003507c0b0001113d0f02d150000d0440004c25164001ac000000004c170002b0000010c0d124000002902c11,
    0x341102c0004c1f0000000000000b303483000530010702c00000e302cfb00025044430000d05c00000672240d0d40b000000001100000074710000d,
    0x4c7f1641122c2503400000a30a40b0000046cbf05c3b00000000250003d0341f02c0000000000ad000970000b05c001240002c71044130004300017,
    0x250bc00000113bc0d02c0037c3b0d40b0000007cc71940d0a4130000b0bc0d000000004729c4305c1d000671840002c13000000340b0450100000]⟩,
  ⟨101353, 1065, 106, [
    0x250bc00000113bc0d02c0037c3b0d40b0000007cc71940d0a4130000b0bc0d000000004729c4305c1d000671840002c13000000340b0450100000,
    0x1d29c00000000441700013434000a40d0ac0002c2504c000001100095314000006b0741102c3b000711241f0340005c001840b0000004c000446d,
    0x44170ac0b28c1338c00304000001d000e502c00000000000b000004f411000590340002c000440d0000b0bc43074e9224000001f0000d02c0000025,
    0xd0006107cb302c000341104c350000020c0041c0b0bc170340000065000111ac53000000ac0b044fb000132740d19c2f000ef000000342507400,
    0x341702c00000f10940b07c110009d0740030400000000ac0004c0002c1728ce913d19254130341102c000001f0340b0ec00000292d44900000,
    0x1fc0000000044000bc0b0000d05c0002c000000d000290001305c0b0000000000000110ac0043c000f43534c0002c8b0002513c1711c1f0000d00053,
    0x940d0001707c000a43502c000001129c000004f0ac00000001ac130000b11c0d0440b000c70000000000000831b40d04c672241d10c0b03400]⟩,
  ⟨102609, 1066, 119, [
    0x940d0001707c000a43502c000001129c000004f0ac00000001ac130000b11c0d0440b000c70000000000000831b40d04c672241d10c0b03400,
    0x940b0009703533000110000046c1307400274000342f000292b40d0ec00000000000b000530000002c0d0000000011074003c44702c003943d04c0b,
    0x2c000000013c0b04c1d0443d0000d000890000b0440d0009502c610000011c0000017000000941104c00034000f4170001149413001150ec0002c00,
    0x1302c0010c0d00101000000440014c000001d13c0002c001ac0002c000ad0d184000340038c00000df194b504c0b0008b034000000005c00094b3,
    0x7c00494000003b000130000025c0b0002b2cc0000000000110005311c0d04c0002c0005c001b429124000440b000000001702c0d07c000006700000,
    0x342b04c4f0001d0003502c59000000340b05c2f00000034000442b0940b05ca70000004c0d0d41d0001f0000d0006502d07000000000b3a41d05c0d,
    0x74000000014c00034fb00017000003141d0442902c5900000094002b4000341310c6d0000002c000002900000044002741f05c0b00000000111c400]⟩,
  ⟨103879, 1067, 95, [
    0x74000000014c00034fb00017000003141d0442902c5900000094002b4000341310c6d0000002c000002900000044002741f05c0b00000000111c400,
    0xac1f2240b000000000d07400124a304c0002c110001f3940b000df044000000d05c4f02c000000034c0b0947f11c130442b22c3b0350f02c1f00067,
    0x5c0020c000000002c000ec00000174040d0000029c0b3150d11c1f3bc00044001fcb50001d0340b0001325400034714dc4f0000004c651840000011,
    0x110001302c35000002cc0b22c3d0941f0344f37c17044000006d3a40002c1d0341f094130000d0000002c470ac1d04c0b0001125c0d4640019461,
    0xd0f411000590740b034253bc0002c001ac9d4cc000001f0340b4943b0000004c000d400000000004304ca702c0d0a4002d40004417034002fd15,
    0x38c2f0340004c11094890000002c610000031c2b0005305c00000000f42507c0b2b4000000b4e4d30340011c0000000034000001d000000440b0bc13,
    0x4c0b05c250ac67044000000d074001ac170000d1246d3c40046c1107471000000000b0bc110000002c0005d0f000430ec9d0a40002c1307c0d0440b]⟩,
  ⟨105191, 1068, 116, [
    0x4c0b05c250ac67044000000d074001ac170000d1246d3c40046c1107471000000000b0bc110000002c0005d0f000430ec9d0a40002c1307c0d0440b,
    0x2c000000d37c0b1941f0000003400000130a40b00000074c702c1300011000430000d00017044000a42f00000000000000d000002b4000000002c00,
    0x4f02cf10340025c67194110000012400000250340002c000000d02c7f0a4112243d00000000000440d164170000b13c1d07c2b0000004c0012400,
    0x350441f00013000000006b0000b0007f04c000a40d07c53000a3000bf0000002c0010c9504c472d4110340b000c141c8302c000008b0bc000001d,
    0x74000440d0000002c1f04c000440b0000005c0000000000000340b0000000011034003940038d0d0001305c0002ce9034490740b000000a417,
    0x43001150f471000250ac0019c00000111940002d3d3bc000001704c0d074000d4000440002c1305c000003b0a44f000000940b464a34dc000002b,
    0x34000ec0b095251ac11000fb000670344702c000bc000340b07d01164000f4e30001302c0d2cc000740b07c0d1241105c000007f0000002c132b40d]⟩,
  ⟨106526, 1069, 117, [
    0x34000ec0b095251ac11000fb000670344702c000bc000340b07d01164000f4e30001302c0d2cc000740b07c0d1241105c000007f0000002c132b40d,
    0x43c170006d0000002c000440029c0000000000890440b0000000000000130343507c1d11cd31fc0b000170000010c000001104c000bc000008b0ac00,
    0xd40007c0002c000000d05c0b0441311cc13940046c000ec0d000000000002c0d000000000007c000953902c1d0010728c0b04400034610003b04c2f,
    0x1b400184170740004c0b07cf10bc4302c0d22c1300000000110000b0a42b00017000470f4250340004c000440002c003ec0027413000000745925449,
    0x2b4131ac00000e518400000e302c47000530340020c000000004400194350000b034001240b0000d000890001104c001c4ef000170000d0940b25c35,
    0xec0b2d40020c170a41303400000000003d044670000000059034000d45304c652cc0b34c000000002c1d000000440d454000ac2502c490341110c0b,
    0x2c1d034000000b000a3000470001f000001840b19c00000bf02c00044000001f0000004c2b1c400034000002900000034000009d05c000000002c00,
    0x1ac0002c000000005c000bc0d0001d000000000d04c1102c250003502cc5044130f4171fc2f00000000004cc250740b0ac49001191b4530000d3a411]⟩,
  ⟨107875, 1071, 112, [
    0x1ac0002c000000005c000bc0d0001d000000000d04c1102c250003502cc5044130f4171fc2f00000000004cc250740b0ac49001191b4530000d3a411,
    0x164110000d00000000000003b0340b04c2f4f400094df0441d0010d05c000000002c0d3c40000000000ad0000b000130000d02c110000005c0003400,
    0x2b411034000000002c970000029c0b0740003413000671c40d10c0b0006114c0005c29000000000d000e50003d02c170001f0440b000000d48b,
    0x3d0a41307c1111c000000010c0d46c0005c0002c0d274002cc1d0002f05c00000250001302c0007c65034531b53304c002540b000000442b05c00,
    0x13c000000b3040d0442f04c1707c000002902c000008b0000b0d411034a33a42504cd302c11124a70000b04c650001f00000034002d41d02c00044ef,
    0x44000000004c2502c0000071001010740010c1731c0b14c00000250ac0d4640005c00000000440b43c002cc6141c000743b20c0d0a41f0d4bf49413,
    0x34250000002d3707c1d0000b00017034003a4004340003400074000000002c110008920c0d10c170440002c0d000000bc0b000c545413000a30000d]⟩,
  ⟨109256, 1072, 123, [
    0x34250000002d3707c1d0000b00017034003a4004340003400074000000002c110008920c0d10c170440002c0d000000bc0b000c545413000a30000d,
    0x14c0004447000000340b124000001102c130001d0001710c350000b29c67034000003b0006d00000000110004f02c5300013000651ac2f1642900000,
    0x6100000044831fc0d2541302c5904400094000000004c0d000001241d19c0b000110000b0001f000003c40040400000003ec000341704c0b00025,
    0x25c0b000001241300137000000a42f0000d04c000000005c9d14c4307c4f000000000b044000341d02c002d4000342b0003d1ad1b02c000001d4cc0b,
    0x2c0005c3d0000b000110940004ce3000170340b0000011c4902cfb2fc001b50f034c12cc000000d0000005c130bc114e44337c8307c0d0001702c00,
    0x1240d02c3b000000000003400000000a461000000440002c000340002c0000000000000001731c111641f1fc2b0000b000113a4350000003400000b5,
    0x890342905c2b000002b4000440b00000000000f41d000130000013c001fc2b02c130001d000bf034a70000b0006b0341f02c29000430f41300000,
    0x941f0008b000001640002c0d000000000b0ac0d0d41f00011000004640b0001d0012519c0005c7100025044001ac1d02d3904c003bc0b2540d00000]⟩,
  ⟨110660, 1073, 120, [
    0x941f0008b000001640002c0d000000000b0ac0d0d41f00011000004640b0001d0012519c0005c7100025044001ac1d02d3904c003bc0b2540d00000,
    0xac0d1fc000740000000034130014b1644702c00000000441f00000184290000d37c6702c0014c000001105c000000d0000b000111240003417,
    0x3040b0340004c3b000001953725c1f02c13034290000b0000d314b31c4000001f02ca30ace504c0b10c0004400000350bc1314c0002c1109400,
    0x130bc004340002c170a53d0740d0006d11c114540b0001f0ac00044000bcd309400000830000b000000340004c00044b50f400094000000000000,
    0xa4170000002c0d000134cc0b2fcc141c653ec003bc11074290003b0341702c533c400034000749519c1702c5946c0007c0b0340000000274a700011,
    0x1104cb3000000000b05c001b42902c710d4650eca70441704c0b0000d34ca30440004c1f000001ac000bc4902c350001d0000d0000007c4700000,
    0x34293bc11000000001f4f40002c00034350000004c000340000000000000000b000e30000b0006b0004f0740d0ec000002f00139044000000b0f40d]⟩,
  ⟨112094, 1074, 119, [
    0x34293bc11000000001f4f40002c00034350000004c000340000000000000000b000e30000b0006b0004f0740d0ec000002f00139044000000b0f40d,
    0xb074000ec110340031d0f05c8904c0000000074002cc6505c8b0bc00034004040b000000ec2502c00001070d4130009507c1702c47044970000b,
    0x2c714541f1b40b0440d0000049400094000000b10c1307c0d02c11000290740d00000094112d4000001300000000000000031400034000acad02c00,
    0x446d02c13404df000000001f11c000d40d2b4290000002c000003d02c113ec00000491ac130345907429000000340b04c000000005c00224003c400,
    0x2b000000000005c2904c110000b38c3b034000002f0000010c2b000251941102c1707c7f0000d044c104c0b000170000002ca30000d0009d13c00,
    0xbc0d0442504c000f44302c1d2d4110000b000004dc61000000340005c0b3bc003a400000973c4000001107c1d4640d02d4b11c000000b034e500013,
    0x4c00034000442f4f495000291fc35044000000002c0009400184000000010c0007c1105c0002c00034000000000049034170000b20c130740000000,
    0x7c0b000bf000470000d000c50001102c0d000000000b164132d4c705c000740002c6507c2f0000b0d471000000a41319c000000002c0d05cad]⟩,
  ⟨113561, 1075, 130, [
    0x7c0b000bf000470000d000c50001102c0d000000000b164132d4c705c000740002c6507c2f0000b0d471000000a41319c000000002c0d05cad,
    0xd0000002c1107c1303400000000002f0000b04c8300000000001ac000000d001250000b0001d000970ac110000d05cdf0003b04c000347f,
    0x1d3c40002c130ac830440b0943b0000004c17034c5000890bc0d0006b02c8b05ce50740004c1113c0d02c000004729c0b0a46d19c254e4000011b,
    0x5c000002f2241f0000b13c8b0440d02d0d0a42b3ec0d000004640b4cc3d000710007f0004928c170a4000341302c000006d0440000067000000001f,
    0xad000530940d000b30d40002c1f0000000000000170001113c9d034000a40b0ec000340b000130d400045011942518400034002542b0000b07400,
    0xb000000000000000000000000005c000740007c0000013044000000d000001240b000a720c0002c000001100000000000000d02c110001319c0b,
    0x2c9511c000000b000490000000107034000440b000000342f02c1d22413454c10000038c0d2fc350946d4340d0440031c0004c2b0000013c1102c0d,
    0x19c2f02c1d000610343522551000130001743c110000002c6b0f40002cdf034000000046c250d4e90005305c000a40b0440010c1f1941d0001704c97]⟩,
  ⟨115054, 1076, 120, [
    0x19c2f02c1d000610343522551000130001743c110000002c6b0f40002cdf034000000046c250d4e90005305c000a40b0440010c1f1941d0001704c97,
    0x1253d07c0004c0d000000000b0740000013000111ac0d00000000000440d02c430a4170004f04c473140b000590740002c13034c70940000011,
    0x194111c40005cad0001d02c0007c004940b0000014c0004400074000ec0b094000440000000034000f42f41c170341f02c29404110000b000431642b,
    0x11c0019c11000002d4130000000000164e30341d02c000000034c002753704c3d0348b0003502c0d11d0f00000000000940029c0b0440d0ec0000000,
    0x3040d04c0b0a41107c00034bf000e922c4902c6b05c000000b034ad0a41d0006d0ac0002c0013c0025c0b0002505c0d000003940028c0002c3d0ac17,
    0x34000001d02c4f14c3d0000007c000000004c0b25400000111b461000130002f0d41111c0b035330ac430f400034003bc00000710001d04400,
    0x440052c2b02c000a4170000b000c704c1d0000d000002fc4f000000001102c0000000000b30441f0bc5902c003ec1305c0b00000124000a40d00000,
    0x170000d0000019c0b074110342502c00000000bc13000000ec0b07c17000110000d22c4722400044134642902c0025c0d0005904c0020c0003539]⟩,
  ⟨116574, 1078, 136, [
    0x170000d0000019c0b074110342502c00000000bc13000000ec0b07c17000110000d22c4722400044134642902c0025c0d0005904c0020c0003539,
    0x7c00044130344913c0005c0002c110008b0f4000341d000170000d1fce50000b254290000b000001c40d184000000004c000ac3b07c002cc0b11c9d,
    0xb0d417044250000004c0041c0d044433c4590000d000d320c25000a74041704c0b1c42b0000002c1f034000001d000000000002c0010c000000b,
    0x2c251fc0004c0b0740020c6705c00000111b40b314000002b02c00034c10000000000034290bc0028c0012400000e30ac1f034170014b11c0002c13,
    0x4c1f02c00000170001100000000001b400000000001f02c000000002c0d2cc000002b000590000000000000000000b0011b0000d000130001f184fb,
    0x349714c0010c0000000044000740b03413095150442b034000001307400274b502c004dc0d30411000000000b164000f41102c2f05d0d2fc000000d,
    0x4f4000f459494290346b02c130440019c0b00000000e904c00194000000b0342f11c173ec4f0740020c00000df0001702c00044000a40b04c2500000,
    0x131b40d09507000711840004c0002d0d0000d0006505c000000d000ad0002f02c000ec2b044ef000b50001d0000b0340005d3300000,
    0xd5390000b0006b0007125c0004c7f0000d02c3d000000000b044000ac0007c9d10c0002cdf0348b4540b074110340007c17124000ac1102c293941d]⟩,
  ⟨118119, 1079, 133, [
    0xd5390000b0006b0007125c0004c7f0000d02c3d000000000b044000ac0007c9d10c0002cdf0348b4540b074110340007c17124000ac1102c293941d,
    0x74001ac5302d5100000000000ac00034000740b0a4b30004904c0005c890340052c1f0000b000c5000c70440043c00000000740d07c1105c3b,
    0x940d0000002c4f3041f0340b0a400000ad00011000b500013034bf0442f02c0029c1300043000000002502c000000d0440b05c4f000000341300035,
    0x6b03400000f10000b000ef0ad0f02c000001700011124000a40b0d4130440005c002540009400034000003b02c00034fb04c00000e928c0000011,
    0x5c110ec1f4cc00000590000d02c130a4000000d000d30440000000000004940b0441d13c0b1941712443404000002b0000007411000891c40b04c59,
    0xb0000d0f40004c000001d0340000000124134641700000000350001f000000940b224000000002c610001d11c000bc0d13c1302c00001510340b,
    0x2c1331cc50340b000001fc000000005cb30000b0344f0ec0002c0d094000f4002740007c00000000000d4dc2b04c43000bf00000000170443b02c00,
    0x2fc0002c000002b044132d4001240d0ec00000002b40d02c0007c1102c0004c2907453164110010d41c00034470940b000000006100029000000446b]⟩,
  ⟨119694, 1080, 129, [
    0x2fc0002c000002b044132d4001240d0ec00000002b40d02c0007c1102c0004c2907453164110010d41c00034470940b000000006100029000000446b,
    0x440004c0013c0d0000029c003140b000170ac00000290004704c0003411124f102cb3034c1045190001d05c0b00000194e302c0000000000174f489,
    0xec1d07c00185390000002c1114c003a40b0000004d1b0008b0d4670000b000111c4000741707c25044a311c000bc6d02d010000d0000b0000007c53,
    0x349d0440005c970014b07c0020c1103400000d302c00034291247119c0025400000000940d02ce3000110000d07413000000000b000000d46b0000d,
    0x430000b044000340000025000290443d02c3b1fc134040b0ac0043c00035510bc1102c5305c000000b1b40000000000000003d04c3502c0007400,
    0x2d429000133bc1f02c0d0002b00000000110746105c0b31c0d00000000250000d434000441346c0b1b4000008b05d3704c0000000034000000030417,
    0xa32742502cc110c1104c0b0001f14c0d00133000000ac6122c170011502c1f04c4f000000342905c8302c2f034110000b000e50d4000000000065,
    0x1d04c000000b044000000002cb50340004400094000000b31c290ec00034c51b4000000d00000000ad02c0005c110bc6b0000d1fc0012413]⟩,
  ⟨121308, 1081, 141, [
    0x1d04c000000b044000000002cb50340004400094000000b31c290ec00034c51b4000000d00000000ad02c0005c110bc6b0000d1fc0012413,
    0x4c0d0bc7100065001390340002c430740000025001250000003400000170bc0b000670000b00000394170001f0000d0740004443000130340b0ec00,
    0x1c40b0340014c000001d05c00000a70001334d0f000000001107413404000ac000a40b000610000002c000440022c00034134541f02c000ac000000b,
    0x2c0013c1707c0b0ec000000d094000002b1fc0b3c43504c0002c003ec6d000173bc0011c000010707c000bc11000001ac000d4894f41104c0d02c00,
    0x2b02c0d2fc1300025000290346511cd3044000d4b302ca305c2b02c1d14c000000d0015b04c000000020c000440b0000d094170f40025c1103400,
    0x9d034170003d0000004c0b224000001103400000430000d0440037c0002c470000019c1d0000d14c0b000250440002c000001f0001d00095,
    0x744f000000000007c0002c000000d0000b000350000d1b4000000004c0b04400000950000000013000000346b1c4c702c2b4340005c0b0000031411,
    0x11000610000d05c00074590ec0007d1928d5b02c5304413000290340000000044130340002c7f094000000000017000000340b545370001322449,
    0xb27400000000004710c000000002c000001d1940b0000005c0d2b4000000002c1d41c1f0a40b000f10ac2f0d43d04c0d0440002cb300000]⟩,
  ⟨122939, 1083, 146, [
    0xb27400000000004710c000000002c000001d1940b0000005c0d2b4000000002c1d41c1f0a40b000f10ac2f0d43d04c0d0440002cb300000,
    0x34000003d0001102c00000c500013034000d4002240b034000000007c000a41d52c0005c0d0000b000000000d07c1d000174f4a700049044e904c0d,
    0x7c00000c102c2f035070000b4e46d34c3505c130a4000003b0001120c0002c490010f464111640004cef02c67000000000b0001307c000011504400,
    0x4413000000acc737c0b46c170000002c00000c50f4000000d0000b0001122c0d13c00001330442f0001f3a40002c000944905c1d0342b0f4b50a55d,
    0x5911c130f41102c000000d25c170000010c25000610740004c0b05c0014c0b034000443b00025034000001f00000000000000b00000,
    0x5c0b044a329c6d0000000000000110d44f034000941f0740004c4725400000000340b04c000740d02c11000000000019cb30002b02c0d3ec1f0000b,
    0x2c0d2542f0440b00000034000002b044250000b04c170000002c1f46cb5000130001119400000000015b000350000d0001d25c8b000000340002cbf,
    0x2c001c40041c002fc7f38c2504c11000c70ec0002d250000002c830000022c1f044000a515034000740013c0b034430f4f1000172b4000001d,
    0x74470a43d000110ac0d0000b000000bc0d0741305c1f000000a4000002502c004340014c00194131640b0ec110000002c6704c000000d0002b]⟩,
  ⟨124596, 1084, 142, [
    0x74470a43d000110ac0d0000b000000bc0d0741305c1f000000a4000002502c004340014c00194131640b0ec110000002c6704c000000d0002b,
    0x5c0d0ec253ec0002c00034950000b000000455d0002f31c250000b0744f1ac0d000130ec110000005c004cd0102c0d000530000b000170346d,
    0x254dd4b034000a40004c000440000053000a702c000000028c0d000000006b04d194941702c000740d04c001fd3d000000440b22c0007c710ac83,
    0x2cd510000b04c000001f000350f40d0000002cb50000d11c0b0000012453000002fc1d02c9d000000000b034170006525400074710000002c0000013,
    0x4ce50002b1240d02c610001d34c0043c3b094000000b00000044000342b13c00000290343d05c0b0002f10c11000000000003400304110006700025,
    0x13cc10001f02c0029c7f0d40b0006120c13044a305c4707c49000134340d02c000000000000000970d47102c00044290000b0000d000530741100017,
    0x340031400000000000b094130009702d3922411000000351b0000b0441f000df074000000d0000005c0038c0d02c00044000ac000006504c000000d,
    0xef0a40016413034170000002d190000004c4700011184001ac00000000340b14c2f07c0b04c352b41d0f5150000005c2500000000000000b19411,
    0xb094bf000004dc0d0000004c0010c29000000003b0440d07c001c4170000d0440b075610d40002c1707c130015b0ac000001102c3b434000000b]⟩,
  ⟨126286, 1085, 145, [
    0xb094bf000004dc0d0000004c0010c29000000003b0440d07c001c4170000d0440b075610d40002c1707c130015b0ac000001102c3b434000000b,
    0x2c671941143c0b0d40005c000001d0000d11c0b0bc973041702c0004c0020c7f07c2b00000034132242500000034000000000000044001240002c4f,
    0x4040002c17000110009d34c0000000000000340010c2b02c132d40002c4f00017034131840007c0d000950a4003bc0b00000000000bc0d0441307400,
    0x46c0d10c0019ca3044000340005c0b1c400074000006b5740003411000133940002cfb000110f400184000000b0000d0000002c1700097034290442f,
    0x44c7035333c417000df02c000bc130000b07d39000000a40010c1d2cc0b43c000946d0014b044000342b0000029c5302c00164000940b0000004c00,
    0x490001d2b41f04c430000d0a400000000ec0d02c00000005440009400000111b4000d40002c0004400000490010d000000ec0b05c1d0000d0001f,
    0x28c130440b0d50705c6700000034110740002c00000000000b094890000010c1f0000d02cbf0002b1fc0b4f43d04c170740d0002f0006102c0003400,
    0xf400184350350102c130011911c4f04400194000340b000000740d05c0004c2f000110ec0022c0b0000d094e9000f100000000c10000005c0000000,
    0x29c5304c2902c00184d30bc0b0ac0d1ac110001d0000d0000004c000ec0002c00000350442f494253140002c1f000fb2fc0b0002900000000001c400]⟩,
  ⟨128009, 1086, 142, [
    0x29c5304c2902c00184d30bc0b0ac0d1ac110001d0000d0000004c000ec0002c00000350442f494253140002c1f000fb2fc0b0002900000000001c400,
    0x22c7f0d4000000d0000b11d1519c0002c2f05c4304d0f000000000b0341d05c130004903400000000000013c0002c11000000341f000e30ec0005c00,
    0x350000007c1d34cad0441702c6704c001854b0446d00000000000000d0000b584000000b0001107c0025c0020c133141105c0d000291640b00000,
    0x340b000000003b094472746b044590341d000170ac13034000004f000250003d05c0b0000d000b302c131c40d37c1f2d4470452502c000002f0000b,
    0x2c00000130000b0342f0740000017000834dc0b000c11641102c00194000342b0d40000013000174f44f044002544904ca70000014c1f46c3d02c00,
    0xa4c502c003a40007c0d04c3d13c000bc670ac000001702c0d0440002c430000d04d5b0001d37c002740004c110f40b0000000000034110008900000,
    0xac0004c001ac000006d0000b05c0d04425000000000000000000713041d02cc73940003400164490000b0341d0bc0002c3b000170001100013,
    0x4c290000011c000740002c002b4000000b034110000005c0038c2f0440b0d40003443000fb0ac0d0008b000000015102c00000000000b4549500000,
    0xd05d5d41cd3164530344f09400000130f40002c11001390341307c000449520c000004902c2931c0005c6107c0d000130000b000250341713c11]⟩,
  ⟨129759, 1088, 156, [
    0xd05d5d41cd3164530344f09400000130f40002c11001390341307c000449520c000004902c2931c0005c6107c0d000130000b000250341713c11,
    0x7c110340b0000028c25000130742f0011502d01000000440b0000007429000000440002c17000430340b000000007f034610941107c0002c0000035,
    0x1ac1105c1302c000000d000000000004c0d0000b07400000a70d51900000124000000004c0b0001f224170bc250000000000044b50000d00000,
    0x1b4610000d02c112cc290000b03400000df00000000001fc67315330012502c000a40d0000005c002544702c1314c000ec0b000002fcad0444f03400,
    0x1f39400034890440b000532743d02d67000000341f000004340b04c00000000bc000001125c130940d0745902c830f4000014b31c000001f04417,
    0x44590750722c00000000002902c0d000a7000000740d5441300017000110ac0b000130000b0440005c0003400000000006500000074000ac0b00000,
    0x4540b000d30000d46c1713c11164002fc1f3bc0000000000004040003413074114cc0b034000000002c9d0002f0000005c000346502c00094e30d40b,
    0x2c17044005840b464000000000011000430000b000000001f02c2b0000d09400000000000011d5b074110007f25c00000530bc0d1b40010c3502c00,
    0x340002c000440004c0005c8900000034490001325c0002c170d42902c6707c001fc114f40d0000004c000000d38c0b07c000741300000000650000d]⟩,
  ⟨131537, 1089, 147, [
    0x340002c000440004c0005c8900000034490001325c0002c170d42902c6707c001fc114f40d0000004c000000d38c0b07c000741300000000650000d,
    0xac130ec1700000034000001d31c0b000110a4ad0000028c2500000304000341702c3d0441f000590a4002740b04cc520c2b02d0f0012507c001ace9,
    0x6534c000755d0000d02c4905c9d0000b2d4b3094000000d05d190000b04c0d00000000001c453000000bc001b41102c00000170340b0740011c3d,
    0x4c53194173c40004400000000f40d0000002c000bc3504c974dc00000e50747104c0002c1100000000000348b0001107c0b0006b3143b00000,
    0xd320c0b0f4490ac0010c00044250ec8902c0004c0007c0b000000bc00000130342502c000000d0000b0011b000bf124000440005c0d02c000a400,
    0xd001010000002c8b0341f0000004cfb0002b3940b0d411034ef0001f0f42510c17074000000b00000044950a40d3040000000000000340000000,
    0xed1b0340002c25000004340b1941d0000038c00000132b4000442505c7f02d370005907c6d13cdf0341302c11074000340b1ac0004c1105c0000029,
    0x2541c13001190000b0000d2cc0002c7f0440d3a42f0001d07c0b00139000c711c0005c13000000ac0007d5102c2f04c17000350000014c0d07400,
    0xbc000000d00000000a704c7102c0052c6505c1114c250004f000000440005c0b04c0d0f40b0a4000000004c00000000440d0d42b3ec950000b03400,
    0x5840b07cad0342f0000022c170002b000000946503411000b50000d0a495044004940b000c707c6702c0d0015b0006b0000005c0002c000004907c0b]⟩,
  ⟨133356, 1090, 159, [
    0x5840b07cad0342f0000022c170002b000000946503411000b50000d0a495044004940b000c707c6702c0d0015b0006b0000005c0002c000004907c0b,
    0x2c1128c1d0000b13c0007c000000d3c43d3040b1640d0440002c00000004e4000440059c000002f19c000349d1ac00000000001113c130002502c00,
    0x5d0d02c110000d0a40009400000170741307c2f0006102c650001302c590ecbf43c00034001fc1700000000000000b0741303400044000a4000002b,
    0x107000002cc115741d000130000b0000037c000001704c6d074490000d28c4302c83000002551b0000019c0b000e511c2502c0d00000044000ec1f,
    0x34000942f000130448902c0022c1f0340b04c1d0000003497000110000b0001f0ac290000d04c00000001ac0d0005902c3b000001c40b4cc000440d,
    0x44000008300000034004540004cb5000000d46d02c0005c000000000011034000006110c0002cc53a4250ac1311c2914c000000b000000000016400,
    0x3d05c0b0001d56c0d00011000531641702c00000000000b11c0004c2b4f40d0003b02c29094130440b05c1f19c0000000000000340002c1752c00,
    0x7443044ef0000002c00000a7000110000d124000000b43c13000e9000ad0009722413000170340b2cc110004703467000000001f000000001309533,
    0x2f0009702c00000000740b1b400044290340000000000470000038c1302c00034111fc650000d07c0002c17000001840b04c000940d000000bcd3,
    0xd14c000002910c0b0340007c1302c110000020c1d0007f0340b0953d1c400000000441d05c650005911c0002c0d0000014c000a4c5034c104c00]⟩,
  ⟨135207, 1091, 146, [
    0xd14c000002910c0b0340007c1302c110000020c1d0007f0340b0953d1c400000000441d05c650005911c0002c0d0000014c000a4c5034c104c00,
    0xb50343b20c4f04c11000ad02c00000000001305c000002b094000015d1240b000001ac0b000000342f0a43505c110340019c130001f37c0b00017,
    0xb000001b461074000440d25c4331c9d0000d04567495012fc1714c000003b41c0b000890001102c00094a304c00000110004302d515840d0000b,
    0x2c6d0000d0000b00013000a30343507c710000b11c2b0a43b02c000000004c000000d13c00000250013700000194df05c0d0441d19c000bc0002c00,
    0x1702c3d0345300000000000740009400000000340002c1104c0d02c17000000002f04c000001f0000d044003c40b4340013c00000670002b10c00,
    0x11900000000000003b05c250d40b3bcc52745304c0d074170440007c000001302c002d459074000bc2b0340b07c003a40002cb3394110008b40400,
    0x7c710001728c0d0940002c350013304c0b044000bc7f00043000c70340b1ac17000000356f0000000089001370441302c1d0340007c0b0f41119ce3,
    0x2513c001fc000f40005d5b0ac4722c1102c130000005c3b0440d00000000004e51502c2b00013074000009d044000000b04c000006d1241d,
    0x350f0740b00017000000d561000000340002c00074110340b0009510d510440028c0002c0d29c000d40b0000d0012504c1f20c000740002c0014c0d]⟩,
  ⟨137094, 1093, 172, [
    0x350f0740b00017000000d561000000340002c00074110340b0009510d510440028c0002c0d29c000d40b0000d0012504c1f20c000740002c0014c0d,
    0x1129c000000002cbf04c000ac0011c000002552c0b0440037c0000000034290440020c000bc0b4340004cc10ec00000000001105c290001f34c00,
    0x494000001102c0005c0d0000b000000000000000000290000d0001f0011b02c0d16417001390ec350740002cb3000172740b0f400034000000000013,
    0x4c0019c49000110000b0a4000944702c0d10c8b000e53ec000000b05c891fd5d0001d0009503400000000007102c61000000742f3c413044d300000,
    0xa4000006759c00044250001d02c0000013034000ad154cc1f3bc110000038c0b0344f05c0b10c0d000b50001d31c0000013094000000d0000b04453,
    0x440b000000742b0005903413000290003b05c002cc0004c00034000001105c2b0000b0002f044ad02c6d000003140d07c4f0008302c000340005c0b,
    0x2c29034000000b000ef000110f4000002f04c0b000e30000002c000000000011074000001f04c00034000ec00000000340005c0043c0007c0002c49,
    0xdf02c000003519c1f1840d04c11000000000d1ac8b02d3d0004302c000000005c891243d0002909411000130000b00000001370000034c0d00000,
    0x5c1d13c0d044005bc00000000340b044000006b00119000c14943d04c290000002c0d074250ac13000e90000b28c000000d02c00000490002f03400,
    0x3c4000001f034a711c2f02c000001d0000b1c4290341707c130ac0d0000b41c492d41304400000000000d000000740002c97000000000b094132550d]⟩,
  ⟨139006, 1094, 162, [
    0x3c4000001f034a711c2f02c000001d0000b1c4290341707c130ac0d0000b41c492d41304400000000000d000000740002c97000000000b094132550d,
    0xbf16435001610f4110001f3ec0d05c6b0000002c0d4f41d00047000130946d0a4000ac0002c000000003400000113944904c0b000170000007400,
    0x41c4f0000b14c0d1c400044c70001359c0002c000440005c0b1940003400000a70003502c83000114e40b000000000009411034000000002c0004c00,
    0x56c8b05c002d40002c2b000290440000017000132740b20c2507c1d0000d000b30ec00000e50000b04cf105c250000037c000440d0002f0001725c43,
    0x34130001d02c000010f0000b0006b03400000ef09449034112b4000000002c5907c004cc0d544000011b02c0d04c000a40b000e334c1d001370000d,
    0xe907c0005c000340b000001ac2f02c250ec0029c00000c50440b0000003400194000007f07c0037c6114c1102c4f074000ec00000110ac0007d19,
    0x4704c00000b314c0d07c0002c250002b044000009d0000d04c290003d0000b0d42504c0b05c0000000000890451510c590a400034710000b00000,
    0xb0008b0000000000000001fd5d0000d07c1104c5311c000002b044000001313c0b0ec000340002c00000a703400044002546102c3d000000000b,
    0x2c00000000bc0b2246b124973040004c590340b000110000002c170ec1d044350354b000001940d05c004e43d00013000002740010c0d0006102c11,
    0xac0d02ce51841d20c170342f0001f0004f0011b0a41302c000340002c000d41f04400000000001d1c413000002fc0b05c2b0001104c000341d0007f]⟩,
  ⟨140957, 1095, 168, [
    0xac0d02ce51841d20c170342f0001f0004f0011b0a41302c000340002c000d41f04400000000001d1c413000002fc0b05c2b0001104c000341d0007f,
    0x7417034111246b000001b4b50000b0001d0013d07c2538d5b0f4005d4170000002c001c4135bc00034170000b0003b034f102cd3044a3404000a400,
    0x10c001ac111b40002c0d000000000b0940d000000001752c000000b0011504c7f00000000000000004c1f0a40002c000bc9d20c0b0440d00025,
    0x125370bc0d04c00044002540003489000000006102c1d000e910c110d4000bc170000d0a41102c000f40031c00000001940d34c0b164000002503413,
    0x446b1b40b03400000430945905c003ec0002c2b034001c40b05c0d000110001d0000002c000440007c0b000000001d28c29000173141302c0000167,
    0xe3000000ac1702c833a41107c0d28c13000bf0000b00000000130000010c112b55d000000a40b04400034b50001f000130003b0002b2243d00000,
    0x25c000440002c0d22c000ec0b00011000004641f2540004c00000670340002c00000000350d001610ac1102c000f4a70000b0341d05c1f04c471fc00,
    0x943b000000441305c0b000000740002d3d04c0000000000000000b0740d13c00394110006104c00494250000002c17000003040d2b533000ef0d400,
    0x340043400000000a4a30000002c2b034110004300000034000000005c3b0000b001010440b0756f000000000d4e400164000005338c4705c0b1b40d,
    0xb0000000059034112cc000000013c530f47f00000000000d40004c8b034670000b05c000001302c000002918411000170000002c6d000df0940b,
    0x2c49000950000b31c0d0440011c000000005c0b0442f0000d02c0007c5305c0d0941345400000110003d0744907c2f0ec1118400034000d41302c1d]⟩,
  ⟨142936, 1096, 164, [
    0x2c49000950000b31c0d0440011c000000005c0b0442f0000d02c0007c5305c0d0941345400000110003d0744907c2f0ec1118400034000d41302c1d,
    0x7c0002cfb000000006539417044000000d000000740002c890000002c130000046c00544000350f0ec000004f0340b00000044bf074351c46b00000,
    0x4cc612242f0000011c000000b25c0003417304f1000110940000043074e902c67000290000d0001f0440b0946d0017502c000000d1ad1904c4f,
    0x5c0d0a50f000ef04c0002c00000170000b000130000000000034000000b3148b00000000000001704c00094110000d02c1f10c130d40b035610003b,
    0x130342b000000004756c8b000bf000290442f02c170d551000001fc2b0000014c1d0000002c25034001b40004400034470740b0000000011000e5,
    0xb000294cc131640d4dc0005c0002c0d0000025c0b0bc1f0440004c000000002c002b4001b40b0001d000d3044950006b0a41702c0d00000,
    0x2b40004c0d0740002d1b224250353d0001f0003d1940b05c0004d0713c49044001c40d04c3b19c0b000000a400000470000d0ac35000000740003411,
    0x1105c0002c00094000000b000000001700167034350441f0000d1642502c13044001b42b000a72d40d02c00000490000b0d4110009d20c1700000,
    0x1111c430000b5bc000000d02d5d0bc000d40d0a42b0000b0000007d251843d000172cd4b0001d0344302c1307cc11fc00044000003b00000,
    0x14c1d25c0005c0d000000000002c000eca3000df000130942f20cf1034000000b0002b0340b00000000135d41734c5300000034e904cfb0440b0003d]⟩,
  ⟨144953, 1098, 160, [
    0x14c1d25c0005c0d000000000002c000eca3000df000130942f20cf1034000000b0002b0340b00000000135d41734c5300000034e904cfb0440b0003d,
    0x3140b11c13164000441f20c430001d0f4ef000254042b000000a41129c0d000000000b0001105cc702cad13c000740004c354e40d02d19274590440b,
    0x2c002b4000f40b000c104cdf0007f035374cc0b05c000341d02c000001152cfb04c8b0bc0d044000000004c0d05c000000007c000000038c2b02c0d,
    0x3bc0002c1f04c000340028c110940022c43074000000002c590001702c00034110000000000000000442b000000000b0d4000002929c2510c002fc13,
    0x4c5304400000000000d0001f0000b000000d43b0003d1b40d3a41d0ac1f0000d02c00194002240020c110000b0003505c0002c0003413184000017b,
    0x11c1746c1d044000004902c3b13c000440b001371b489000000001359c0b000290001107ca30342b11c17000970342502c13000000000b0bd2541c61,
    0x164002d40010c000006105c133a400074110340002c2904c1707c0000000000000342f0440002c0d194a707cd30d400074671640b2540d04c0000000,
    0xd1240b0001300011034000ac610008b02c00000003140b03400001610ec1707cf102c0004c000940b194004540d000001c4004e40002c9d37c00,
    0xa495034c70000002c000444f04c6d0d43d0001d0440b0002905c00000bf000a3000000002507c0b03400000131c42b034110001714ce50008307c00,
    0x2c174553d07c0b04429000f10000d000fb184002cc5904c1d02c0010c0000047000130000002c35000650000b044000bc000940d00101,
    0x295d40d0001d0ec0b3bc000340002c4907c000ac00000110000b00000094530f40d000710001d000000442b02cc10000d0002505d39000130342f]⟩,
  ⟨147023, 1099, 174, [
    0x295d40d0001d0ec0b3bc000340002c4907c000ac00000110000b00000094530f40d000710001d000000442b02cc10000d0002505d39000130342f,
    0x754b000000341f05c000008302c350001d00000035510f5370440d000130000b000170000b0bc290000d2cc115ec17094ad04c000001119c0b0001f,
    0x4340b00000000e300053074490000d00000044000000d000250000005c290001f0000b1840056c0002c00034250443d000892fc0002c6505c1104c0b,
    0x2c3d0ac000000b04c000016f0d459000000000b07c1d0007102c0003400000891acdf0341d0000004c29000c50009504417034130ec000000002c00,
    0x1302c00000495442913c350ec000002505c710001102cc70009d02c0d0441d0a400000000ac8b000d30001f04c0b124000000d11c000000005c11,
    0x34111943b0013d074130bc170000b034c10000022d5b034000ac000000004c0002c250000d0000025c000000b14c430000002c110f4000000038c0d,
    0x4c1107c000343d02c2920c000000b0001700000000f104c001ac0b0342505c0004c004055d07c00124004940002c000001d0440b1fc004e400,
    0x5c67184001c4111940d0000007417000000000002cef0ac0d41c250740011c0d254a72240002c170007f2d4000001f0a4004640b0340004400000c5,
    0x394250000b4f4000442b194004040004c0d02c1f000170740b000115fc2f000000000002c11034350000b0014b0341325c0043c000001f02c2f04400,
    0x44000000019c0002c2f464b337c0005c00034005740b000001ac2911c1100000034bf304e30440b00013000000000059c1d0a40004c0d00049000b5,
    0xd0001302c670d4000340b5bc0007c000950d0000005ca7034832740002c1100000000130003d044c702d330000d04c0b000003a44f034710001d]⟩,
  ⟨149135, 1100, 180, [
    0xd0001302c670d4000340b5bc0007c000950d0000005ca7034832740002c1100000000130003d044c702d330000d04c0b000003a44f034710001d,
    0x34df000000000b04d250001102c171940007400000fb0000b000b30a40004c00000000001f0341104c0002c00034e512471074000001700000,
    0x2b000000440010c670940d02c00044002b40d0a400000000002b07c970740b000110000b13c530000022c5907cef29c000000046c2f0f40b5ec13,
    0x4c0b0000d05c350004f0f4000340000011000000006b0008b11c000009d3c4610000b044000007f02c71000170ec000000d0009502c13000bf0340b,
    0x2d3d094b30340b000110011b1642f0001314c0b034001244f02c0d000c5544ef0001d0d40005cd35840d20c470a41100013074430000031c0002ca3,
    0x940002c000d50f38c000441319c0d00000000000440d02c47000e502c0000000000000a4a700011124250341d05c0b000115d4000010704c0000017,
    0x1f000350740d13c0025c000440b3040004c000001f2cc0000017034001640002c6d0340004c0005c5311c0b0ac000002902d0113c000741f10cad,
    0x27400000000bc3d0ac1702c0004c000000b52d61000ad2d41122c1f0000b0006507435254000a45900000044130000002c610000d28c0b14c0009400,
    0x34170d4000a400000000002f124fb0341f0002b02c00034430440004c17000000941f0000d02c13000170ec0d000000007f0000b094113c4000000d,
    0x1d0000b0ac000340005c00000001c46702c0011c000000b0006d09400034005fc1302d372d4000000b0002f0440000000000890002b02c110f400,
    0xad000175440002c0d1c4000f41d00000000110000b13c0d094000441307c0d000c1000f10000b0ac0000000074000452504cc5034000a40000000]⟩,
  ⟨151274, 1102, 187, [
    0xad000175440002c0d1c4000f41d00000000110000b13c0d094000441307c0d000c1000f10000b0ac0000000074000452504cc5034000a40000000,
    0x1330bc0002c000000014c0b05c132240d0006731c110001d05c000000002c000d4000001f034000000002c29034e90000b000170003b07c0004c11,
    0x11000000001704c0b1ac002d42b02c610341319c6d0450725c0b000000009d03429000d338c0d04c650017502c000015b000110000d3940000000,
    0xd4e411000c5000000340002c000944710c0012400001150341d000004340b000e90940b0003b28c000bc6504c0d0000007c00044000340b22400,
    0xd40b0341d0001105c130ac250016f000000000037c0007c00000002d4e304c000ec0b11c2910c0002c000f4001fc170342f0000002c1d044001c40b,
    0x2cfb04c002540b044000000d2fc53074000000b2240010c6702c1105c1f1855b0000004c1100000000000000000000074652cc4f41c0005c0d02c00,
    0x440002c0d000970bc1d0006d03400000290ec0004c0002c3d0740002c115ec130ac0d05c000440000167574000000b0000d0ec65000000000003435,
    0x6b034293a47f000114cc0b04c0005c1d034000940007c0d0d45905c1102c0013c0031c610440d07c0b000130000002c490a4000000005c00,
    0x442b37c000000002c1743c0d2540b000250000d39400000000000b0000007c000ed010f4fb00011034000002f02c4305cef04c0b0006500083,
    0xbc0007c130440d0000000047000000440059c1702c4f0015d224350343d22c0005c110341302c1d00000000831245904c000340b000000001d07c00,
    0x5c650000b0002f0000004ce5094170001102c00000000a40b6155114c0d0004704c0002c000001752c0b04c0000000000000ac0d1842502c0016400]⟩,
  ⟨153449, 1103, 189, [
    0x5c650000b0002f0000004ce5094170001102c00000000a40b6155114c0d0004704c0002c000001752c0b04c0000000000000ac0d1842502c0016400,
    0x34000000004c0002c11074000a4000340007c000000b03400000004540019c7f000003140d0000b0000029c0d4dc110010d094c70000028c000d40d,
    0x4c9d0000002c1f034000440b0000005c000002f0441d41c2b0a4000004702cad000d30001d000110000002c00000250ac0b0008b00013000350001f,
    0x434640011c0b000610441f02c135ec530000005c0d0bc0b000002240d22c2b1240000000000c110c0002c1d00013044b5034000013d00095,
    0x5c29000bf074000001302c000000d0000007c2b04c110ec473a4005840b29c950000b03400094590440003400000003c4290004904c0b5fc00,
    0xb27400000134e40000000000ad001010340000061000000440025cfb20c490340b56c1704c0d02c0037c110000010c003141d02c0d0002b1ac0b,
    0x2c0d0012505c0b000000340004c00000650440b0000052c3502d0f07400000295d44f19c00000001fc2b000130440d000491b41f22c290341102c00,
    0x3b02c4707c0000161000000000010c00000110002902c2f0000002c00094e3000ad0006705c13034a3000000000b0344f4dc250ac6b2cc3d00000,
    0x2f0000000000434000a40d07c0b0acc72240d05c110d413000000003b0440002c1325c000002b000000000b05c1f0941d02c001ac000000d0bc11,
    0xa4110000d000000000002c000354b0000b4941f10c4904425574173bc0b4cc000440d0bc591846705c00074250000002c0d04c110000b0011b0341d,
    0x74110340007c1729c000ac13000ad0000002c0011c000000d000002cc8334c9d28c0002c0019c0d000001640005c001ac0b0440022c0004c53]⟩,
  ⟨155661, 1104, 183, [
    0x74110340007c1729c000ac13000ad0000002c0011c000000d000002cc8334c9d28c0002c0019c0d000001640005c001ac0b0440022c0004c53,
    0x174640b0001104c004e4e33bc0d07c2502c130000d0000b10c0025417074000010d02c005fc6d04c0b034000002b184e90d4130000002c0000000,
    0x13254000000d02c4305c00000250000025cfb0d40b2241700011034c7194c100025034111c40b0743d19d6f04c002cc0003400000000bc000455b,
    0x444f0001702ce5000131240b000df00000000000ac00000001fc0007c0d02c170001d3a551044000000002c2b07c6b13c0b0740d00000001010003b,
    0x340004c00274250000b0001105c0002c0045429000000340004c0b12400000111640004c0d000000442943c0d02c000003525c1707c000000022c0d,
    0x1fc25044000741703429000bf02c115bc000ac0004c003c4b31c453001010340b0a4006140b00133000110003b19cb50f40041d3d000000740b28c00,
    0xb0ac000440043c0d00167000000448311c43000250000d000890000034c0d0740b0003b3bc6502c0000000574130d41f0000002c0052c000000b,
    0x2c1f584f114c0b05c5900029000000000d0940b184132fc0002c000f400000003ec17044000340010c131ac00034172540046c0004c000001f02c25,
    0x4dc1d02c130000000011000710bca7000350343d000b502c6d0ac1f02c000000003400074130bc0d000e3314e50000b04c005ec000000d05c2500000,
    0xd0000000000000fb0342b5440b0ec1f28c00044001fc00034000006114c0002c1f05c0022c111ac0004c0b0740d0001102c00434000340000000,
    0x340004c9d0000002c00044490000b05c6d000000ac1d000290000b05c0020c3d164b50006b0340014c0059c0002c250442f0000b1240005c13,
    0x4c000955b0000014c2b0000d000000d46d0740d02c0000011000000000007c2f000000000002c970a400044000000007d3d05c0b19c130000d0003d]⟩,
  ⟨157906, 1106, 186, [
    0x4c000955b0000014c2b0000d000000d46d0740d02c0000011000000000007c2f000000000002c970a400044000000007d3d05c0b19c130000d0003d,
    0x94001640b00000125010bd85034970f41302c1741c534540b0441334cf10a40005c0d02c1f000000000b1841113c000000d000001941102c0003400,
    0x5c000001d0340002c1f2d4131b4174e42f0443b0340b04c000000d000c10ac00000001ac000940b22c0d0007f04461000ef000001c41d04c1100151,
    0x194490013702c130000011c0b3940d0742b04c115840d0010f000000440002c4f1fc0037c0004c430009502c495d4830440b07c004cc000000009400,
    0x2b5fc1f0000d0000b0000004cc702c00254000001107c000740b0342f04459094000349d30400464000d41302c0000000034a7094170002f18411,
    0x19c1138c651b4430002f0001f02c00000bf3a41d0000004453000d304c0d0ec0b044000a40b00013000350004300000574470000d000000000b00029,
    0x340b05c110000000000184350017503417000003140003413094b30001d13c000000b07c0d0000002c8b05c0d094002b4290000002c97000130ec0b,
    0x2c00000000000b034000004300000184000000b000000000002cbf000130340000049000170a41d29c0007c00000470bc3b04c000007f0441d02c00,
    0x740002c0005c000440d0d4650001313c1d4e4000000002c0d0001102c6b0000d07d513c411000250d400000170ac0b20c000003d0342f0000004400,
    0x44b307c6711c8904c00074000000b0940d000130000046c0028d15634112b56702c3b094000340004c000000b034004050702c130000010c0007cef,
    0x10c130010d000000a40002c110002f0000b0342b05c1d00000000001840b00011034000001d14c0d044000004f04c4902c003a4000000b0a46d00017]⟩,
  ⟨160199, 1107, 187, [
    0x10c130010d000000a40002c110002f0000b0342b05c1d00000000001840b00011034000001d14c0d044000004f04c4902c003a4000000b0a46d00017,
    0xd044000acdf09413034951c4110000007d0702cb30f400034170002504c1d000000000002c0005c113bc290bc0d224bf0000b0ec2b034000004f,
    0x2fc000340b0441f07417001370ec000445302ca3000650000b04c003944f000000001102c00464000340b0013d5bc3d035150006d164a702c000001f,
    0x52c170003b0bc0002c004940d0001f584110000d04c0b0946b34cc100017000130bc00044002740b0001725c00254293ec6d0001d000000000d00000,
    0xd02cb50001105c0b0342b04c970002507c591ac17194000740002c3b0000d000291fc000000002cc7000110000b0015b001010000003400,
    0x11c000a417034350000b044670000002d6f00083034130743b0000b13c000001710c00000c10741111c0d3c41f02c005ec110006104c53000b300000,
    0x130000029c3d0ace902c0d38c29000001ac0d6140005d010010f0000b124000d40b1649d59c6d034000000004c1d04417000252b40b0002b,
    0xb0bcc507c0d0002504c000004f0008946c6b00139000113c400034000bc9504c0b0344311ca302c3b0440000000164710340002c00634000000b,
    0x2c000743504c0b000000017b07c0019c000000b074430010d02c000000d574000ac6500000000b50013d0a4110001f000830000d05c110000002c13,
    0x340002c000000005c0000000314000346b0441f0000002cd30003b02c0007400000170000d00000000430ac0d0440b41c3d0000000013000113040d,
    0xd42b000c10348b274000000b56c1319c110ed330a400000130442b0340002c001fd191943d074000000b000000441302c000011505cb511c00,
    0x28c350008325c000000d02c130a40007c0b000000001104c0d0004f0bc0b0440d0001d05c250000000000000000ec4302c17074000340b04c0000011]⟩,
  ⟨162545, 1108, 190, [
    0x28c350008325c000000d02c130a40007c0b000000001104c0d0004f0bc0b0440d0001d05c250000000000000000ec4302c17074000340b04c0000011,
    0x14c11224000ec130bc000001d0006b0000d04c0002c00044000a4001b4df05c43044000000002c1f2744f1641d034534948b0ac0b000bf0940005c00,
    0xb07400000000f41704c000a40002c000006734c0b4cc0007cb509400034e502c2b25c0d0000b0001307c000017f05c250440d02c0046400,
    0x7c0d3bc290001102c000344900000001911c4170000b0002b0357504c000000005c0010c610000b2b4000010f0000d094000002907c000340056c00,
    0x5c000340002c00044000000b46c170003b000e920c0031c13000110000002c3511c1338c11000170341d02c25000000340b3ed5d000000001304400,
    0x441d0000020c2f1c40b5fc0d0000002c0041c0d094170014b59c0b164110d4290000007400044000010d0ec0002d6f1241f04c47000290000d13c00,
    0x29c1f1c40d0003d000000001102c1305c251b55125c1f0000019cfb31c0011c0b0000d0000b4f42f0440000000074005840d18400000171940b03400,
    0x1840b044000346b04d0d0a40022c111b400000130340005c1d0000d0003546c005740b000000000002c0d1240010ca3000000001302d75000000740b,
    0x2c1305c610440b00000000002740d044170740b0000d0002902c670ac003bc2522411000000000014c000340004c00000c5000000ac3b0001702c65,
    0x2c2f2b40d000131b4000f4290ac110000056c8302c1f4dc1d02c0004c0000000034170002b00000000950000b11c000344314c713040000000,
    0x43c2504c1d05c651b411000000000b001070000034c000005904c350000d07c0002c0004c3d3c43b13c9d1fc0b4041107ca702c0d0001d46449314df,
    0x34000000052c0028c6502c000ac000340b0bc0004425034000003d0000b1fc130ec000000d05c113ec000000d11d8d02c11394002cc0b07c0010c0d,
    0x1b561000000341d000000440004c000940002c000002f07537000290340019c000008902c001c4004540005c135bc000440b00095000000d417]⟩,
  ⟨164930, 1110, 201, [
    0x1b561000000341d000000440004c000940002c000002f07537000290340019c000008902c001c4004540005c135bc000440b00095000000d417,
    0x1642f0000b1fc000f40d2fcc5000650000002c1d000130000b43c17000950000d0000002c000000005c0b0444741cad0000007c000348b02c250bc00,
    0xa73c4130000002c17094000009d0000d000d30ac0b07c47045392cc1d000000a4670bc130340b00000000110340004c00614005741113c000006b,
    0x31c170000002c1d0017b04c0b000e900000034c5000001243d46d0d10c1702c2b034000ec000000d3bc1702c00044e30000b494000000d0d41100000,
    0x740d0940004c000000b0342910c0002c1d0ac11194001c4170340b04400000000000007cdf2544f124895840002c0d044000000000035034001b413,
    0x4c0003417000c7001850745302c005d40012400000111943507c7f4e4000440b2fc000000b0f4000342507c00000000340000083000130bc0b00011,
    0x6440b0000000000000000000d05c711fc1310c0d11c1d0440005c130003d3ec000440b0001d0940002c00000000003b000132b41102c001ac0d0000b,
    0x2c0007c0d0000b0007100013034002d4a722c0b0000004c9702c29544000001d5ec0d0000007c470bc002fd670001d0000d0a4000443d04c0002c00,
    0x2c00034110744f07c2b000590000004c000340002c950000d02c6512400094000ac0004c000a40d0003d0000b454530000005c000440000061,
    0xf4c10000000000044613c40004c0b0000007cc70000d0ac4f0ec11094890a40002c1700011000b343c670340b00017000a302c1d0bc000000004400,
    0x4400000bf0000d0002b02c000746137c0b0016f0a43500000094430340b00097404000347f04413000001b49d0940002c000343b0000b05c003941f,
    0x970000013ce30ec110bc1f274000008b02c000741331c004940d000114641305c8302c530440009467434002d4170000b13cad1c4130a561]⟩,
  ⟨167362, 1111, 200, [
    0x970000013ce30ec110bc1f274000008b02c000741331c004940d000114641305c8302c530440009467434002d4170000b13cad1c4130a561,
    0x343b0440b4040025575000001fc110340002c0007ce90340b0000052c1305c004f4ef02c0d000250f40b28c0d0a4001ac1d04c000000002d7f05c0d,
    0x544000440002c0000017000130442b14c353ec0b30400000000003b0343d00011094000000b194000741f000000003505c2f00043000c504c1d,
    0x37c2b0740002c0004c0d0000b25c471241116413074000000d0002b0000002c0d05c00044000000004c0002c000000019c0b000130356729c3d1247f,
    0x5c130000007c000940b0bc3d0001702c0d5fc000008b13c000000b000250753d304001842f0341707c530006b02c110d46700000000000000000043,
    0xac0028c250a533000130444702c0034c2f034000441700000000000a46d04c0b0347f0000b4340d0740010d070001f00011000494540d14c0b3ec00,
    0xb04c00000002cc00035010440005c350001f14c0009400034710016756c470000b04c000008902c6b000590000d000000446702c170350f46c0b,
    0x2c59034494340b07ca752c1d000e5454000f40b04c0005c1102c950002f28c130000000000000e30357b0441d0ac000340000000634b50a42f02c3b,
    0x8902c00075250ac2f0000d1640004c170000d0000002c000440002c47464000000000000000000003d05c112740b00000000c125c110740d000f1,
    0x8b1840d0004f11c0014c000340b0bc9d0442b1b4130000000000000000000002c0d000171ac1f000130000b044000000d02c4f04c2519c1103400,
    0xec130358d1842502c00000000000b0001103400000000000d0440b164000000000013000000000d0001707c2902c00094000000b0006731c49,
    0x7c1d19471094470000004c002540d000000012502c0d2b4836642f000000440004c000742902c590ac000340043c250f4000000b07c2f0000057411]⟩,
  ⟨169847, 1112, 195, [
    0x7c1d19471094470000004c002540d000000012502c0d2b4836642f000000440004c000742902c590ac000340043c250f4000000b07c2f0000057411,
    0x1c4110a40b04c0d22483000ef0001d3a40002c7f05cbf0440b000000357537c000449702c00000000000b0000005c0014c00034110004902c3b00013,
    0x4c00000110007f02c0038d0f0002b0ec29000b35bc0b0001d10c170f40d000490006b0018559c0b05c000d400000000001f0000d044130000007467,
    0x341f000ad02c11000171940b0d400034130743d4cc1f03400000130017b02c00000000000d000003943502c0d0bc9d05c0b4051b0a4000441f0000d,
    0xec170000013c6d0340b0ac1334d5102c002d4004557f04c001640b00017034611ac000001120c00000170a4a302c00314001c4000019104c000442b,
    0x440014c1d0bc130000d05ca302c891941f04c0013c0011c0d00000464110940b0bc1f0000b04400000bf000001c4004dc0014c250341d0000b25400,
    0xb0001719c8b000000d41104d070740d1943b000490a41f000001fc00000110ac0b29c000340002c0052c1303400074000000002cb3614000ac0b,
    0x2cc50444f6440b37c1d0003b05c110f4000340b000470002502c0004c0007c0003400000711240d000110ac250000007c9738c172fc0d2240002c00,
    0xd02c2b044172b40003400000000440056c1d0940002c130346b02c2b000f1000113ec1f0003510c00000000000b464610bc0000083034130006d,
    0x3400000533941f314000000b0a411000471656f0000029c8b000130bc0002c4f044000d4830340041c0b000000356102c0005c000000049447,
    0x22461000293bc1d05c1102c0d000132fc0b0000d0003d3a4711ac000000b4040028c17000004e41d00000000000001102c4f07c290000b1b40d04cc1,
    0x757f0000d0000004c0004400034000001d11c1302c0007cb50000005c4325c250000d0002b02c1104c000bc0046cb35440d0000b0000005c0003400,
    0x134040b034250ec000741f044000000002c00034000bc0b4540d0001f000290000002c350000031c0b4340004c590ac170440037c2902c0000000]⟩,
  ⟨172381, 1114, 216, [
    0x134040b034250ec000741f044000000002c00034000bc0b4540d0001f000290000002c350000031c0b4340004c590ac170440037c2902c0000000,
    0x2513d1b0003502c13000ad0000d0006105cc10000b00011314000bc8b04c000002b07c1d5740b0000003400000001b4fb5bc000000020c4705c00,
    0x1240004c0002c0d0bc000a40b000001643d000000002500000044000340002c1d000000340029d7b0010702c113941d0000b0343d000114dc4300000,
    0xa40029c000d4000740b0009738c0002d750441704c000002920c0b3040d0001305c53000000004356c000000002c00000000000d0ec47000112d425,
    0x344f07c3500000000d320c0002c1703467000112742f0340000000044001840b0f4000000b07c172cc2b0000d46413044000001d31c000000b07c0d,
    0xbc0b0003b000430351507c0007449000001ac003c4110f40000000074000348b0000b000001b40002c133a44300000614000000002c00124710000b,
    0x2c110d4130000b34c0d2248b6340005c0007c0b000000440d02c00000000000d0440000013074290010f4cc6528c3d04c2500011034170000002cc7,
    0x5743502c110001f1240004c43000a31ac0d0000019c9d02c3b0000002c290000004c6d000530342f20d3904c000340b3041d11c0004400000000001f,
    0x940005c0004c1100000544000ac0b00017034292553d000df00000000004541f02c002b4003ec0d0002505c0b2d4000006502d6f0000d0441766413,
    0x4c0d07400000000442902d0731c0014c0b000000740019c00034110000b000000a40000011094000003b000490000d02c47274650740b0340004400,
    0x44e50342f05d7f59c3d5d46b0008b000130000002c0058467634130001107400000000005902c00034ef38c1700000034130000b00000254000951b,
    0x1993a40b000a7000001ac0d000000004f02c0d0ac0004c0b1b43b1c400000110940002c0005c490440b0002b16447000000001f0940002c0d00125,
    0xd4000440d07c1302cdf00061034110000004c0005c0b0018500000094000d42b0000d0000004c0b07c110011905c000a40d0749d000000000003417]⟩,
  ⟨174961, 1115, 214, [
    0xd4000440d07c1302cdf00061034110000004c0005c0b0018500000094000d42b0000d0000004c0b07c110011905c000a40d0749d000000000003417,
    0x650000002c001ac000000b04c00044000ac000346d0002f0940d0000002ca7000112d400224ad05c0d02c130941f52c0b000000010d0000000000,
    0x2f0ac3d074000000b10c830000d02c113141f0000d000e30000b04c3514c0000000045750ec13000000340002c0005c000a4000001f074000bc35,
    0x1711c000000d07c111c40002c00000000a4000010d40413184a3034170000b074130340b0ac250a41714c00000110000003400000001fc0b4cd91,
    0xb2fc6b34d3714c00044000017b07c000000004400274170ad5b0000d0a4000000b094e952c1102c1d000b3000490001104c0d02c000f40020c0b,
    0x2c1d1ac173ec0b000000f425044130343b4f40b0a4530351902c350000039417000610740d5841f41c470000d0000000095044f1000a30000002c0d,
    0x2cd300000034596440005c1d0008b1fc130004302c1105c0002c250340031400000001840004c49044a70740b00000000130011b0bc000a459,
    0x7c1300025000170000d41c0020c0b00065000492cc0025c0d04400000000000d02c2f3bd250000011c430000b04c0043c0002c00034110000007400,
    0x1ac000006d000000001302c000010d13c0b0446500000094002fc004040b04c00000000a449034c50bc1f464000340002c000f40005c0b0001100029,
    0x4d8d0003d05ce5000000010f28c000341102c3b0005304c1d044000ad750341704c0002c0d0015d00000000170441f0000b2740d0ac9700000,
    0x1b40d34c0b0000000095034000003b0002b02c0004c110000b0340005c00044131240002c670a47f0000b1c44f0000d4e400000000bc1d02c1f00011,
    0x5ec11034000a46102c494cc000940004d85000000000b044000001f0a4000011b0440005c470000b03400000e32b4130341756c1100025000c70f42f,
    0xd30001102c000001d0000b0bcb30001f05c0d0001300035075670004f02c000ec1f10c000bc674541302c00000000000b09400044c50000d05c00,
    0xac001240d094110a40b000170353702c000001d000000001f3040b000711957f2d40d000130008b19c00000e902c2504c0d05c000d4890440003400]⟩,
  ⟨177578, 1117, 215, [
    0xac001240d094110a40b000170353702c000001d000000001f3040b000711957f2d40d000130008b19c00000e902c2504c0d05c000d4890440003400,
    0x4343c0003400044c704c0002c004cc000ec17034000d4000000d2b41d07c0b04c002240b14c003c40d04c293bca707d1b0ec2f1b46b11c0b04400,
    0x440b5740004c1d404bf0000029c0d494df000001c40d0017b38c0013c110002f0000b0001f0441702c00034000ac000007f1b45302c9d07c1d0000b,
    0x2c00000002d40b0ac1f0bc110000031c1d0000b000170000002c000346100011434000342500000044000f49710c29000590343511c135440002da3,
    0x9502c00000b33ec00074000001105c130002b0003502c000001302c0d0018d11c00000290006500011000c11b40b0001307c0d5bc170940000089,
    0x34000a41f0447100000000135840b03459000000d41d0343d39525000000940002c110000d00000000006440b19c000000002c251242b04c000000d,
    0x68c0005c003a4130340002c1f000000000b04c000000000000274000000b0341d2b5990456704c000ad5105c000001d02c00001390000b0001700000,
    0x89000290740d0013d04d7f000000003502c000000d000c7000000000d0000007c1702c6d000000001319411124350000b034000000010c00,
    0xb05c0000000044000002b0bc0d02c00044000000b07c4f04c3d0000014c0002c6d034110000b07c17034f1000110001d2b40002d5b3bc00,
    0x34c00394000000002d075ec0004400000250350f4dc0b000130ec000740000000034130000005c0b0004f12453224950bc00044001640d2d41318497,
    0xd07c0002c00000000340b13c2529ca30d40005c00074110342f4cc1302c000002500000074006640002c3d05c0d1c40b04c3b1942f0340007c17,
    0xf4bf03400000000000b07c000a41302c352cc000005914cc10440b10c001b4250017f000003a519034001ac1102c000341d4340019c110009d04da5,
    0x1943b001915742504c170000d02c2f184000440d001014dcef0a425585150000b0ac000000b1c4a704c000748b0440005c0000013000670000b0ac1d]⟩,
  ⟨180251, 1118, 233, [
    0x1943b001915742504c170000d02c2f184000440d001014dcef0a425585150000b0ac000000b1c4a704c000748b0440005c0000013000670000b0ac1d,
    0x14c0b0740d4941f0000028c4f034000a40043411074000000022d8504417000002540b00000164df02c170ac4704c530440d0008902c000007f0340b,
    0x2c00000290340b41c1305c000001f0d40010c0b034110001702c0d0002b0441f000fb000000006b0f40d000b5000001640012429000000000002c11,
    0x1102c170bc5900000634000000d224000940007c0d02c0004c4902c00000170440004ca310c0007400034350000b0ec0045411000f14e40000025,
    0x19c00000110000d4f4002cc2f05c0b000000006d04c7110c0005c00034000001302c1d0346b2b4000ec000000b22c0025c0002c17044290002500083,
    0x2b4530000000011000c502c1d5d43504c0b38c000002912400000000000b000000010f1ac2b46c00000000001d0f41302c000000d29c0b0440022400,
    0x34000000007400044000a471000000357f0000002c130342b0001100000000a3000000000d02c0007c130d40d000000ac250bc0b04d6f075390440d,
    0x44000940b000000340013c0007c0020d4b02cf1224000000b0000000011034000741702c13044470000b164002fc1704c43000951fc0002c0000000,
    0x9585000670000002c0d04c1130429000000f41f0000b0000d13c0005c970000d04d15000000000b0441d04c3b3a40022c00000610341f05c0059d0f,
    0x1d0440002c0007c001640b124110000d3bc0000065000c50000022d3702c000000005c3b034000001102c00034000000b2d40014c430002b00013,
    0x4c002b400044002fc0b0d4000001d02c4703400000000bd610000b0000005c0003411001070000d0d42b4940002c000002f000000000d13c0005d99,
    0xd000000000019c000341702c000001100000000000ec1d034130ac2920c0b094000440b0001f00000000000000d0001305ca3094000340b07443,
    0xb03443001010bc1125c130003d0ad19074173a58504c001246507c000000005c0b001910002b02c2910c0007c11034000000002c0004cd30000b,
    0x2c000f53d0000b000290440d000170000004c0b044000000002c1d0000022c000a4470000004c110000000000094e5000110013307c4f5bc0d02c00]⟩,
  ⟨182967, 1119, 220, [
    0x2c000f53d0000b000290440d000170000004c0b044000000002c1d0000022c000a4470000004c110000000000094e5000110013307c4f5bc0d02c00,
    0xeda302c0d165670d400000670344700000000001241702c610000002c0031c001940d000fb000712d41f094130000b10c0d044000001d37c5903400,
    0xbc00000000355b494000002928c0b05c000003d03495000111fc0d04c9d2240002c654640013c130000d0440b0002b0741f02c00000170006d2cd39,
    0x1f4f4000002f3c41d02c472240d0940b0003b0000d05c13044ef38c0b1c4830001309435001152fc000341114cdf02c003048b10c0b34c1312400,
    0x1fc0005c000000d00000000256640019c170441d02c001ac4f0001f034130004722c3d0346102c2f0000005c2b044000014b0340b31400434110009d,
    0x18d68c0b0002b0940046c00000130001f02c1110d250000b25c290440d2542b2cc1f02c17000000000b31c00000000446d0a40d000d302c0004c3d,
    0x340010c2505c1d02c003040000000034710a4131ac0b0341f0bc00000470457b000a70000d0000b04c000000d1847f56cad1641313c000001d6940d,
    0x74110ac2f02c000355d2b40b1c4004641d2246b000000440010c000000002c000440041c0005c000000002c6d04c0007c0b1841122c00001850ed75,
    0x18400000114cc000000b07400000bf02c000002505c001fc0d0000b46c0004c0d000350001f0ac000006d0000002c001943b00000034ef07c0000017,
    0x7104c61000110ec1f0000002c002540d0bd010001d000a704c170000010c0b0000004c0b0340005c00000000350d000000000034c000440b0a4a3,
    0xb3ec0000000044170002b094003c4000340004c0013c2f2cc110000043c130340b0ac110000d02c00000000a41d05d5107c0002c0d001a50440b,
    0x2c0d0001f0000b07425034000000004c000000b2d40007c0002c00000110009d000000a44f044004dc17001150000d29d5d09400394000340002c29,
    0x4f40002c000940031c2b05c110006b0000014c430001302c170000002c1f000110d4000bc00000c1034132cc7f0000b0342959c1d04c491640000000,
    0x470441346d150000037c0d0740b0003d0000d28c000000019c000758d3141702c0007c130a40010c110000b0000004c7102c3d000000000d00065]⟩,
  ⟨185727, 1121, 229, [
    0x470441346d150000037c0d0740b0003d0000d28c000000019c000758d3141702c0007c130a40010c110000b0000004c7102c3d000000000d00065,
    0xd044000000002c00034000440b20c00001910740005c610a40b0ac3504c0d000a7074000945304c710009702c0d000175d40b0ad6f03495,
    0xd4df0000003417000000000000119000110000002d0f0017f0000d000000d43b07c950442502cf10000d00000000003a41d0000b2d4000bc0022c13,
    0x4c2b07c0b4e50d0a411000000000d0000002c0014c0d0f40b0002b19c4338d990002f02c8b07c001640b0340000011000000000005c1302cad07c1d,
    0x740068c0d02cc10440000161000132b5330440b0000000013034350947127417034000000b0bd8d00029000173bc11034250747f25c0000035,
    0xac3d0000002c6b1643b0000b044650000007c470bce304c000000005c0d02c6700029000001240028c3b02c00000000940b0440d3ec0004c0000047,
    0x340052d071ac130000b14d510000002c0004c950004f034110000b0007f0000019c0005c0d04c00074000440d02c290001729c000bc00000430000d,
    0x314830017b0000003400000b302c1f1b47f05c00094000013304435000000340b0001d0000b22c43000002d4110ad3737c00074000f4111840b05c2f,
    0x46c0b0a50113c000ac0d124170bc003bc250440007c000000d0000004cbf0000d0000b25c000bc1302c000001d044000000005d6102c00000115bc0b,
    0x2c00000000740b1c4611b400000250000d0000b13cad1941302c00044b30000005c1349400034c737d910001f034000440000000001a50741302cb5,
    0x5c5902ca70ac291b400001190001700000034000001102c000000002c13044250340043c000ec0d00000000000000b000d304c1f0a40d0003500011,
    0xd2744f07c250018d034431640b31400000000001704449034253c4000002f02c00000001fc0007c1d0a40b0000d3943d02c11000470340004c00,
    0x1241d03411001a304d3902c0007c0005c0b25c130000018400000000000b00000000000742f19c3d034003ec000001f02c002fc130440b0d4290006b,
    0x1314c0000011000000000d11c1d0002f0000d02c2505c006bc0000000165190004f000e502c00000e90000004c000000014c0b6441f0440d00000]⟩,
  ⟨188543, 1122, 235, [
    0x1314c0000011000000000d11c1d0002f0000d02c2505c006bc0000000165190004f000e502c00000e90000004c000000014c0b6441f0440d00000,
    0x10c0005c0b000000441300000034000001702c000f4002cc0b000110000004c000000d02c11000590000b05c000000034c0d25d0d0000002c1703425,
    0x440004c000340002c000ac000004907c000744f0340b0000004c0d14c11000000000004c170440b5d40d00000000002540011d7b0d53d124250002b,
    0x41cc702c890002f0940b0000d0a5150008304c0d0d4000001d0000002c1138c9d52d330001f0458502c17000d30000b000003c5371ac001b400,
    0x441d0000d1240b000000001102cc1001af0003b2d4bf0000b03400000000ac00034c505c001941129c6702c135fc25034296941d46cfb0ac00,
    0x7c0009400044000000010c0002c3b044004045305c1338c7f1656f0000d0000b25c110000b00000000130ac0005c00074000f40d04c000000b00017,
    0x340b37c130003d0001d000000011b034110000059c3503400074170002b0002910c0b0440d2d43b02c1f0000d0004704c830d46b02c29001994dc0b,
    0x2c4f184002740b0341104c89000006450f31c0b0d4291c40002c00000000340004c8300000094000000004c0034c1105c1f00000000000000002c00,
    0x4541702c0004c001840d045b14e42f00000000000441f02c0d0000002c170000d00000304430001100017000000000b000110ac00034000001f09413,
    0x4ce356c830001d0015105c000440b0000d0ec3500043000170001f000000000002d7528c2b0341d000951b40b034001ac3502c00094130001d29c00,
    0x74a311c17000000007102c00000290000b034001640000011000130940b000170341f0003d4940d1b443044000004f02c132cc670000b59cbf000c5,
    0xd000000bc0068cb30341305d390008913cef02c7f04c1f0343d2d4595fcad0bc2b0ec0002c0000000394110940d0d4004f40b000110340019400,
    0x340b000131fd4b0002f14c000000002c000001d0000b000000ec4907c0013c0002c1d04c290340b0946b04435034004cc0038c0002c1100053,
    0x10d194003049d02d9929c0d04c00000350000d20c0b3ece900000044290001d3940031c1f0000b000000f4130001d044000012505c0007c0d40471]⟩,
  ⟨191414, 1123, 231, [
    0x10d194003049d02d9929c0d04c00000350000d20c0b3ece900000044290001d3940031c1f0000b000000f4130001d044000012505c0007c0d40471,
    0x11c004dc0d02c0005c1f0000b034ad0944f0002900011000000000004c0002c000000d094530001311c2902c000d4170000b0bc00000971c46703411,
    0x110bc000343b1940b3a4250000002c000000003400044130000b05c6d0bc000441310c00000000000d1fc0002c000000007c110ad5d05c1300000,
    0x6bc0022411454000948b1940002c0d0ac00000490000d07c005ed19074131fc0b41cad05c0b11c2b000000346113c000001704da5044000000b0014b,
    0x4cc0b000250000d000003941f000136640005c0000000074000ec530341f05c000000b03449074bf02c000bc3500000000610340002c000440004c0b,
    0x2c00000001fc0b04400000170ac001952528c0b000830940002c110000d0004f0000007c110000004c5900000000000a41d05c0d614000000002c00,
    0x341302c0014c0010d5b0ec0000035034ad194171b40002c0007c0002c110015105cc10000d04400000000740d04c0b000f1000590003d31c0011c0d,
    0x5c3b07533000000341322c113ec0b00139000000740043c0000029000000341102c00404b300017044000d40b0013d0000002cb5074005d400000e5,
    0xf4000440019d192d40d02cdf094110000b0a4590ac170000d04d8d0000b0740d0006b04c0007c000a41125c2b0000002db120c430340b11c0007c00,
    0x13d1b124e30442b2742507c352fc6d0440d0000002c2f000000f47f000000a4130001120c0002c000740014c000342f000000940b000172cc9500000,
    0xbc000000b0940014c004dc005ec0004c1102c000a40005c0b0000000000000950341d02c590000d0000b000004f4130ec00074c511c0d02cef10c00,
    0xd05ca30001f02c110341d22c0000017000002b40b0000003400194000006b11c00000000000b0d41305c1d1640d434000000004c00034170a41f,
    0x341302c6d0009d0440b0001f000490000004400000433ed996140002c1f52c00584130ac110350102c4f0a5af0340b00047000000755d00000,
    0x1c400000e905cc50000b04c0d044c102c000000d07c00000000ac0b1ad6f11d0704c000a425000352540004c1702c000000004483000005fc0d37c29,
    0xd04c000003568c2b02c00000000000000000000110bc6b10c4f0000b4540d0ac0b05c6134c1d0441f0f4002cc0d00000125250940b03413]⟩,
  ⟨194333, 1125, 250, [
    0xd04c000003568c2b02c00000000000000000000110bc6b10c4f0000b4540d0ac0b05c6134c1d0441f0f4002cc0d00000125250940b03413,
    0x4c0b0002f034000d4000000010c670000000089034000ac530440d11c00094001640b074000a51b02c0d0001105c00000df0001f02c11000000000b,
    0x2c000ed1907c0b0002b000001fc0d4dc130440b4e40d000ad02c130a40000000001b114c3b0000005c000340004400094131c4e9544000001102c6d,
    0x10f02c003940d000170001307c00000000bc11644f102c1d2540002c00000b500000034350009d00065000251c40b04400034001848b04c000756f,
    0x2541700000000130a459000000000b0006704c1f094110ec2f000000000d0440002c000000004cd329c171240b11c000000002c0d0001f0a43b00011,
    0x34110000029c0007c0002c0004c4f0340b4dca3000000341711c1d3140b00000044df0d40d31c00544c14f40d000b502da5000110000b000000bc0d,
    0x41c2b000110d40003400000610002507db72fc6702c6b20c003a42b04c0003417000250bd7f02c13000000004700000000650000b0441d0000000000,
    0xec000000b000110000d2740005c3d0740002c0019c005ec0b05c43000000000d0001302c000001f0000b13c0025c2907400000170340002c1300000,
    0xac000f4000001702c1d001a33a4000000d0000025c0b4e4710741107c130016149435000110340b0000011c00034890002b04cfb000004040004400,
    0x44250a40002c00000000000b00013000ef0341d6340019c001844f0f41102c000351b0015b0440d2740002c95000002b40b124c705c0d0bc6504c00,
    0xd000000000004c0b034110000002c290001300025000670340b6bc1d0001100017000b52fca30441f0000002c0d000000001300043034001fd0d,
    0x3bc13034000001d0ac000000002c111ac000940011c00001390009705c000000b4cc610000b1b41d034110012504c000341f314000a45305c0b38c25,
    0x740b000fb0440020c130000d68c000441d0000d0bc1f12400000000000004c590d40b05cd31844702c000a40000000000170000002c950000d0000b,
    0x2c0004c0d0ac0b29d670749d034000001105c0b001154640002c1f0009505c0014c0d04400001851240010c00000006940d000000bc2b0002902c3d,
    0x28d5102c000347f0001131c176c4000f41f1255d0341d02c000000d02d07000131b41f5d41d0013d0ac0d0005352c0b1842505cad20c000000013c2f]⟩,
  ⟨197302, 1126, 241, [
    0x28d5102c000347f0001131c176c4000f41f1255d0341d02c000000d02d07000131b41f5d41d0013d0ac0d0005352c0b1842505cad20c000000013c2f,
    0xd400094000f4000ec97044bf0a40b04c47000170440d0001f000b3000670d41d02d01000e30bc11000000340b0001310c1102c2b000006dc710008b,
    0x5c00000000000d0750f02c00044170000b000000001314c830a46d0340b07c000003b034002541730413000000000002c000347104c0b0000000000,
    0x17500013000611ac8300000000000a4650000002c172fc111b4e30000d12400000f10001302c895fc9704400635a504c000000b10c0007c4f00035,
    0x34b36440b000000001f04c00074000340002c65000c50340b04400074000002f04c4702c0d000000000b04c0d0005300000000290ec1102c000940d,
    0x304890000004ce902c000bc000ec47000f10440010c0b05c001240041c0003400094000f42f0740b13d5b0000004400000e507c00094002b41100013,
    0x4c0005c1f02c000000d13c0b001a36141700011184b307c0d14c35044c702c0d0ac000013d20c00404df02d0d29d1b0440b0000003413000170ac00,
    0x1ac006640038c0b0001f0000002c0d000001241122c970940b1c41f0443b0000019c1703400000000748902ca3000130003d000000000000011,
    0x110742b05c00000430a41302c9d0000003400074590443b000000002b0000b034d307c0b0000d000000941700000000001fc110740d04c0b0d400,
    0xa40b00011000132242f0346d000001240004d4b0000000029034e56ec00075370f40b4f4ef04c2502c0007c000000d000000000002c00034351240b,
    0x2c00034000000b2543b0000004c29094000000b05d5d0f40002cdf000470009707c0009400164670343b3141305d15034000ac0059c83044b302c17,
    0x2902c97000b5044001c40d0007f000e50000d000ef02c000001102cc1000000001d0001107c1305d61184006940b0bc0007449000000d40d04400,
    0x443d6bc0d000590941707c1d0340b000bf0004337c00000136442f000110000002c0d0006504429000002540b0006105c0d02c0014c2f4cc1303400,
    0x4941743425034470000002c11000890000b07c00034006dc350000d0000b000110002b00000304650440d19c001240002d0f04c000000b0740000119,
    0x1b400044000001f0000005c0025c0d000000002902c0d09417000bf0000000053074000000002c0000011034000ec001fca70000b0d4c70000004c1f]⟩,
  ⟨200318, 1128, 246, [
    0x1b400044000001f0000005c0025c0d000000002902c0d09417000bf0000000053074000000002c0000011034000ec001fca70000b0d4c70000004c1f,
    0xb0440d04c29000000001f0440002c13000fb0d40b00107034004e4170a41102c000ecb504c0b5ec000bd5b000b3034130000002c2b1c533,
    0x544130000037c8b02c531840005c00000110000007c0b0004f05c9528c0d0000034c00044000000b0002b1649d04cef000000000d4046b3945300049,
    0x34470000002c17614111fc0b0941d0340000000000000340020c000ac0002c000bc001240d00000001b102c0d074113c40b10c350ac25000b50000d,
    0x224a704c000017b0340b0442f0000002c3b000000443511c1d04c0b0015b034ef0004304c0063411000001c40002c000a4110941f05c490000007400,
    0x2fc000003d07c0005c0d0000002cc7000000751b04c0028c0d4948b000003c40b000170000b0003d07c000ec2f14c17000000454b034000000b00000,
    0xb0010f0000022d330005307c0004c0d0000000047574110001d05cb5000d35bc0b000000344302cb30440003413000490a40002c0005c000000b,
    0x2c000bc1d0000b000000000000000000000340b0f4134348902cc5000710bc00034e905d610000d09413000111b42b000176bc0004c0d0f40002d01,
    0x38c0d02c132244307c00034000000007400044471fc3b02c00034c102c0005c000000000013000000014b000430440b04dbb0000019c3b0341105c47,
    0x15d03465164000001d04c170000b07ca7464110a44900000074000448b6640002c974544f000000346104c0b1acad0345302c00000670945941c00,
    0x4c2b25cad02c0d000000000b0d40d000110bc00000000000b0442b05c00000c11241f0013728c000003502c2f000250000b3c40d0a411,
    0x4c110000d634003a4000000003417000350acb502c0004459001b107c1d000000440d0006d02c17000c5001af07d7f0940d0f40b000131fc8303400,
    0x7c000ac0b0341d0bc0022465000004341302c00034175440b0000d000d3000000000002cf10001d0000b1ac250d40000013000000440002c1d00029,
    0x7525000531841102d91124130000d05c1d0ec000940b04cfb000000013d0008b00000000000ac0b38c1f0353700167000290ec4f2cc170440000000,
    0x1640028c0002c0d0457f0740b000000d42504c0043c2f05c000ac110340002c000015b0341104c001ac0002c000002f0000b03400000473a50704400]⟩,
  ⟨203398, 1129, 250, [
    0x1640028c0002c0d0457f0740b000000d42504c0043c2f05c000ac110340002c000015b0341104c001ac0002c000002f0000b03400000473a50704400,
    0x441f05c7f0a4c13bc0b0002b04c2502c17274006c41d4cc000000b0a40d000e3000250ac1d0446b0000005c1302c00000970000d000bf0001700000,
    0x356f19cc52fc2f000b50001102c00035a30006100065034490001f04c0028c0b46c004e40b6dc13044530000d0001d0000013c000000029c0b20c0d,
    0x1240b0446705c250342b10c000001152c1f000000004f000130002500000034005840b0006b3942f02c11664170009d1c40031c0002c000a4130000b,
    0x2c25000000440b0000d11c003148b044000000b14c000000d02cd33a4130000d10c111ac0005c7f000000d4292cc3b0000004c1d034000000002c00,
    0x11502d5d13c3b0f40043ce3074130000d0006d05c2502c000bc6502c0007c006bc290453903400000350f4000340b07d3700000000ad0ac0004c17,
    0x31c2f0000004c11584350000b0002b0341313c890740000017000000000002c710001f0740d04c000000b000112744702c130000d07c0000025,
    0xd00175000000001702c00000590000b39400044430003d0342b0000b644001948b0002900011000006940004c0d02c1128c000000b03425001c1,
    0x434170344f0000012413094000440022c000bc0002c00164001c4000001704c00000650000002c00034170755118447034000440b00000000000001d,
    0xac0004c0b6c4e5000f105c0d000002d42902c0d0747107c0b04c83000001ac0059c0002c000f4b30000b0458d0000000025184000751902c0d00000,
    0x1842f0940d11c2902c000001f03400000006dc9d04c0b00000044000001f074130000d4cc001940b16400000110004314c0d37d010a41141c0003400,
    0x94000006102c00000350000b05c5304c00044ad0340029c0005c0d0003b02c435440007c000d5390740d02c00044130000b000174943d304116ec00,
    0x6d11cc1000170ac0b0007f0000d02c8b000112540d31c0007c0b04400000000001d0000009449000130343d02c000449d0740004d8500029000bf,
    0xf4fb000130000d454002fc1d02c00000001642b000110a40000000034000440b07c000340b000004cc0020c1d0014b04c890340005c000000b09411,
    0xb07cb5075b705c0004ca70a4000000019c00000000453d0f40031c0d000890440b37c3507c0002c4704ce500017194c514c0d02c2b0753707c0b,
    0x2c4346c1104c0b0000007c0061483034000000b000000346b02c0005c00000000742f0000d000000ac000000d1fc0000000000000450705c0002c0d]⟩,
  ⟨206545, 1130, 257, [
    0x2c4346c1104c0b0000007c0061483034000000b000000346b02c0005c00000000742f0000d000000ac000000d1fc0000000000000450705c0002c0d,
    0x4d5b02c95584110340000000000000a40007d0d2740002c000946102c490340028c0005c00000fb0bc1d000590940b0001743c2b1c4130446d3143b,
    0x1d000290d41f0440d000003bc0b0001305c000bc674f40d000110000005c0d02c000741100000000000940b10c4913c1302c2903489194000441f,
    0x459100035000536647f02c131641d0000b001a31ac0004cd35d4000000b0001f000002240003425000000003b0340002c0005c6d0bc0b04c3d00000,
    0xecad00013000000ac1146443095670341702c9d0001d29c0020d4b6ec11034350943b02c0d044492fc000f4000006d0000b0000d000000742b,
    0x5c0d0440b00000000000342504c110000002c4922c290000b0340000000164000016f02c470bc170000b4e4130000d0000000000000b502c7f3a400,
    0x35034000446502c000a50d001150446b13cc50000b0ec0019c1d04c251c4000ac11000490000b034000006d00000034952741f001510003b0ac89,
    0xa5370001d02cdf000650000b0000005c110f40d52c0034c130015d0000002c7f13c13045013bc0007c6d02c00000000000b0002f304171840d14c00,
    0x31cc10000d0010f0000b000000342902c006ec004f40005c430000b000130002f0d40d0017b000006943d001b702c110740d04d670000011c0003461,
    0xec2905c89034002b41d0440002c13000170001f034003bc000740d19c833a40b000530000b29c110000d05c0028c00000110009d7041f0000b04c00,
    0xb29cf14dcc704c00000000440d0002f000130000d25c001640010c00000350000b000170002902c000340000000000000441302c00001250000b,
    0x2c131240005c0b56c95000000943d07d1b3a40b68d990001102c000341d0d46711c590342b00000000000441704c000f400034001fc250000002c53,
    0x7102c000001d000134643b0000000000000291940002c2b0440002c0d04c6d19ce30000005c1d1fc2922c110000b0ac000940d000110001d45483,
    0x340004c000940000029000000000b0341d0440005cd30348b04c0007c3511c4f02c2b04c0d00000000fb0000b044250000002c00000b3000110000d,
    0x7c0025c00000000340002cad2cc000bc0b0001104c2b00000000170440b03413304670000010c0005c00000004e40002cef0000007c0b0000043c00,
    0x7f000005bc6b4cc0d000290000004d5129cfb02c1110c0d0000011cf10440d000001841d02c000941f000000001305c000000b035af0002b0ec11]⟩,
  ⟨209739, 1132, 267, [
    0x7f000005bc6b4cc0d000290000004d5129cfb02c1110c0d0000011cf10440d000001841d02c000941f000000001305c000000b035af0002b0ec11,
    0x20c116340b1ac0000000000490000038c0d02c00000130440b31c2f0001713c1d0443d02c25035a51840b0008b0341d0a41f3a41104c2f02cc500000,
    0x13c1f314110000002c0005cf1000002253d034007040b41c1722c430ad5d0000003400000130000b00000000710013904c006ec000440d0941f4343d,
    0xd0001702c11000000340b0002f0ad611b57f00000000000341f000df02c1704c3b59c0019c2b0000002c0011c0d1240b0a41d27400034000d400,
    0x340004c000440b0011b05c0002c1f0a4d3001b10009d05c0b0740020c000001f1941100000034000009702d7b0340000017000610003504413,
    0x44001840000017001190000d02c001658d0000d000bf0741f0d400000110a40b3ec000000b04400000001242522c0000000000000ec130000b00000,
    0x1fc0b7040d0bc00184001b4110355b000134cc000943d00047000130000007c110bc0b2b4000017502c6714c004942b07c0d0000002c000d4e50340b,
    0x2c000443b0340b05cfb0001300011000250000b0340004d1502c0d0004f00000000173c41f000000000d07400000170010d001510003504d0102c1d,
    0x2c43044130001f000000000d0440004c000740d02c350000002c000003b000110f40004d992cc590342b0a40b28c00000000740005c4900000,
    0x1b4000000d000000000004c0b28c1100000000002543b00000035010742502c000350f00000000bf0000b0006522c1702c590d49d000002d429,
    0xbc1f000251c41102c00000b50000b05c0011c0007c002242504c0b05c00000e538c005441307400000a70001102c291240d0000b56c6b05c97,
    0x34250ac00000006443b044170013d034000005902c000341352c497241f00061000135bc0d02c110003b0000d0011919c1105c0b2fc001ac1331c0d,
    0xc70000b0a51b034a30001d0444f10cd302c170002568c0b000000a4130355d05c0002c000ac003140b0bc1d00000000670443510c6502c00000df,
    0x5c00000000740002c0d001610001300000095370000b0bc0d07c3b000000000d0000014c590000b000000440020c000002f0d400034000740004c25,
    0x2d6f04c000000b4f4002fc0d000130d4175fc000450f0bc0002c00074000ac000340004c0002c110343d3140b00013000110a42500000,
    0x1307c59000000bc0b0955d2240002c8303591000000ac000000b45400705330340011c0007c0d0001d0002902c000006141cb33bc0d0001107c00]⟩,
  ⟨212993, 1133, 262, [
    0x1307c59000000bc0b0955d2240002c8303591000000ac000000b45400705330340011c0007c0d0001d0002902c000006141cb33bc0d0001107c00,
    0x5d40d000000ec00000130340002c0011c95000110000005c000344f045af04c0b000290740b0ec00000002b4df0000d0442500000000000340b000c1,
    0xb034000000019443000001241d0001707c00000110000004c00000a3044000000b04da514c0002c4f05c0007429034000008b02c0019c170000b,
    0x2c11000000000b0003d1940d13c4734c000000b04c000441d02c00000000ac13044001c417001b70002546c00000a70d40000011000000ac0d02c1f,
    0x56c0002c0d05c2f00000314fb0341f04c2b074c13bc0002d372b40002c000001f20c0d2d40009400000001b4170000b0000d395850447f000a303400,
    0x2b000000341100000000474540b1942920c0003413001a31240d0005359c0002c000000005c2f1b40d0ec0b724bf0012502c0004d390440009400,
    0x3bc13464290445902c4f0000d4040b1942f05c0d1c400000113040b00047094000001100000000000341f05ce302c3d6c4000940b0000004417,
    0x44970003d0000d0000004c00000000747f0000002c0037c000bc17034110000004cc70340002c3d05c6b04d7b000000742b0340b000530000000000,
    0x670000b04d610001700011000710d4a302c002cc3b2240b074000000d184113c40002c00000e90440b000000948305c000000d0003b02c2900013,
    0x3417044000000002c710000007c11035af0001d0f40b03400724002b4170000014c001640d0000b31c110940d0ac1f4040000000000130f44f1240d,
    0x2c000340005c0b0a55d044130bc1f2fc0000017000130001d02c00000116956f1ac250000002c53000003040b0007f4341f22c0000000,
    0x83164170001d07c0b28c130003502c110002b0009504c0d0a40b194003bc0d0ec00044001fc1d13cb50000002c000000010c490345904c1d4e400,
    0x742f000000ac130001113c2502ce907c0d04c000017514c0005c89000000000b6ec430000b0354b000000d5610341100133000170002b0000b0bc71,
    0x37c0b0002900017094670440004cb30000003400044001b40013c00000254dc000340b0bca30000d02c35000131240020c110ec2902c0d1c4433c40b,
    0x2c0d4642556c0b000e30343504400000000000b1b41d0015102c0004c00254592b46b6c41d000130002f0000007c0d000000442b05d010351b02dcd,
    0x7c4702c002540005c00000d30002b59c00304000000002c110000002c0052c1d000130ec8b3c40003400045850000b035072249707c2913c13394c7,
    0x20c0000043074000d40d19c0b000006640d0002911c000450105c13000a302c0000000455250d41f0000b001750005902c002b41105c0d0f449]⟩,
  ⟨216299, 1135, 264, [
    0x20c0000043074000d40d19c0b000006640d0002911c000450105c13000a302c0000000455250d41f0000b001750005902c002b41105c0d0f449,
    0x2fc0d4f4005fc0002c00034130000b04507000000010f68c0029c0b0006b0000d05c000004f00065000000440002c0d0001d0000b0ec110342b,
    0xa41f00000034b304c0000043074002545905c1102c1f000290000d0440005c001c4007343d02c3504c0d724650003b044000000b000255ec1f05c00,
    0x4e4133c40b2d43b0002534c170000d0000002c000bc0d0740b1841f1ac9d044490ac0002c00074000000b0340004c00000e305c0029c0002c890ac11,
    0x11000000940d02c1300000000005741f000170000b045990006b0340004c000441f0340013c0b001190ac00000250001d034110bc0010db700047,
    0x5c0004c1102c000f44f0000b52c170000031400000e94541f04cfb56c0d02c000006104c000001714c0002c00304000000b0000d04400000002b41d,
    0x34000750d000110000b001cf0bc0002c0011c6704c170344f1ac0b0002907c13001a50000d0bd61094a70000d02c0007c0046c3b07400044000000d,
    0x2753d0000010c35034000ec5902ce504c000002919c490003d00011000000340b000002fc0b0000022c290000000013000830ac000001707c0b04495,
    0x440b000710000013c0d56c000000063400494000001305c0d00000000110000d0a40b0d42b0440002c132240000000184000002f02c00094470000b,
    0x2c6505c130d40b1fcd310c1128c000000d2cc0b38c0019c2b02c000003b094113141d00013035370440005c000349704c0007425000002d41702c00,
    0x2c1f194895d45304c1d4cc1100000034000006b02c670000002c3d000000342b000171640d3ec1104c1d0000b09400705af0000d1b45300167,
    0xd000000446134d6f0341f0000b0442f000000002b000250351b0001f0000002c115740028cc50008b0000b0000d0a5cd02c000003d034a700013,
    0x4c00034005ec5937cbf02d7f11d010000b3ec95094a713c00304001240b0009d075b70444305c00034001fc3d0000002c001c4e50000b25c2b00000,
    0xf43522c0012400000110000d19400000131ac0d02c430000007c1325c2f1fc00001670004f02dbb0001d07c0005c111b4130a40b000000000d00017,
    0x4641d2b40b001b10002f04413034250015d02c000455104c0b0f4170ad0f0000007c0d02c000001105c0b000b5001070000d11c000ac0002c000343b,
    0x1240007d390341302c17000000441d0ac6504c000340b73c000000d254670a4250d4000007104c0b0000d0014b0740005c0004400000c50000007c00,
    0x172540002c250004707c0b04c0d3a40041c650a40d00011000255ec1702c000016125c00000000f41702c13000430bc0b38c0022400000c7074a3]⟩,
  ⟨219680, 1136, 275, [
    0x172540002c250004707c0b04c0d3a40041c650a40d00011000255ec1702c000016125c00000000f41702c13000430bc0b38c0022400000c7074a3,
    0x250ec0022c0d5440b05c000ad8502c000740000000000170440b034003ec35000a70343b1b413000000001102c00000530344f37c11494000a53d,
    0xd400000170001f000001646b02c4900089044e500025000130001d0000d0d40b274130000b6bc0000000000ef0442b000000000d000c11240b0001f,
    0x340b2cc1d00000000c71ac3d05c1f0340009411000830340005c7f044130001f0000b0a40d0000002c001840d0f4000440004c1702c1d0003b6440b,
    0x2c000000011c0b034000000000013074c525c0b07c11000a702c0016435034001b4000000046453000000002b0bc610742913c000018d0002502c11,
    0x1102c5334c2b04c0d09400001bb31d07000130004f02c0d0740002c001940d0440019c000a40004c000001f0000b254002d411034000000000000,
    0xec1311c110a40005c00000ef0000b0000d0ac1d49400000000006d0a4004cc0002c17000670356f46d0d0000b0341729c2502c1f044000000018400,
    0x94d307c1110c1302c2f000005fc0b0356700000000c11b43505c0b04cdf0340020c002cc0d07c3d0000010c8b02cad585b10000b0445900000,
    0x940d04c6b0001d0450d0340007c000000052c3b02c00000000341174c00000000000004c1102c1d000255442f41c0d000174dc0b001150341d04400,
    0x44000340b000830008b0003b000431841d02c1f04c6d3a40b0acc768c1105c130000002ca7044650340b0002939400034000bc430001f02c7105c00,
    0x11c000bc4f000f102c000740d1fc3d04c000000d14c0b0000000000001610bc1125c290ac003140b0440000000000130f40005c71000000000d09400,
    0x440d02c0052c890000b0341107c0046c17000130ac000d4000000002c0005c0d5fc1d5ec000001102dc1000290000b0008304c000000003400,
    0x5c0000013035850000b000000001702c00000000355b5d4000000b094490001d2cc117241311c170000d0bc0002c1d04c0016400000000d4000ec7f,
    0x43cd30a40040400074df04c6d02c0d000112543d0000d0bc430940007da30000b04c000440b00097000000340007c490002f6dc00000354f40b00000,
    0x7c0b0000004c0d0ec114e4000009705c290004f6bc000003500000035910ada52240b034470000002c000940019c11000000341d02c170ace90000b,
    0x2c000009d3bc0b0bc0004400074000002b0000b0440005c0002c590740d2d4f10003b00000000110001f38c0031c670001122c0d0a4130000002c00,
    0x342b02c6d000002fc005bc000440003413000490000002c0043c1302c0000000000000940d074000000005c0d0000b14c130440000000000171ac0d]⟩,
  ⟨223112, 1138, 287, [
    0x342b02c6d000002fc005bc000440003413000490000002c0043c1302c0000000000000940d074000000005c0d0000b14c130440000000000171ac0d,
    0x1941f59c0054400034c54941322c0b0f400000000001f04c112cc00000000340002c000001700000000000440b0002f0001d02c610ec0004c1f00000,
    0xac002d4a705c130940d02d010ec001c40b04cbf574000a40d0441f0000b6940d000000008904c0000000074113ec0002c2b19c350340b164611fc1d,
    0x4dc4f074251842f000001c5c104c590000d0448902c35000e300000001b10f4001241f0000002c00000002cc130340013c000d40b074970001100000,
    0x14c0b31c0000049000950000041ce902c1105c3d0940b0a400044a70743b0340002c000000d5bc0b0000005c000440014c0019c0d02c0000017,
    0xd000000000002c0003400000000a400000254340b0001303417735b70440000013000000000b05c00455010000d07c001ac474cc670341300011,
    0x634110342902c7f000170000b00000000000002b001bb044000bc4314c1302c000441d0f41f37d7f0348902c002544f0340b04c111b40007c00000ad,
    0x34c17000110ac000000b0000d0941302c0013c0d664ad000610000b00017000c5000002740000000000175d41d02c00000431b400044254640d04cfb,
    0xd0741104c2505c0002d670003d000133c400000170000011c003940b13c0d2cc0b0000004c00000004346b0d40d07c132d4290440b03585,
    0x19c0b0001703400044000000000000000490bc530342907c000000d00000000170740b3ec110000002c0d29c0004c2511c000002b02c43000950440b,
    0x2cad000000000b000130a41f05c0d4e4350000b0ec0d0002f02c001fc1104c950f40028c61044000001d0340000089494004041720ce373c0002cd3,
    0xa41d02c000000d0000030411000bf00097614000000002c2904d5102c890001100000034e900000044ef000000d40b0000003400124000008b0bc43,
    0x44430ec00000e50ac000000b000df0000004c000008307c000000d31c1302c000bc250ec6d0001107c0b0743d59d3d02c0d05c000000014c2b,
    0x3429000670444905c8302dc9000000340b22c00304000341d000650000b0010f07c115ec0d434002542f2d40d0001302d5b184003140b094000740d,
    0x1840007c0000000034000016f1654b544110756102c130004746c0005c000344f0ac530440002c291ac13000350000010cfb1fc0b04c0005c0007c00,
    0xb434ad0000d07c00001250003b02c001c4000000b0001d000290000d1948902c130006b0000b0ac000001104c1700000035bb02c0028cb5,
    0x1d0000002c3d0453314c3510c0d05c290440b0002538c000002b05d5b04c2f000000340b0002904c2503400000110000010c1d0010f05c53]⟩,
  ⟨226607, 1139, 281, [
    0x1d0000002c3d0453314c3510c0d05c290440b0002538c000002b05d5b04c2f000000340b0002904c2503400000110000010c1d0010f05c53,
    0x5d40002c1f274290000b0447f074000348b0940000191254ad0000002c00034000006b0000d0bc0002c00000000740b044000000d0000000013,
    0x4c0d0000025c710000b035370d41f02c25000170bc002cc110340b000000001f05c001ac531958d000350440002c0d000c70ac0000013034496dc00,
    0x5c000340000000000000002902c1713c1328c1d07c3b0006d04413000000000b000253940b664170340057411001d303413000000bc110000b2fc8b,
    0xb0003d704000009d0000d0003b14c000440d0001704c2b10c610001d000254640b3bc0025c3d02c000001f044000a4b5124f102c8304c0d34c0b,
    0x2c890000d0000b000430d4000340005c0004c0b0008b0000002c25044005d4001840d0000004c1d0d4000004f43c000440d0001f4541752c1d02c00,
    0x742502c0003400000c16140004c0019c1d000000341102d5d0000d02dc9044ad0ec59000002740007c0d41c130000b194000a400000000f4d300011,
    0x1105c0014c0031c000750f07c0b454170a4000000d044000000004c4f1ac0002c0011c00000130a5af0340b25c1f1c40002c110015b7341700000,
    0xef000110000d0003502c001b40011c0b0941f25c1d000135fc000340b0a42f00013034170d4001242b0013d5ec0002c00034000440b0001300025,
    0x394a305c1107c000bc00000ad000001244302d3922c004cc000ac0d14c1d37c470002f02c9d0016f0001738c1d0000004c0b0ac000442500000,
    0x348b4940b3a4000440009400000130342f02c00164000340b0001113c00000000007102c0d05c2b10c0b14c0d00000000000f4000009502c000440d,
    0x4400000001b43d02c0000000124006edcf0001305c0b0000020c970ec1103400000ad6bc350440b04d074040005c00000252cc13000000000000017,
    0x130940002c350000d20c0b0744f0010d000001fc530000d1c4170742f02c0d000000a400000000440002db104c000000b2fc00034d30ec2f46c29,
    0x7c0004400000650000b2740041c1102c0d37d8d000710746b0000b0004304c47704000d400034003c4110015d02c2b05c290000007c00001910f400,
    0x1704c8b0443b000650000002c00044ad03400001371ac0004d4b2d4170000b0341104c0b0940d0001713c00000c10001d10c000000d0000b16400,
    0xb000350a4007349703471000ef1641138c0004c0018417034000a447584130000b0443d3a40002c000742b0000d0bc1f0000002c00034000940b,
    0x2c1f034170000b11c11000000006504c0059c0b0741f0005302c2f494000001709435001b1000000347f5bc0000011035015d4000742f0001f02c00,
    0x2c003c4000a4000440d05c00314000ac0d0441302cbf05c1f02c0007400635a314c000001100013000000000b000110001704c000a40d0015b]⟩,
  ⟨230178, 1140, 305, [
    0x2c003c4000a4000440d05c00314000ac0d0441302cbf05c1f02c0007400635a314c000001100013000000000b000110001704c000a40d0015b,
    0x224350ac0d000170f5610ed070340b1241f1fc0039400404950940019c000000002c0d184134cc00074590f40b0940004c0d02c6d000000000003551,
    0x3b0007f034430000002c9d0016f0000b0000003400314110000d5fc0b0000004c1d000000ac001840d044430bc0002c6d0745905c0b000835ec00,
    0x74c004544704c0005c000001d0000d0000043c0002c0d1943d045cf4643b07c670d4170000002c2529c00034110001707c000000b1c41137c0000013,
    0x4c000000b0740d000000002b000000940002c59000000000b4e48b03400000000bc0002c1f14c000000b0006d0440000000034000001302c1113c00,
    0x470a4492240002c1f664252746b00013000115ec0b0acef694130440d000350740005c000f40b0006d00000124df044130000d000613ec00000e9,
    0x3400185c902ca30942b0000b1ac000342905c000001103400455374042502c00000673040d4f4710ec1d02c0d574004640b07cb50000004cbf05c0d,
    0x10c110001f000130340b000173c40002c0004c0000000044ad0000b6445303497045510740004c000009d2540002c004cc0005c110a43d0004f20c00,
    0xbc11000000000d0001f02c1d0000000017000470940d584002241f0ac0b05c000000b61400000000a413074e50000000000034a70ac0b00035,
    0x5c0b0015b10c113ec6b22575000170000d18425000000001d0000004c002cc000000b07c000341302dc1000ad03400000000000002c53044290740b,
    0x2c2b000000000b0440013c0020c00000000340b000170a41302c11000000006d034130001119c0d0000007c3b000000007f52db70000d0001302c47,
    0x440d02c003046b001150358d0949d05c7131ce33a40002c000341d02c110004907c000003b04591194000000046c0b2cc2f04c00000170340000000,
    0xac000341d1add329c25000111c40b0000011c000000005c000a4000bc000001102c0068c0007c00034001940b000000342b02c000001d0000004cc5,
    0x451b0940004c0002c0d000110740b0000d0010d0ecc777c004e40b0003d5fc0000000000bf04c1105c0056c2502cd3000130000b13c0d0d400,
    0x130000d044000001d00000034000440007cf102ca314cb30748300000454000000d0001702c006dc000000004c652b40d0000b000000003503459,
    0xb0341f0ac1337c3d254000001102c1d0342f7240b0d40d0000004c000013702c000004f0940b000170f42f00000000000000002c000001f,
    0xbc0004c005d40002c11001670000d000001b42b0000b0000004c000001d5ec1f001cd04c2505c0b00043034001fc11574610000025c290d400000e3,
    0xdf0000002c0d000000440b0008b1b4000000004429001a5000000359902c13000c103400000110000002c0005c0034c0b034005fc2b0941d54417]⟩,
  ⟨233786, 1142, 281, [
    0xdf0000002c0d000000440b0008b1b4000000004429001a5000000359902c13000c103400000110000002c0005c0034c0b034005fc2b0941d54417,
    0x746100000001330000b0a4000450d02c1d0f43b584000003514c0b0000d094000013d0000013c2f05c0020c1f02c1319c710440d00000000001946b,
    0x34001640000000000170743b02c00034b30002f000130341146400574c50000b614fb0000b00107000130440d29cd305c670001f04c590000b4940d,
    0xb1941307c000340011c001842927400000000001d0d425044e912417034005d40b000130000002c170001159c0004c0011c0002c11001bb2540b,
    0x2c290002f1240b25c0d04c0007d0f22c610440b094b50000d02cef000000ec0d04cb310c004dd0d000e504c000441d001cf00067034000001102c00,
    0x2c1704c95074470ac006443d0000d000110000002c490000002c0038c174e400000000342900000001190340b044470003513c1f1ac000ec13,
    0x4c430f4000000007c001940005c0b5bc0003400000110000005c00000290447f02c25000b50000d14c000000b34c000003b02c170000d31c0000011,
    0xd00000000170ec0002c00074c107c0b000290d4e30442f034130740b184250440022c0041c0037c296ecbf0000d02c130001114c0b034000ac00,
    0x2f0341152c2510c2900013000001948b1c43d02ce504c000002528c00000890a43b0000002c1f034000ac0010dcd034000000b0440004c670bc00,
    0x2543c0b11c1105d072d40d000490005902c0d0000013c0b000b307c2b000534341702c0004c610000b0000007c170001d00000000ef02c0d1b400,
    0x7c000000d000bf02c00000290344300000001154cc0b001190001105c000013d0000d46c110000b5ec2f07413000003a40d2544307c6d05d670341d,
    0x44000740002cc5124530000b0ec0058400095c90340028c000000d04c1102c000013905c00044131fc0d02c00274000a40b0ac0007489000535fc25,
    0x73cb30003b001510000b000110000d02c9d05c000000d000130000b43c8305c11000132242b0000004400034d302c356641f00000184000bc1305c00,
    0x4041f044000f40d000000941702c113c435635d331c1f0002b614290341325c0b0002f0340b0000007411464490006d0aca3034001651b0000b00000,
    0x2d40b000000444f41c0077c5900013044000a417000b30003b0001f1940d0f40005c0b000fb001af02c000006b0d400000250740d02c710000004c0b,
    0x2c00094ef19c0b04c002541d00017034112740b0bc2b0340002c00000000a4650001f0440d68c1704c001b40d000003940000013584000000002c0d,
    0x941302c00074670341100000000000d4b5000000a41702c1f000a702d33034000000013c002fc001b42528c8304c0b4dc00000000bd990742b56d25,
    0x1c137c00000000000d0449710c0b05c000010f044610000d0017b3140004c0d02c490f4e5094111c42b6140b0009d07c1102c0003417000000a42f]⟩,
  ⟨237482, 1143, 286, [
    0x1c137c00000000000d0449710c0b05c000010f044610000d0017b3140004c0d02c490f4e5094111c42b6140b0009d07c1102c0003417000000a42f,
    0x4c89001010006702cc10440020c0b000002544f05c0004c3b0ac0b0011b38c0004c1f034f10001d34c000340002c53044000ac0b07cb309400,
    0x20c1d05c00000590001f00000000350ac170340002c00000110013d000496c413034000744702c0d000000440000000000000000b0940d0001700029,
    0x1fc0d28c0b13c0000000034000001d04c0002c97001a538c0b0340009400000000006102c1710c0059c0b0d4110740d2742907c2f0001102cdf11c00,
    0x5fc000341f05cb502c00000bf0ac00000000440013c0b07c1d0940052c6d0002f0f400001cd0a40b0341300017044000351b5ec0004c000001107400,
    0x1302c00000000bc0b000673bc000740d56c000f40074c000441f02cc1574000001305c000004902c007042b0440b000000000011c0d00000,
    0x1df3ec0d000000000b04c000347102c2f14c4905c112fc000000b000e90440004c0d07c004e4250000004c0002c3d1840d314c7000000000003411,
    0x25c110001d035910a4710d40002d750943b0009d034000448b07c0d0000029c0b044000940b0009505c0d07c2b5bc00000430001111c1d0a40b00013,
    0x4c0b000110002b00017164250000d07467000001b40d000004f4000002f0002b07c0b00000000b502c53034293c4ad05c000000002c134dc2f6340b,
    0x2c1707c000000b0941d0000000000224130ac0b465af0000002c13034170006b124290340007c3534c170000073c0000013034470f4430446502c00,
    0x304e902c25000000443505c13001990bd6f0001d14c0002c170001102c0d11c8300000434110d40068c000008b0000b0009528c0d38c0004cb504471,
    0x346554417000130d40031c000000b034fb04d0119c3b0340022c001ac110001702c006140d04400000b33940b001330bc0002c000003b1c4002240d,
    0x2cc000a4431941d0340002c1104c3b0000b00025184000000005c2f11c0b034111fc00000000001d0457f10c130000002c00454175740b2fc1d0001f,
    0x740004400164170000d14c2b0001125c1d000df02cc519c0d59c0004cb50000d394000ac3502c1300011000a30000011c3d2b40b034000005900000,
    0xb044296c4ef074a30942f0440d02c0007c000ac0b1ac0000061000000ec1102c000343d0000b000000340010c000000005c2502c1300137,
    0x4f5fc000000002c25000df1940049411035a50000b0005956c004341300000034170441d34c0b001390a41f0bc1713c0004c003c40d0000000000,
    0x59c0d0000002c00000110340b0001310c830ec000f49d25c000340005cc102c1d1c400001e7000000000002c000000d14c0b0ec1f10c7f0342904c00,
    0x1b70343507c0004c0b044490005302c655bc130451b0a4e92240b000c70ac000bd1505c0000011034001844702c000341100013124000ac004cc00]⟩,
  ⟨241248, 1145, 302, [
    0x1b70343507c0004c0b044490005302c655bc130451b0a4e92240b000c70ac000bd1505c0000011034001844702c000341100013124000ac004cc00,
    0x16413001d3000fb000000000d02c0043c2b05c0d10c6b29c47001250007f05c0b000350ec0b30400094005840004c1f22c000441d2ccad4340b05c6d,
    0xb0d40d00049000133a417034000007f13c1f00000000110a42b0746704c0028c0b634256440002c000442f000001240d05c0002c1f000000340b,
    0x2c3504ce30340b07c0000000724000a4000000b0353d0746502c0d0000019c0005c0004c00074000000d52c1100000000000bc00254110951502ce5,
    0x5c0002c290003d00043000a70000d07c00044ef04c0d02c000005902c000941300000000d30001700000035390440b0001d00025000000001100000,
    0x2fc950007141c0d00000184002240b04c4f0001111c1700000000000358510c0002c00034970001f001a30740b00013044df02c7f00000574000001d,
    0x1c4000750143c00304b502c000000005c0b0000007411000250000007c0b044290000029c001fc47000130bc2507d0d02d8d0000d04c0b38c000f411,
    0x341100013314530ac00000000f55103400000ad02c29034000ec000000007435044000000d02c00000f10000d13c8304c2f0000b07c00164490000d,
    0xd40005c0b000000353704d7b000590001702c2b001e72740b2d5750bc000340004c0002c3d001150740b04c970000077c007243b044c702c1700161,
    0xa4000000004c1102c0d0ec6b0002500047224000000b1640d29c3d1840043c0d0001d000170000b10c0068c00000000001f0748b0342b044fb00013,
    0x4c1f0010702c00044001ac0b000290000d694000001f00000000110003502c2522c0011c11034650ac0002c17034950000b00000000130001f04435,
    0x442900000074250f40b0000056ca302c13034003142f254000000b0d4110000003400464000440d164000f5bb02c2f5bc130002b0000d0740014c00,
    0xbc0d00185000001ac000341102c2b0001f4f40005c0004c00034000004313c0b0741f1fc0b00029044610000005c0d20c0000000001750340b00017,
    0x13c0b034e9394131640000191000112d5cd04c00000252241f00017000296dc001b40b0000004c0002c110019919400035af10c0002c00000000000b,
    0x2c1d000000440b000170ac0d04d37045a50940b0010f0009d02c000000007c00254110740029c2f0ec2919c130000005cf100061000000000d02c25,
    0x1702c0d0014b00029000470341d000110002f0000002c710006d02c17494000a40d0441f0f41300017000000740b0000d19400000bf07c2503453,
    0x1ac00034e30001105c001240b464004047103400614130bc0d0003d0004702c1300000000430000d0000b000110013902ce9194e5000130743b,
    0x17000c10000002c290000d0000b074000440d644000d4896340b1241700000000530001177cc50345919c0002c1104c000000b22c000004f,
    0x194590941f0000d0000000000044134f495001cf02c6d07c0005c1d0342b001b1000000355d02cef25c004943b000670a4000340b735610d40004deb]⟩,
  ⟨245095, 1146, 321, [
    0x194590941f0000d0000000000044134f495001cf02c6d07c0005c1d0342b001b1000000355d02cef25c004943b000670a4000340b735610d40004deb,
    0x94000ec0b1c41704c000001f1640014c0002c130007f0000b124a346c0d0000031d1902c3b0000004c0b04400000005d4000000d0001d02c0038c00,
    0x341341c650000002c005fc43000000340029c000000b0342f044294cd67000000000007c0d0940b000000000d04c00074000a49505c11000000000d,
    0x2f0000002c47034130000b00000000000456f124000ed010740013c0002c00000170002b000000a40002da30441725c0b19c000d4a30001109400,
    0x4cc514cef0000b0006d3a40002c4300011000000d40d04c0b044ad0a40d07c0004c8b000590f4000000002c0004483001390340005c7100000,
    0x10c0007c476eca7494005446502c4f1240d0000004c1100000274000941d0440b0002b05c0b034000002f1fcc703400000170007119dcf0000b07c11,
    0xec0b6640046c1d0000007c003151904c00034000002b04400094000000005c000340b254000000d02cdf000000941328c000001102c0d0001d05c0b,
    0x2c0d0001110c0b00000034173ec0028c1d07c0b000130000002ce3000976bca7000000000052c0000013094000a40d0016f05c490446b0342b02c00,
    0x3949702c131fc1114d7b075150000069400704170d52502c001640002c00000d305c2f0a41322c250342b000000000b03400184001ac000440019c1f,
    0x5cf100049000000440004c0d0000b094000000d0001d0011b000110ac000001f02c590941159c170bc0004c0b125e70002902c000ac003040d04400,
    0x450131c0d04c00634a302c25034000ac0b0f43507c17001d3000df1c40b34c1d10c0d000000442b56c4f000000001d02c0d1ac000000b0009d03413,
    0x4c0000000034000757525c1113c0005cef0000002c00000001940d0a4250ec11000000000002c000440d2241f00000000e50000b0bc136440000000,
    0x440b20c00001b14f4000ac0d2b41302c4737c0d05c0b3ec1300000000005ecc502c430000022c0b034a7000000d4130001d000b302c000ec2f,
    0x3bc0005c000440d02c004341307400044170d4001640b04c530016103400254002fc11034000bc0b07c0005c000002b0003b034001b40004c17275df,
    0x46c000006702c130ec001c40b07c3d0001104c250000007400000f10000d02c00194000441704c000004302c291ac1f0f40b1b40d000494540013c00,
    0x34000f40005ce90000b0000004c0002c000001f0ac00034000000b000a30004941c290000d00000000002fc0d02c112241d0002f0001f0000074c0d,
    0x574000000037c2b034000454b02c0000115000000448331c000000004c000340b184006dc0b05c110008b074001b4290001100097000250000b0001d,
    0xb074000000019c0d0bc890440007ce50ac3d05c000000d25c9d001370000d0000b000291940002c001ac0005cb3000000453302c00000131640b,
    0x2d0d0a4bf0940b4f400000000ec001640d7ac0b544006641102c1731c13075e70018d000000341f05d0104435034250000004c003a4470000002c00,
    0x2c3b000000001719daf1fc133ec290357b0004902d670440002c00000000343d10c000ac0d074000001107c0b05c0020c532240d0000004c00]⟩,
  ⟨248989, 1148, 324, [
    0x2c3b000000001719daf1fc133ec290357b0004902d670440002c00000000343d10c000ac0d074000001107c0b05c0020c532240d0000004c00,
    0x7c0d000000002904d850346711c0b00053044130000000000034d3000170003b02c1d20c6d1246b04c170000b0440d0000002c1307c00034110003d,
    0x4541303400000970002f02c1d29c000f40b00011000000001713dc10440b00000000f10ac25000000341f0a41d04c0002c00000000000b1857f0007f,
    0x17074830001311c0d0d4000bc000000d02c110ad2500191665750441743c000006b02c002cc35000000018d0001f11c0b000000740d00011,
    0x1104c0b6bc0010c2b124350340019cf102cc50001f0440b04d5b27400094000440d02c00000000000b37c0010da30bc0d0001152c5302c1f03400,
    0x110341702c4728c000a461000005fc590340b000000000d124710001300000000bf0000b0000d2b400000c709447000830442f1940000000,
    0x1d0000002c11000000d40b0000d04c1f19c000000d304250a43b0011902d0714c1f074ef0004f0d40002c256c4130000b0004305c00044002d539,
    0x38c00224fb0000d0440b000000001d02c2b00000094131841f0000b0349d00000000170341100000000130005302c172fc000340004c4f0017504465,
    0x442b0001300000000000000002c000002500095000ef43c1d2b42b05c0d07c0b304000000b0443500000000000bc0004c000000d0000005c0b075bb,
    0x340b6dc590ec650003504c11694250343d0746d000670340034c00000001ac1104c0b05c0d0d40002d5104c0d0008b000175bc3d02c0007deb0000b,
    0x2c000440004c0b0341f000000001129c6d05c0b000df0004302c1d0006b034250bc00184006c40072411000002b4e94342b000b30002925c0002c13,
    0x4c0002c1d044254640d0001700049044000007f0002902c0d0002502d7b41c0d0f41100083584001855d000002d40b0019105c00034131240000000,
    0x252541f0007f000000a4001b40b0740d00017000bf07c000001310c000000002ce904435034a738c000000b034000741302cc1000000000000000,
    0x5c0000000000350ac1102c1310c170000b034000002504c29074002b40b274000340079c000000d4dc470ec000001102c8b0bc0013c0b04c000017f,
    0x6440d0bc000001346c0003400000290000004c1d02c170000003519000000bce32240007c0002c110000059c000000d000110000b00061034c500025,
    0x11c290340b0ac000005922c000449505c0002d33194000000b07c6729c1d000ef0000002c00000000340b07c130019903400044a30001702c2500059,
    0x6d000350001d02c000940d000000014b0000d0000b05c1131c0004c000009d07d012d40010c0b0acbf04400000003c5a30016f0f43b0000d00000,
    0x740005c0d02c000003d0000b0343b0001700000000c10bc13044000002902cfb0000d0000007c490000002c116bc002540b22c2b29c110001303400,
    0x10f095510340020c0b074e30002b02df30442903400001330000b0bc133c4672b471164173943b14c0d0000002c000000004c002fc000001100000]⟩,
  ⟨252953, 1149, 316, [
    0x10f095510340020c0b074e30002b02df30442903400001330000b0bc133c4672b471164173943b14c0d0000002c000000004c002fc000001100000,
    0x94350000005d190bc290000002c0d0000007c110000d34c0000043044653040b0a4490000b000000002503417000000440037c0014c003a40b04d07,
    0x4f40b164004e40d04c000ac000000000000000136ec11734001c400034000441d0000b0358505c0002ca70011b0001d0003d0341302c590006d11c0b,
    0x2c110003d0000b07400694290001f2fc6b0ec0b05c2f0440002c000000d0001f04467001df28c3d404000000004c2f000000ec0d000000015b02c17,
    0x351b02c110004f000130000000000035b13940007c0002c830001702c0004db7094001940d0017b05c890000d0000b0a4000001d0444311c000ac0d,
    0x17f04dc10001103417000710740b00000000000f4000000004c00074000343502c0004dc900000000b50ac0b0000005c6d02d25001eb044530010d,
    0xd4170002b000e50440d02c005846b0000b0000004cfb0740d094110ec0b0d40d25c0013c110742f19417000610940002c000a41f0340b6140004443,
    0x457b77c4307d8d0000005c001adcf04c0d0a42f02cd3000170000037c11000b311c00000f102d5107ce30946d034130001d13c0b0008b0eca72b4c1,
    0x9d0000b001993bc000001107c000000002c006dc135bc0b0bc0041c350a4110340002c4920c0d0440b0740014c1f1fd4b0ac4704c0d02c0031c1d,
    0xd044135743b02c000345305c11094590001f0740b00000034000d48911c0000000094130000b00011000000000d04c000f4170741f0340000000,
    0x340002c1707c6b04c0b0009704525000c1404000002b000000000002c0004c11001752b51b0346702c007cc000340b68c001c400000000a400,
    0x2b4002740004c000940b1fc0d1840002c110bc0d13c00000000ec0b11c25000000002b045150000007400000e502c0000000000ef05c000000d00013,
    0x4cc50000d0006b05c110000002c00000610000028c2b0002f00000304000000b0000d0a40b0001f00000000670001111c0d0743b000130000b03429,
    0xb1244f034df0010f0441d0f4e30001322cd303497094000000d05d256146d0000b001670001102c0d0001d07c00000110000002d3705c2b0bc0b,
    0x2c3b10c000740b00000314130440d000000000b2fc0d04c0002c001b4000014b0000005c3d0a4000002b0340011c0000017045a307c0004c3502c00,
    0x6b02c000a40d001a500000734000000004c000005902c110d43d02c3b05c000744f0340004c536ec1f0450d4cc0b19c00034000ac970000005c00,
    0x2b4530017f000430001704c0b0ac49001991fd15000a7044000000d000bf02c9d000000002b0001d56c0b254003041f02c0d000110d4004dcb3,
    0x341d0009d000000a42502c00394000340b044170001f034470000004c0b10d7505c000740d1641328c000f40d0440002c00094000000b0a4110000d,
    0x5c000000009400034f1194490ac17704710001102c00000133141f0440003400000130000002c170ec0011c2907425044004cc0b1253d74c1300101,
    0x8913c0b644596940d001f71c4006bc1f02c00000110000b20dbb000130440d0001f02c00000000bc0b000000002b0000004c000352502c9507411]⟩,
  ⟨256980, 1151, 319, [
    0x8913c0b644596940d001f71c4006bc1f02c00000110000b20dbb000130440d0001f02c00000000bc0b000000002b0000004c000352502c9507411,
    0x3ec11000002744902c0020cb54e41305c0d074430bc0b0441f6657f0000000095044a30010d0340b0947f000000342912551000111841714c0004c3b,
    0x712fc1102c0004c000000b00000000d3034130ac8b05c000001d0000002c0003400000250f40d04c0002c2b001b707c0b3c4130440d19c003a5cf,
    0xd05c1d000110000b034000000002c171fc00000000016f0340b3bc3d0002b000e30001f000470000005c3b02c0d13c00000350001d034170002f,
    0x4cc000347f00000044130006102d39074290ac000003500161000110000004c0b000000000b0bc00034001640079d5d034000d4250003d1ac0b04400,
    0x440b04c0005c290001d14c0d3bc00000000000d0d4000018504c0000011001f30000b04c00044e502c0000017000c50950f07c0002c000000d0000b,
    0x2c001b40d0000b0000016411034fb000470000b04c6107c2502c00000003a4110000d2740005db1044000a4250004f0000d10c2f31c0028c3b02c67,
    0x8b02d330349d000002b41f6341104c0013c350340002c000ac0d02c1d0002f0004311c000007f0000d0007105c0b56c3529c6b68c003142941c17,
    0x672cc000441d79c000bc2b4040b044253a4000000d0a40025417164000006502c1107c2f0001d05c130340b3051514c0002dc904d4b0001d59cc7,
    0x74000001338c0d0001702c000a4250000b00000001190ac0007c490340b000000002503413000430f40007c000000002c6b035750000b0010d00000,
    0x170000019c000001104d51000470004f0d40002c000017b0a4000000d0002504cb50000002d0f0001704c00000111ac000000b00000224c11b400,
    0x340007c0b04c254dc000448331c000343502c3b0441d0340b634250002f000000000002c0d07c110000b0000d0000000011000000006d02c2f07c0d,
    0x4c2514c17001a502c2f07c3b0440000000314000000b3bc00704000000003417001d30009d2cc0b124a3000000d41d1847f04429000130ad0700000,
    0x224fb0000002c000740d0000b05c000bc1307c00000253c40d05c13000a702c0d000000000025c000006502c6b000006ec0b3a41703400001af20c00,
    0x2b00000000170000b4dc13000d302c0d094000000004c000440b14c000ec290000052c0003400000000001102c6d0bd5d7ac1d0001104ce52cc1f,
    0xf1000131c4000007f02c1f000430340000029000003042f074470000b0340028c0b04c0d0006b0003504400001f70000005c0d10c0b0ed19,
    0xac0b1c4000005305dc10340004c00435850001107c00074890340004400124003140b38c00074fb02c3d1b41325c0d0442b1650102c00034ad0000b,
    0x2c00034002240b0ec005ec000002f000002b40b25c110002902c4704c00044c72cc000000000013034000001f5453d0341d0006556c9505c0002c11,
    0x13c1102c0010c47000007ac0d34c29734006c40d1840002c131248b02c95000000441305c001acc50011b074df0ac0b00017000110000043c0d5841d,
    0x94290740d07c000ac9d000e90340b13c0005d39074004940041c590001305c0002c0d1b4c70000007c250000b000000f40d02d8d0447168c6503400]⟩,
  ⟨261097, 1152, 330, [
    0x94290740d07c000ac9d000e90340b13c0005d39074004940041c590001305c0002c0d1b4c70000007c250000b000000f40d02d8d0447168c6503400,
    0xf447034110000002c1707c134dc0b0002b03400000e50000d2240b074000bd85000df094290000d000004f41f02c0005c000ec0b0440004d91,
    0x65000000ac000447f2242f0ec0d000000001302c0d000a3000110f4290000005c004541102c0004c000344f00000724000000b0001f5bc00044ad,
    0x44130000b1940d07c000d4f1000171240002c294e4ad0000b2cd33034112d4000941d02c00044170ac0b0002f04c000000003400094c502c001244f,
    0x2c13644110005907d5b4dd1b19c0b11c00000000940d04c110a57f1c4435d40b044001841d00000000000bc0d6dc000007f29c00,
    0x3599045a502c000009734c0b14c110340028c00000430343b04c000000002c001ac3d04c0d0001f0001102c0d094610000b57449000170740073c0d,
    0xad2d400044000340b43c291940002c004640004c4705c950000b07c000341307411001af0d400000430940002d250000059c0000000000c70003d,
    0x7c0005c49000000d40d0ac0002c8304c11000001b4001c40d0000013c000000b3a4000440b000251641d05c00124130a40000000034000000b1842b,
    0x4940b000000f4000001129c8b000000940d000472d4130bc00000001ac00000000000b074170340002c1300000034110002f3940002d07001a30000b,
    0x2c000001305c0b164c7044250001d14c000340b0457b4e40002c290bc000f44303400000132240d000fb000170740004c110a5610000d0000002c00,
    0x77c0d02c000003509471034000446d185fd0a5c10ec1f02c1d0345302c25001af04c002cc0005c000a40004c000000b00000044001fc000341f07449,
    0x37c000342504cad000d3404005740b31d7f074fb05c00000111ac1f20c2b0a58d02c000d40000000034000440b05c000340002c00000000015100013,
    0x4d15001cd0d4000006d02c0d0008b0000b0000d0a42f09539044170000b000006441f0f4000ec0005c00254110002f02c00000002d40b6c40d68ca7,
    0xbc436940d0006d34c17000b303400000130442502c000001f000131840019c490000d0000002c0000000000590440005c0d0ac0b0001d0001103471,
    0x7cc170000b0342f2fc0000013000000743d02c110340004c0b4940d0441707c970003502c2b314000000b000000a400044490003d3bc4702c0000000,
    0xd4970001302c1d05c9d0940d0003b04d0d74c0b00017074c7000b30440046c8b0a41f04c0b001bb035c910c000ac00000000002507c0000011,
    0x110001702c0d14c1f0000b04ca722d010001d001b70440028c950348302c170442b03400000e94f46102c13315b10000b03411000000016f00000,
    0x1a556c11094000000b0000005c4302c00000000002b0f40005c0b04c0d1655152c00000650a413000002d40002c250008907c0d04400000000006d,
    0x34000001f0a411000fb11c4f02c00034001ac003bc00034131fc000a4000000b0d41319c0b1241d0000073c0d4543d0000011c6141c000440b13c0d,
    0x740b00000000d30340059c1f000007cc1d000a30003b001c9000114dc13034001c40b22c110013d02c2b00000584000000004c0002c3b1b4610440b,
    0x2c003bc001840b05c0d0750d254131ac8b0bc0b000002cc0d02c710ac1137c0d0001707c25044002fc9d00083000170004700000035190a40002c00]⟩,
  ⟨265277, 1154, 332, [
    0x2c003bc001840b05c0d0750d254131ac8b0bc0b000002cc0d02c710ac1137c0d0001707c25044002fc9d00083000170004700000035190a40002c00,
    0xd40002c000000004cc512411000ad0ac0d000130001d02c2f07c0002c000d411000000001d0342b0440007c290340b000e3000130f48905c4f00000,
    0x3a41304400000000003d634006bc0b20c00034005fc000000016400124000941d02c2905c000000d19c110000b04c1d1b41702c255d40d000000bc00,
    0x20c0d07d91044000741302c6b0ac000440b05c6100185000000340010c0b04c00000110bc0007ce313c00274000000d02c00194a725c0b0340005c35,
    0x35f711d0f0000007c1710c9d000110eddf02c001fc2504c000d400000003c4000442902ca30342f19c250002b034b505c0b1957b0010100133,
    0x125610a40b000a3000110000d074bf0000002c0d04c0041c0b13c00074003bc1305d9902d3d000000000b00000000110003d000000015d02c0d25489,
    0x5c0011c0d31c1f02c00044000341704c2510c000440b0758d000350010120c000000d0ec000740b29c000002b000130000d00115001cd0bc000341f,
    0x1bb0000002c290015b3040b0441f0000000000034132d4000000d0ed3902c1f000250006110c8b0000d02c0019c000000b0445304c0013c0000000,
    0x28c0046c130000025c0b000c70000d02c530ac0007c0d10c116c40b00059434250006d4f413000000bc470347f02c6704c0000000000170ec000d41d,
    0x746b0000d0013304c0002c00000007dc00074e905c0004425034530000b04c000340b2d44f6640004c111843b6dc0003400074110000b3c5d3,
    0x11c0b05c0004c3b124b3000fb464000001704400000000a4000d4430000d075cd0000b000000ac0002c0005c0004459000001840d02c4f59c1143c0b,
    0x2cd30000007c0b00000000650a400034000000b2b425035e702c6d045cf00083000000000d3c400074000000d000000444319c0037c130d58502c0d,
    0x4902c6105c00034000002b07d3316413094a77241102c000a41302c00034000001d0ac710bc003bc00000170000b00013074e500035001c100011,
    0x1ac11000000003d0000d000130000b0a4000001f000a30440d0016f000000000d02c00001b705cc1000000000b52c003ec9702c110341f04c252fc00,
    0x110741307c2b02c00000000000b04c0005c6d0004f000002d40b31c0056c00000470344939400000530340002c0038c290440b0740045417,
    0x68c3b3c5cf0001129c000000004c0007c000340002c650d471000170007f0002f034000019102c0d05c5922c1320ca3000250000b6bc0d0455d0f443,
    0xd0940b0000004417034000f4002247f02c710000014c0b0341104c3b0ac290004902c11000135d40b10c000000d05d0d4645913c2902c0004400,
    0x4417034000000002c002540043c000002b000000000b000131946107c1125cdf000130743d0440b034170017f07c0003400000356640011c131ac00,
    0x7c2b0000002c00000c105c0b0001d404000000d000354cc170002b0001302c111840000000094000440002cad074530ec0b04c0007c000000d22400,
    0xa5510440d1c40028c0b001fd0341102d1b000000d4000001d0000b0002f000170000d584b3000000ec110008b02c496440d3bc7f11c6b0002f03400,
    0xadb1000000340004c2f0000002c2904400074130350713dbb05c0d000000000b094110000b1fd6704c0d0f537000000001f00013094000000b00000]⟩,
  ⟨269548, 1155, 356, [
    0xadb1000000340004c2f0000002c2904400074130350713dbb05c0d000000000b094110000b1fd6704c0d0f537000000001f00013094000000b00000,
    0x34c0b19c6d7ac1700000000970000d0bc11574350000d000000001d094000000020c0b0444f0000002c490340004c00404350004702c002cc1f0000b,
    0x2c530001d0000b000113c40038c000009d20c0b10c000003d02c1f0340004d25000000340074c290000000000094110bd850357b05c1d2547102da5,
    0x1b40002c000000005cdf04400000000741f00000045cd02c0004c2f02c0d4f4000001704c49194116bc000943b22c0b074110000d0002f1840000000,
    0x34000ec95001c12d41d6ec000440b034000d42904dfd0341f0740005c002cc1302c000000d0f425000290000b000350011902c000000005c000000d,
    0x1b70ac4f0342902c000002f04c0b2741d41c00000110010f79c0b034000a40005c000000014c71044003941302c173ec4f46c0b0000000000,
    0x29c0000000000000000d0002574c610000005c0002c130ec0d044000001d05c0d0010d1fc1f02c950ac13000110bcc12cd370000b0341107c3b05c00,
    0xb0001d0941f19c17000000ec0d02d5b0000028c0b000fb5bc2577c00001af02c130341d0000b0003d0349d04d6705c2b1b40002c1100000,
    0x7483124250bc0002c5904c676642b0d41d034110000b1840011d01044002245303400001390000b0000004cef000000440007cad0000d0012500059,
    0x5c0d0001f02c00000000340b22417000003c4430001107cb3034000000002d61000bf00000000170018d02c350000d6c40b73d37000000340000011,
    0x4c1103400000000000b0ac1f0000002c000002500017044470000b0001f00000044000001d00000034000002f02c00034a70a41100013194530002b,
    0x1113c00000000000d02c3505c130a40d000000000000013000000000b0000007c0b000000a40011c000001d000130bc00044170000b00000,
    0xb0bc0d00011074001c41303400000000000013c0004c0007c00454000a43d0ac0b0000037c6b02c0007c00001190000d0014b02c25044000340b,
    0x2ce505c000340b04425000490d4003141704c0b0347f000e302c0d00043000b507c000001104c6d6c40d05c0014c0046d070941d124592b41702c00,
    0x44a702c2b094651fc950003504c0d25cb33ec9d11c0d02c000000002c110ec00001c900017045390015b034130f40b0000010c00434005d4e907c00,
    0x545a37ac0005c0d43c6507c110000b0000000107000000740000000034005fc1102c4303400074130454b0000b0a4b51242f02c8b000613bd370ed5d,
    0x6140004400000000018d02c00000110000b07c0000067000135eca70bc0b0005922c130a4ad05c00094113a4000016102c1d0ac0d0000b000131c429,
    0x3400000000441f0bc000000045465035c10f48302c000340000000000131b5bb000110000d02c434e4000740d05c000002904c0b00000000000000d,
    0x740b000f10340000000000130001102c4f074b50000b000172fc000341f6dc3b02c000a43505c0b00000000710ac59000000740002c0004d6f,
    0x68c000a44302c0d0000000000000a71841307c0b0000d000000a4000740d0002b11cc50d40b04c001c4434941105c0000013035330009700000,
    0xbc1313c0002c000d5670440b0010111c0d000000442b0006d19c000001702d9900000000b5034110741702c1f034000940b001d30ece334c4900000]⟩,
  ⟨273869, 1157, 336, [
    0xbc1313c0002c000d5670440b0010111c0d000000442b0006d19c000001702d9900000000b5034110741702c1f034000940b001d30ece334c4900000,
    0x7049525c533bc2f0a40b05c430443d02c00034000015d194170000b0006b04c000341d000000000d2b40046c2502c000f5df0441f0000d0a42b00000,
    0xd04c1707c00000000341d02c473040014c6d0940000011034677cc710000b0000004c0b0002f07c2b0441d0000d0000012400644d30340b69400,
    0xb0348307435000002d40005c00000250002f04c9d0010f044490ac00000130000b000970000002c004e4114041f0340028c1702c11074000000b,
    0x2cb34cc000000b000e50000d0002504c000440b1c4004f43b02c7f0006529c00074250d5990002b00053000000441300000224001641f0000d02c00,
    0x2c0d0d40007c0000059034f11fc00454110001302dcd0000002c00000250000d000290000000013000610000b0440d2740004cdf14c00034c5,
    0x1d0a4130342505c3b6dc000ac0b07c0031c00034110006b38c0d000000440002c1707413000001240d0000b0001704c6102c0034c0029da500011,
    0x11001a32b4714cc0002ca30000d0000b0bc0020c0d044000000005c0b001c904435194e90001f00000034000742b02c00000110000b05c0022c3d,
    0x2d4610d41104c0d11c0010c00000000f40079c0002c250001d0003b034005bc0013c670348b02c00001750000007d07634170340b044000008907413,
    0x4c2f0000b0f4110000014c00124006440002c000ad610000b824470000d05d0d10c0002c7f000df1940b0a42b00000164000000d07c1302c0005c25,
    0x34004640028c2b02ca700017184000341341c6b4f40b0340000011000000f42b254000bc0d0000b0001f1940d0ec000001305dbb000005fc250440d,
    0x44003041d02c00034000940b1fc00000610ac170003d04c00000000001102c0005c0039443044000002f02cbf000ad73c0b0000059c1d04c0052db7,
    0x5c1f0ac47000130000b7dc110a41702c6b04c003c41f2740d1240b000c50000d28c0031c0004c17044000000002c6507425000d3034000001f6bc97,
    0x4400000000001d0000002c110000d4cd3d00017454000741f000000000b000000f40b034000001122413034000012500000000000bc0b0007f,
    0x940b00000044bf77c0070400000000441f0341d124005ed0d0ae0904c000d44f0340b000001c40d02c25164000014b0000034c0002c0d694000000b,
    0x2c0d000290000b000000342b4dc6b0001137c0b0000005c1302c006141d0016f4041304400094000bc670ed5138c0d000b320c29000650341302c00,
    0x2c000001d00011164001adf3124172fc000bc0002c000000002c1307c430000020d610001d0351905ce93ec0b0346d04c95000000001709435,
    0x756739400404000002b0440d2b40b0001d0000d04447000001c4000d40013c2902d5b0001700011000000000b000002241102c000942907c0d04c00,
    0x13d751940d05c8304c1f02ca7035cd0000b00013000290f49d6ec000940b000005440d10c000000004c000001741c0002c0d044130000b31db10342f,
    0x1300000035a30006b0a4890bc3b13d3d0004702c1d000110940d82c000ac00001df0001d02cb57ac0d0440004c3d25c0007c0b1850f0ac001fc47,
    0xa43d0000b0005319413000710000d0002b02c0005c0d07c0b045c90014b04c1d0000002c002fc3b0000b0341105c1d19cd346c830001102c0000017,
    0x2cc2b04c001640d02c001941f0002900137044530000b0000004c170341f000000ec00034000000b05c000004f04591000670342f224ad000110d4fb]⟩,
  ⟨278291, 1158, 358, [
    0x2cc2b04c001640d02c001941f0002900137044530000b0000004c170341f000000ec00034000000b05c000004f04591000670342f224ad000110d4fb,
    0x2922c0002c0010c170000b6ec00094000001104c0079c00000000440d02c130000007dd3000000010d02c0010c000440b0000d0f40037c350004f,
    0x3417000000007f0000b0bc250740002c890ec0052c110345907c0b0741704400000003ec0d000296341707c0d02c130002b0ec670009d000470000d,
    0x110015d001c90350d05cc102c430002f19537000130441700000000250340b045cf1240b07525464130010f000df34d154e41104c000d40b14c00,
    0xb07c11000000000d000bf00000000000002931c000000d1851b1b4000000d0000b0ec1307c0002c29001010ac0004c1d0000002c350000007c0b,
    0x2cef0000022c0b0ac2904c0005c000000d0000b394000943502c000ec2f0004904c5300083034000000004c00034d30003d16417694000442f02c1d,
    0x2c3d04c170442f25c0011c006640003425075c102c002741102c002540003461000113a40d00000000000000b7dc49000000740d0ec6704413,
    0x440d224000ac1f000000342914c0b0bc0000000000000d4430340000011074c102c0000000044715fc007f40b0000d38cfb02c0005c13034000001f,
    0x35250003b05c0002c110941f0000b000b50f40000175000131940b000115bc17314000000003400000003bc1702c1311c000000b0f57b00000,
    0x440000000000250f40d0001141c001b40d02c4904d3737c2f05c001c4650001d0005302d853041113c0034c00184000740b4e42f04c0d00067,
    0x43dcd0000b0441368c470001d0342b0440002c000003559c0b0ec2900000000000000d02c0004c000000b0001d000250000d0a400000a302c6b03400,
    0x67000000340002c890000004c2f14c1105c000340b2b4006bc0d38c0005c0000000044004640b0a40d000132cc8b000000001f001150749d05c00,
    0x3055b0000002c6120c110ac0b0000d0007110c000000d46c0025c5304c0002c0007400000007ac1307c4f02d070bc110000b05c0077d392fc000002b,
    0x3b0000019c0d1b40b0440007c7f02c0029c17044001641343c0b035510000005c130342510c110001d0000002c1f28c11034000000000013000e9,
    0x5c1d000ad0bc67001a30000002c1728dd30001f0000010c00001991240d0000b0ac000740b3ec17000650000000000000000440d20c1f0940b0a400,
    0x340b1b4001240007c000002f00013034bf5d5af18417034112d5e700000095910000b0000d001cd02c000440d075c10d48b0002502db70000004c0b,
    0x2dc911c2b3c40b034670004f0f40005d510d40b435cf0001d02c430002b03400000950a400000b304c0000011000350946b00013000110000002c29,
    0x1241302c00000001640d22c00000c500035045b10000002c0d000bf02c610000d59c000003d0001f0ed2514c250440b1ac290bda5034000001100000,
    0x16f05c005857b14c13000000000b3940d1641109400000000001d044c104ca702d4b00089034000004705c0b034000440002c6500000000174e4e3,
    0x7c0004c1d0a4002b53d02c0019c002cc0b034893a411000ef04df30a40b045c10340004c170000d0000000000434f102c7122c0007c0b0004f1b411,
    0x11c0d0000005c000f40003400000250740046c9502c000442b0355d0000000013044250000002c0011c1f0bc170000d075e70000b0006d0346500000,
    0x1330340b5fc000a41d7f5b122c0004cc702c0029c000bc0b074003ecad000250002b02c0005c000340b34c35634130341f694000440002dcf00043]⟩,
  ⟨282791, 1159, 364, [
    0x1330340b5fc000a41d7f5b122c0004cc702c0029c000bc0b074003ecad000250002b02c0005c000340b34c35634130341f694000440002dcf00043,
    0x2fc1f0ec430001102c0013c0d00000000000000d05c0b0003d000250bca300000000000003b11c0b37c1310c2905c00000000000004c000440d46417,
    0x250000d02daf044000000b034350006700000000000005313c112541d02c710000d000110000005cd302ca70006d04c0b00151394000002b03400,
    0x4449254000341d2cc0b04cad0010702c1f00000034250ec000000b2741138c0004c1f14c470441d0000d04c4902c2905c00000000008325c1d00000,
    0x74175bcb504d3d304001841102c0d0ec1d094674940d0001f000000ac171640b000000000b1ac8304417034000002f00000000000ac0013c0b11c13,
    0x4c0b045154340d0000005c35194110ac001c40019ce300017000000340007d0f0000b035eb5442b02c11404006648907c000340002c13000250000b,
    0x2c00000170440b61400094004cc95044130000b0001d0000002c130000d00017000110001d0004f0000041c3d00000000130000d6ec8b07c0002c00,
    0x340002c004f4291c41f0d41305c00034113bc0010c0002c0005ce902dcd0001d000490440d14c2f0d47f0000d0000b00025000170a44f04dd30000d,
    0x95750001303411000000000b2b57b04c2f000e5000670f4c1184000340002c6b0000004c0034c000a40b000112540002c5311c0020d0f0009d,
    0x94000001f314000000d02c3b04c000000b1fcf10440007c0d0bc000000b0000d11c000000013c1100025000130000002c117dc1d0340b464296c5c9,
    0x274000002f0000005c3528c1f044000000d000b302c000a46520c0004c1f46c001ac172b4c102c130f4000002b0341731d010440b000b53ec8b7ac00,
    0x37c0b0002b0d57f20c000a55b0000002c00000000740b0000005dd30ec2b0341302c000740d0000b044000000045400000000000d02c1309400,
    0xd000002fc0002c00034007cc00000000ac000000b404000340000013274000940005ca30000b0004907c110000d0001704ce3094110343d0ec00,
    0x13d035df02c0013c000000b41c130a40004449314001b42f644b50946702c0007c00000350007f035cf02c00044000340b25c6113de70001104c1d,
    0x6dc2f074290003504c0b0000d0000002d610000d07400000000940b0440019c0014c000004907c8904c000000002c000440005c13074b30000d07c00,
    0x135ec0d184c10000007d0f02c00000000001700011000000acc5000590440b05c0d0bc0b634ad10c950945304daf3940d000000000056c0b03411,
    0x5c0b0000003400000130002b000170000007c8b03400044001ac0d0000004c290440b0ac650001702c0d0000011c00000000001102c29000000000b,
    0x2c0004c110000b000490000068c0d094007240b0000d0ac0002c00404000000025c1d04ce5000650003d034fb000598240007400044000000002c1f,
    0x2d6f0000d3c42b0a41d0ec1f05d0d2d46104c0002c0046c0002c434cc13000350344f00000000000001d4dc0b0007f0340000017044831648b,
    0xa4000d43b074000446d000000000b04c000000007c0005c295d4110000d52d5d02c2f19c1100000000c50000b00013001b702c0d454ef0740004400,
    0x343505c252cc6d224e902d99000290340b001cd0001303400000000000b0ac3b0744359c0d044970bc1305c0d1940002c00000a304c0b0ac170000d,
    0x290f413000000347100011000974542b0018502c000943b14c000000003411275b15441302ca70441d434000000004c000000b000000004300000]⟩,
  ⟨287364, 1161, 362, [
    0x290f413000000347100011000974542b0018502c000943b14c000000003411275b15441302ca70441d434000000004c000000b000000004300000,
    0x1d0440b05c4f0000d04d5d5fc110004902c25000000000b0002b0f4000000d04c0002c6182c2907c0b04c1700000000001944f0340002dc9000bf,
    0x53000e50440002c3b2fc9507c1d0440d1ac3d11c0b000002b4007dc290000031c11000000340b19c3b000000341f0000000059194000000020c13,
    0x4c00000c502c43405d30000b09489000110341f05c9722c1d0000029c0002c35034fb044000bc0d2cc2902c4305da54940b4ddc11240d7ac0007417,
    0xd40d000ef5bc0007c0b0340052da302c130745900000000b50340b000000d4000a43d000000000005ce919c0002c0d000130951938c00035fd00000,
    0x18400034c1094494e4170441302c0007c00001750444f04c000001d73c000000b000000000b28c1103400000000ac25034110002f29c9704c0b0003d,
    0xb0001d000130ac7f0000d044000f44704c0d00000001df001b76bc170002f2fc0b0005904c1f02c17000c70edbb000000440002c1d0000d7cc0b,
    0x2d4b2740d0ec0b0019105c6b034000744343c0b000000001102c0007c00000000000d11c2f0ec00094000441307c000740d000000000010c9502c00,
    0x7c0002c17034000001d1ac000012511c2f000000340002c000440d02c000f4177340000025000130000d2fc110000b1b40031c0007c110007f2d400,
    0x6505c0b000000441d0000d0001305c29000004640002c130017b000f10ac1f0340b044000000002c170017f0941100000,
    0xe90004f10c0d1ac5302df3000470000b0a411000006bd5b000710340b0947f001bb03400000000a50f000000000002c1f034250000b0002f37ca3,
    0x1f31cbf0001d0002f4e400614133bc000000002c1100089000610000d04400164c50f40002c1d254000ec00695010940019c0b05c008241d04c11,
    0x34110000b2248b04dcd10c476c4000341d02c130a4000340b0001f00000000000441702c0d1b40004c0b25c0d00017000df124114cc0002c350000d,
    0x134541156d6102c00074000000046c1f000000940b000000d44905c000344710c1f000000000b0000020d8d04c000bc4f0003d0450d05ca70a42b,
    0x4dcb51ace302c110000d0000b00000000250004f28c1d0000d0002f0000002c0d0006d05c1d001cf0000002d4b0a4000000b000000342f0440000059,
    0x4c71000000440b000000002502c0d05c000010d1240004c0b2244705c1d0ac2504c11035071fc0079cb302c1d07cc500000304350000004429,
    0x44c113db1275f7074002241702c2f68c000340004c430f435454650001159c0b034df0000b0440d1260b0ac003c4000002905c000000d07c0b19ce5,
    0x1ac0b0002b000250001f034110000004c00124170000031ce9034254642b0001105c0b164bf0a40002c43001610bc0d74c534941d02c00034003140b,
    0x2c25034000a40b6ec00000000741173c000000b2cc130d5fd02c0007400000001955d2d400000170341100000000000340007c0004c000000002c61,
    0x4f02c1304575000613a40d12400044000ec0d0001702c000000002c8b000000bc11000130740028c00664000000b04c000ad1b000596dc0d2b400,
    0x404000000d25c000a4ef04c1f0340b05c11094000006d304000000056c1f1244302c0d0442b41c53001df04c0b1c57b4640d02c350f4170a40003425,
    0x19c53034000001102c00000005740b001f70343505c2b0000d0000b000d30000007c00194000000d074290001102c000d4000000b000251ac13,
    0x4c4705c676149d545070440037c0d0001714cc502c0d184a707c000ec00000593042910c7102c1100000034000004f000110bc0b074130001700000]⟩,
  ⟨292039, 1162, 364, [
    0x4c4705c676149d545070440037c0d0001714cc502c0d184a707c000ec00000593042910c7102c1100000034000004f000110bc0b074130001700000,
    0x2b4000bc0b0000d0000056d33044b34e41302d7f0002b11c0b00013034000748b07c0002c172250d0000b001a50002943c130353d3c46b02c0000000,
    0x1fc4307cdf05c0002ddf000130000000000000351240b04c11000007040d4540013c000002907c0b07453044170003b29c350000d1ac9504c2b07c00,
    0x34000a43d02c1319c0007c0b0010f0340004c000004703471044004949502cb30001d1840d04c3d0002502c0d25cc71940b074000001114df30000d,
    0x5d59100000394000340b0001d04c0002c290447105c000bc000000b0ac00034e97ac000000009400184000001302c7f0d42f1acc10add30001112417,
    0x6d0741f41c0d19c0002c000ac000d4110f4000000d0ec17044d30000b0017b0000b0001305cad0000046c35045c900000034000740b0941f,
    0x31c0b2b400000b30bc170f4677041f0000d00000000111fc1300000000000441f0740b5758d0350102cbf0a4830340005c000003b02c00194130000b,
    0x2c110011b1c40b000000ed370ac00000fb0340b07d330440002c970941300000034000016f0000d00017544000d46b79d3d04c110000d0002902c00,
    0xd02c11000c700000034000001320c00000000002f02c17035d302c000004f2d4000740000000614000001f0940b0000000000044000340004c65,
    0xbc00034170001104c00000590a40b0d55d00013000c16dc00000006ec3b0001702c8b0000000000034df0940b074000348902c13000000444700000,
    0x130000007c2f0440002c0d05c0022c0b68c0d0ac590001d05c110000b5448900000000110002507cf10002b04c0002c0029c173ec0b0000d04400,
    0x44003140d2d417000130000003453094000740002c0000000464d343c1104c2b1fc0d0940002c2f000a31ac000001f0ec0d7f40b1b4470000003449,
    0x13c0004c0b034006649d00011000350000002c1f034005fc0b04c0d10cef20c110000002ce3164000440b0000000000000001b42905c1f02d610f4b3,
    0x441d0020902c00001b70f40d13c002cd0104c0b000000bcdf00025000130001722d070000b1ac11035af0001716400000000001d0000000000,
    0x14c2502c0d254000000b0d4000448b00125000670000031ce30340002c29000110343d0ac6b52c3502d191b4130740b034000002905c007dc3b,
    0x7f4a300000000000000b11c350000002c1110d1537c13094000740b0000d0000000161044007041f000130004f02c000001711c0d04c7f0000000167,
    0x34000001354400000110a42b02c000340005c1d1953903400001df07ca705c0b001330ac0b10c00000002540d07c1104c0000000000000000b05c0d,
    0x7c0b0ec000000003447044173a4000018d00000044000ac29000000001d0348304c0b1ac3b0001102da504c61000bf7341105c0002c002d4ef0000b,
    0x2c2f0000004c0b38c0d2ccb5044290007f0000b000490000d02c00000007ac0d05d670006d56c1d4541f16400000000006104400034250001d02c13,
    0x4c2902d7f37c005ec2500000000171c40d000536c53702c1134c4302c0000000000000bc0003417000000453d0340b82c1f09400000130003b28c00,
    0x1f000890950700035074000000b0ec13034c10001752ca30441313c650ac9702c00000000d40d0002f0000b644250001302c000000d0ac1f00000,
    0xd0009711c000d40002c130000005c0b044000001d04c000341f19c0b1b4006bc0046c1d0f48b3140029c000440d02c000007f79c0b0341100000,
    0xec2b034000001300000124001844f0001f04c1102c0005c000002b0443d1ac1d0001f0000002c0003429464b52241d035bb5840b000430bcfb14c00]⟩,
  ⟨296799, 1164, 371, [
    0xec2b034000001300000124001844f0001f04c1102c0005c000002b0443d1ac1d0001f0000002c0003429464b52241d035bb5840b000430bcfb14c00,
    0x5c0b000ef074290000d04d4b0001702c0d000110000b000001246b044670a42f02c25000002740b05c13001cf31400001850003d02c0d49411,
    0xac110000d1243502d6f0000003400000000003b0000b0446d000e504c0007cbf0440d434170000b0bc0013c3d0000007c0d000110011b094f103443,
    0xf4c70001102c00000000000b0740079e1d0000003400000134dc0d0756102c00000130d41f38c001940d02c17000004cc0b000250440007c1300000,
    0x124c5724000d4110000b7cc0014c0d02ce52b46d0000d074000f40b0001318400000676ec0005d5d000000340002c710940004c890bc000440029c53,
    0x11c00000356c40d044000009d02c130006d0000005c000002500011034e30ec0b20cb50340b2cc0011c4f1c42505c0010c1d03400000005ec0b04417,
    0x440b0001f000e904c00314000be092240020c13094f107c6b4e4170000d000000000b1fc530446102c000740000065001c10a40d02c00000000ec0b,
    0x2c13074a30ac0b5d417000111b449034250a40b074000347f02c004341f00011000000000d11c000440022c0d04c0005c3b2d4000742b1258d02c0d,
    0x1641702c0041c000341329c002741114cef0000068c0002c8b001fd02c17034000002507c0019c000ac110000077c0b000001642f0000052c3d224ad,
    0x4c00044951240d05c3d0000b04400305910a4ad3ec0d04c53001150000d02c1104c4700000075c907c0b0f4830000002c2b034653940013c00,
    0x3bc0010c171b4250000002c000002b0000b0006b04cdf00000314257ac0b0001307c1d0442f035990009d000000340002d1b074000000b434000a400,
    0x38c2507c0014c00000110001d05daf04c2f0340002c000000005c590000000000034970000002c0d000670001d0a411000000000b0ec0d0000007c00,
    0xd1940b0741725c43034610ecdf43c6b02c00044130000b035390017f000354dc0002c004f4112d40b001850000d000114560b04c0002c4f00029,
    0xd400034130007102c0000000044000000007c004640b00000000f159c2f0d400074c72fc130000b0343d2746774c00034290440005c000002f00025,
    0x2c1f05c2f04c0b0009d000000000d0006163411224000000002c3b04c17000000a40013c1d02c000001720c0b2540011c001640d0ac1f,
    0x1d0000d04c0014c0b094000341f02c00000a334c003943b0440b05c350001f11c0d07400001a531c000ac1102d0d7ac0d000000001105c6d03413,
    0x4c0059c2b035b7000000000002c1d0000004443034531640013c0d0d42b0000b0010705c0b0011938c0d00000044c50bc1700047000130000b001f7,
    0x7240b0940043cad0a43b3bce54940d1941305c1179c0d0001d000130444905c000000b0015177c0002c3b0341f00000044137346d02c2f0a4c105c0b,
    0x2c00000000000b000bf0001300000000000740b0001104d0102c3503400044e3000000340018400164256c429000491c46d0341f0000004c0002c11,
    0x1102c0007c130006b2557f2242f0000004c176140002c000001d02c0d0015b044290002b04c0007c00000000000b22e1d37c0d31c007cc00001c1,
    0x34002d4111fc00164000000004c0b03400000000ec000342b0000022c4343c0002cf10000d1c417584490000b0bc1f0ac0002c000441d001150940d,
    0x77c110340002c00000000740b1641f82417000003edcd04c0b035390942b14c294dc130006d000000ec0002c0010d910940b04435404c7,
    0xa4000bd0d0440d000e30000005cf10000002c2b0000d07411094002fc0d0bc132cc1102c00000000009d11c00000000000b0341719c130443d,
    0x440041c0b00061000005bc2f5456707c0d02c1d4cd1b05c0b0940019411000000000002d25034000000b705cf034000000004ca70000002c2b00000]⟩,
  ⟨300000, 1165, 240, [
    0x440041c0b00061000005bc2f5456707c0d02c1d4cd1b05c0b0940019411000000000002d25034000000b705cf034000000004ca70000002c2b00000,
    0x28c6b05c000f42902c4f0001131c1300017034000000b68c000007f0001d22c110353d000003940b0442b05c2f0000000083000000a40d2541704c00,
    0xd0459902c1d04c490340b000111fc3b34c130010f5d4350340007c0002c00000830001714c1d04c1102db707c0d0000b0bc130ac000341d00000,
    0x741303495044433a40b000711640002c1d000001843d824000000b000000bc6d000110940046c2b034000ec1702c00034000005307d5b0002900067,
    0xbf1248329c0013c130740d02cad000110000d73c000a55d000001b4b304c0b314000440b05c005bc1f000000000059c000008b13c0082c0b00151,
    0xb04c0d000000941100043035913ec003949705c1d0000004c00000251640022c0b04c1d0009502c000bc0005c116bc0d0000002cc1000000340b,
    0x2c1f000250340b000000440000000635196ec0b0341f0bcf102c0d0013300013000ad56c7f0001105c0d000007ac1d00011000350003b3a41f02c00,
    0x2cb319ce507417000000440d04c3d000000000d02c004341f02c00000c74f539001f75ec4773400034650000b05c000443d0005310c0000000,
    0x10c17000290000d0bc00000001fc0b4941f000250ac1313c1179c8903417000ef02c1f035a50003b000130440b274a30009502c1d04ca70006b72400,
    0x25c000001320c2b0000002c49075fd0000b1b4a7000002cc17044000740b0002b0ec00464130000000000000110006102c650000d1240b1ae0b00000,
    0x34000001710c000006704c0009400034470443502c2f034c1164003a40007c1704d5143c0d02df30010104c0d0442f07c350000b00025000110000d,
    0xbc000ac0b04c49034250022305db10000002c11000290000b05d2504400035850005902c1f000710000b0015d0003d0441d094170000002c0018413,
    0x4c3d000fb0941702c0d0a400000e311c00274000000b14c0d00000000000440d74c7f000000ac0b00000074e52fc250d4000006b0341322c6500011,
    0xa4110740002c4f1b4951840b19c000000d0d40007483044290ac130000002dcf044470ec000342f0000002c00034350000b07c1105c00000000015b,
    0x14c6538c110000005c0b000136dc2902c350342f2b40004d995740b0ec0007400034170ac000000d094003040002c170006b000000440d04c0000000,
    0xd1b400194112fc3d0341f02c0025cc504c00164000ac000340005c1f0000b0000013c0b04c00074004cc000d40d1acb56ec00001f30340b00000]⟩
]

set_option maxRecDepth 10000 in
private def analyticRankIntervals : List NumericRankInterval := [
  ⟨300060, 1165, 1164⟩, ⟨300121, 1165, 1164⟩, ⟨300182, 1165, 1164⟩, ⟨300243, 1165, 1164⟩,
  ⟨300306, 1165, 1164⟩, ⟨300370, 1165, 1164⟩, ⟨300434, 1165, 1164⟩, ⟨300499, 1165, 1164⟩,
  ⟨300564, 1165, 1164⟩, ⟨300630, 1165, 1164⟩, ⟨300697, 1165, 1164⟩, ⟨300765, 1165, 1164⟩,
  ⟨300833, 1165, 1164⟩, ⟨300902, 1165, 1164⟩, ⟨300971, 1165, 1164⟩, ⟨301041, 1165, 1164⟩,
  ⟨301112, 1165, 1164⟩, ⟨301183, 1165, 1164⟩, ⟨301254, 1165, 1164⟩, ⟨301321, 1165, 1164⟩,
  ⟨301389, 1165, 1164⟩, ⟨301458, 1165, 1164⟩, ⟨301528, 1165, 1164⟩, ⟨301598, 1165, 1164⟩,
  ⟨301670, 1165, 1164⟩, ⟨301742, 1165, 1164⟩, ⟨301788, 1166, 1164⟩, ⟨301865, 1166, 1165⟩,
  ⟨301943, 1166, 1165⟩, ⟨302023, 1166, 1165⟩, ⟨302103, 1166, 1165⟩, ⟨302184, 1166, 1165⟩,
  ⟨302265, 1166, 1165⟩, ⟨302347, 1166, 1165⟩, ⟨302430, 1166, 1165⟩, ⟨302510, 1166, 1165⟩,
  ⟨302592, 1166, 1165⟩, ⟨302662, 1166, 1165⟩, ⟨302732, 1166, 1165⟩, ⟨302804, 1166, 1165⟩,
  ⟨302876, 1166, 1165⟩, ⟨302949, 1166, 1165⟩, ⟨303022, 1166, 1165⟩, ⟨303096, 1166, 1165⟩,
  ⟨303171, 1166, 1165⟩, ⟨303247, 1166, 1165⟩, ⟨303324, 1166, 1165⟩, ⟨303402, 1166, 1165⟩,
  ⟨303480, 1166, 1165⟩, ⟨303558, 1166, 1165⟩, ⟨303637, 1166, 1165⟩, ⟨303716, 1166, 1165⟩,
  ⟨303797, 1166, 1165⟩, ⟨303878, 1166, 1165⟩, ⟨303961, 1166, 1165⟩, ⟨304044, 1166, 1165⟩,
  ⟨304128, 1166, 1165⟩, ⟨304213, 1166, 1165⟩, ⟨304299, 1166, 1165⟩, ⟨304386, 1166, 1165⟩,
  ⟨304474, 1166, 1165⟩, ⟨304558, 1166, 1165⟩, ⟨304642, 1166, 1165⟩, ⟨304727, 1166, 1165⟩,
  ⟨304813, 1166, 1165⟩, ⟨304900, 1166, 1165⟩, ⟨304987, 1166, 1165⟩, ⟨305064, 1166, 1165⟩,
  ⟨305158, 1167, 1166⟩, ⟨305253, 1167, 1166⟩, ⟨305349, 1167, 1166⟩, ⟨305446, 1167, 1166⟩,
  ⟨305544, 1167, 1166⟩, ⟨305643, 1167, 1166⟩, ⟨305743, 1167, 1166⟩, ⟨305844, 1167, 1166⟩,
  ⟨305945, 1167, 1166⟩, ⟨306047, 1167, 1166⟩, ⟨306150, 1167, 1166⟩, ⟨306255, 1167, 1166⟩,
  ⟨306361, 1167, 1166⟩, ⟨306468, 1167, 1166⟩, ⟨306576, 1167, 1166⟩, ⟨306684, 1167, 1166⟩,
  ⟨306794, 1167, 1166⟩, ⟨306905, 1167, 1166⟩, ⟨307006, 1167, 1166⟩, ⟨307107, 1167, 1166⟩,
  ⟨307210, 1167, 1166⟩, ⟨307312, 1167, 1166⟩, ⟨307416, 1167, 1166⟩, ⟨307521, 1167, 1166⟩,
  ⟨307627, 1167, 1166⟩, ⟨307734, 1167, 1166⟩, ⟨307837, 1167, 1166⟩, ⟨307942, 1167, 1166⟩,
  ⟨308048, 1167, 1166⟩, ⟨308155, 1167, 1166⟩, ⟨308262, 1167, 1166⟩, ⟨308370, 1167, 1166⟩,
  ⟨308453, 1168, 1166⟩, ⟨308568, 1168, 1167⟩, ⟨308684, 1168, 1167⟩, ⟨308801, 1168, 1167⟩,
  ⟨308919, 1168, 1167⟩, ⟨309038, 1168, 1167⟩, ⟨309158, 1168, 1167⟩, ⟨309274, 1168, 1167⟩,
  ⟨309391, 1168, 1167⟩, ⟨309509, 1168, 1167⟩, ⟨309627, 1168, 1167⟩, ⟨309747, 1168, 1167⟩,
  ⟨309868, 1168, 1167⟩, ⟨309990, 1168, 1167⟩, ⟨310113, 1168, 1167⟩, ⟨310236, 1168, 1167⟩,
  ⟨310361, 1168, 1167⟩, ⟨310487, 1168, 1167⟩, ⟨310615, 1168, 1167⟩, ⟨310744, 1168, 1167⟩,
  ⟨310875, 1168, 1167⟩, ⟨311007, 1168, 1167⟩, ⟨311140, 1168, 1167⟩, ⟨311271, 1168, 1167⟩,
  ⟨311401, 1168, 1167⟩, ⟨311520, 1168, 1167⟩, ⟨311641, 1168, 1167⟩, ⟨311744, 1168, 1167⟩,
  ⟨311873, 1169, 1168⟩, ⟨312002, 1169, 1168⟩, ⟨312133, 1169, 1168⟩, ⟨312265, 1169, 1168⟩,
  ⟨312398, 1169, 1168⟩, ⟨312533, 1169, 1168⟩, ⟨312669, 1169, 1168⟩, ⟨312805, 1169, 1168⟩,
  ⟨312942, 1169, 1168⟩, ⟨313081, 1169, 1168⟩, ⟨313221, 1169, 1168⟩, ⟨313363, 1169, 1168⟩,
  ⟨313507, 1169, 1168⟩, ⟨313652, 1169, 1168⟩, ⟨313799, 1169, 1168⟩, ⟨313947, 1169, 1168⟩,
  ⟨314097, 1169, 1168⟩, ⟨314248, 1169, 1168⟩, ⟨314399, 1169, 1168⟩, ⟨314548, 1169, 1168⟩,
  ⟨314698, 1169, 1168⟩, ⟨314850, 1169, 1168⟩, ⟨315003, 1169, 1168⟩, ⟨315139, 1169, 1168⟩,
  ⟨315300, 1170, 1169⟩, ⟨315463, 1170, 1169⟩, ⟨315627, 1170, 1169⟩, ⟨315792, 1170, 1169⟩,
  ⟨315959, 1170, 1169⟩, ⟨316113, 1170, 1169⟩, ⟨316268, 1170, 1169⟩, ⟨316424, 1170, 1169⟩,
  ⟨316583, 1170, 1169⟩, ⟨316743, 1170, 1169⟩, ⟨316905, 1170, 1169⟩, ⟨317067, 1170, 1169⟩,
  ⟨317231, 1170, 1169⟩, ⟨317397, 1170, 1169⟩, ⟨317564, 1170, 1169⟩, ⟨317733, 1170, 1169⟩,
  ⟨317904, 1170, 1169⟩, ⟨318072, 1170, 1169⟩, ⟨318241, 1170, 1169⟩, ⟨318412, 1170, 1169⟩,
  ⟨318570, 1170, 1169⟩, ⟨318748, 1171, 1170⟩, ⟨318927, 1171, 1170⟩, ⟨319109, 1171, 1170⟩,
  ⟨319293, 1171, 1170⟩, ⟨319478, 1171, 1170⟩, ⟨319666, 1171, 1170⟩, ⟨319855, 1171, 1170⟩,
  ⟨320045, 1171, 1170⟩, ⟨320237, 1171, 1170⟩, ⟨320431, 1171, 1170⟩, ⟨320615, 1171, 1170⟩,
  ⟨320801, 1171, 1170⟩, ⟨320988, 1171, 1170⟩, ⟨321178, 1171, 1170⟩, ⟨321370, 1171, 1170⟩,
  ⟨321557, 1171, 1170⟩, ⟨321747, 1171, 1170⟩, ⟨321939, 1171, 1170⟩, ⟨322105, 1172, 1170⟩,
  ⟨322302, 1172, 1171⟩, ⟨322501, 1172, 1171⟩, ⟨322693, 1172, 1171⟩, ⟨322883, 1172, 1171⟩,
  ⟨323074, 1172, 1171⟩, ⟨323267, 1172, 1171⟩, ⟨323462, 1172, 1171⟩, ⟨323659, 1172, 1171⟩,
  ⟨323858, 1172, 1171⟩, ⟨324060, 1172, 1171⟩, ⟨324264, 1172, 1171⟩, ⟨324470, 1172, 1171⟩,
  ⟨324676, 1172, 1171⟩, ⟨324885, 1172, 1171⟩, ⟨325096, 1172, 1171⟩, ⟨325291, 1172, 1171⟩,
  ⟨325488, 1172, 1171⟩, ⟨325660, 1173, 1171⟩, ⟨325866, 1173, 1172⟩, ⟨326075, 1173, 1172⟩,
  ⟨326284, 1173, 1172⟩, ⟨326495, 1173, 1172⟩, ⟨326708, 1173, 1172⟩, ⟨326923, 1173, 1172⟩,
  ⟨327141, 1173, 1172⟩, ⟨327361, 1173, 1172⟩, ⟨327583, 1173, 1172⟩, ⟨327807, 1173, 1172⟩,
  ⟨328033, 1173, 1172⟩, ⟨328261, 1173, 1172⟩, ⟨328492, 1173, 1172⟩, ⟨328725, 1173, 1172⟩,
  ⟨328955, 1173, 1172⟩, ⟨329160, 1174, 1172⟩, ⟨329399, 1174, 1173⟩, ⟨329638, 1174, 1173⟩,
  ⟨329878, 1174, 1173⟩, ⟨330107, 1174, 1173⟩, ⟨330339, 1174, 1173⟩, ⟨330573, 1174, 1173⟩,
  ⟨330810, 1174, 1173⟩, ⟨331049, 1174, 1173⟩, ⟨331291, 1174, 1173⟩, ⟨331534, 1174, 1173⟩,
  ⟨331780, 1174, 1173⟩, ⟨332028, 1174, 1173⟩, ⟨332279, 1174, 1173⟩, ⟨332528, 1174, 1173⟩,
  ⟨332750, 1175, 1173⟩, ⟨333008, 1175, 1174⟩, ⟨333267, 1175, 1174⟩, ⟨333529, 1175, 1174⟩,
  ⟨333794, 1175, 1174⟩, ⟨334061, 1175, 1174⟩, ⟨334331, 1175, 1174⟩, ⟨334604, 1175, 1174⟩,
  ⟨334881, 1175, 1174⟩, ⟨335146, 1175, 1174⟩, ⟨335414, 1175, 1174⟩, ⟨335685, 1175, 1174⟩,
  ⟨335959, 1175, 1174⟩, ⟨336226, 1175, 1174⟩, ⟨336465, 1176, 1174⟩, ⟨336738, 1176, 1175⟩,
  ⟨337015, 1176, 1175⟩, ⟨337294, 1176, 1175⟩, ⟨337576, 1176, 1175⟩, ⟨337861, 1176, 1175⟩,
  ⟨338149, 1176, 1175⟩, ⟨338440, 1176, 1175⟩, ⟨338732, 1176, 1175⟩, ⟨339028, 1176, 1175⟩,
  ⟨339327, 1176, 1175⟩, ⟨339629, 1176, 1175⟩, ⟨339934, 1176, 1175⟩, ⟨340194, 1177, 1175⟩,
  ⟨340489, 1177, 1176⟩, ⟨340787, 1177, 1176⟩, ⟨341088, 1177, 1176⟩, ⟨341392, 1177, 1176⟩,
  ⟨341700, 1177, 1176⟩, ⟨342011, 1177, 1176⟩, ⟨342323, 1177, 1176⟩, ⟨342638, 1177, 1176⟩,
  ⟨342957, 1177, 1176⟩, ⟨343276, 1177, 1176⟩, ⟨343598, 1177, 1176⟩, ⟨343893, 1178, 1176⟩,
  ⟨344221, 1178, 1177⟩, ⟨344552, 1178, 1177⟩, ⟨344886, 1178, 1177⟩, ⟨345210, 1178, 1177⟩,
  ⟨345537, 1178, 1177⟩, ⟨345867, 1178, 1177⟩, ⟨346200, 1178, 1177⟩, ⟨346537, 1178, 1177⟩,
  ⟨346877, 1178, 1177⟩, ⟨347221, 1178, 1177⟩, ⟨347538, 1179, 1177⟩, ⟨347892, 1179, 1178⟩,
  ⟨348243, 1179, 1178⟩, ⟨348599, 1179, 1178⟩, ⟨348958, 1179, 1178⟩, ⟨349321, 1179, 1178⟩,
  ⟨349683, 1179, 1178⟩, ⟨350043, 1179, 1178⟩, ⟨350393, 1179, 1178⟩, ⟨350747, 1179, 1178⟩,
  ⟨351104, 1179, 1178⟩, ⟨351435, 1180, 1178⟩, ⟨351803, 1180, 1179⟩, ⟨352170, 1180, 1179⟩,
  ⟨352541, 1180, 1179⟩, ⟨352915, 1180, 1179⟩, ⟨353293, 1180, 1179⟩, ⟨353674, 1180, 1179⟩,
  ⟨354059, 1180, 1179⟩, ⟨354448, 1180, 1179⟩, ⟨354841, 1180, 1179⟩, ⟨355207, 1181, 1179⟩,
  ⟨355596, 1181, 1180⟩, ⟨355990, 1181, 1180⟩, ⟨356382, 1181, 1180⟩, ⟨356774, 1181, 1180⟩,
  ⟨357171, 1181, 1180⟩, ⟨357572, 1181, 1180⟩, ⟨357975, 1181, 1180⟩, ⟨358383, 1181, 1180⟩,
  ⟨358795, 1181, 1180⟩, ⟨359180, 1182, 1180⟩, ⟨359605, 1182, 1181⟩, ⟨360034, 1182, 1181⟩,
  ⟨360461, 1182, 1181⟩, ⟨360892, 1182, 1181⟩, ⟨361314, 1182, 1181⟩, ⟨361740, 1182, 1181⟩,
  ⟨362169, 1182, 1181⟩, ⟨362602, 1182, 1181⟩, ⟨363009, 1183, 1181⟩, ⟨363450, 1183, 1182⟩,
  ⟨363896, 1183, 1182⟩, ⟨364345, 1183, 1182⟩, ⟨364793, 1183, 1182⟩, ⟨365245, 1183, 1182⟩,
  ⟨365702, 1183, 1182⟩, ⟨366164, 1183, 1182⟩, ⟨366614, 1183, 1182⟩, ⟨367039, 1184, 1182⟩,
  ⟨367504, 1184, 1183⟩, ⟨367973, 1184, 1183⟩, ⟨368448, 1184, 1183⟩, ⟨368919, 1184, 1183⟩,
  ⟨369395, 1184, 1183⟩, ⟨369876, 1184, 1183⟩, ⟨370360, 1184, 1183⟩, ⟨370817, 1185, 1183⟩,
  ⟨371314, 1185, 1184⟩, ⟨371815, 1185, 1184⟩, ⟨372307, 1185, 1184⟩, ⟨372804, 1185, 1184⟩,
  ⟨373300, 1185, 1184⟩, ⟨373799, 1185, 1184⟩, ⟨374304, 1185, 1184⟩, ⟨374782, 1186, 1184⟩,
  ⟨375302, 1186, 1185⟩, ⟨375828, 1186, 1185⟩, ⟨376358, 1186, 1185⟩, ⟨376882, 1186, 1185⟩,
  ⟨377411, 1186, 1185⟩, ⟨377924, 1186, 1185⟩, ⟨378440, 1186, 1185⟩, ⟨378929, 1187, 1185⟩,
  ⟨379461, 1187, 1186⟩, ⟨379998, 1187, 1186⟩, ⟨380542, 1187, 1186⟩, ⟨381089, 1187, 1186⟩,
  ⟨381642, 1187, 1186⟩, ⟨382200, 1187, 1186⟩, ⟨382758, 1187, 1186⟩, ⟨383289, 1188, 1186⟩,
  ⟨383843, 1188, 1187⟩, ⟨384403, 1188, 1187⟩, ⟨384969, 1188, 1187⟩, ⟨385541, 1188, 1187⟩,
  ⟨386119, 1188, 1187⟩, ⟨386700, 1188, 1187⟩, ⟨387249, 1189, 1187⟩, ⟨387841, 1189, 1188⟩,
  ⟨388440, 1189, 1188⟩, ⟨389043, 1189, 1188⟩, ⟨389637, 1189, 1188⟩, ⟨390238, 1189, 1188⟩,
  ⟨390839, 1189, 1188⟩, ⟨391413, 1190, 1188⟩, ⟨392023, 1190, 1189⟩, ⟨392639, 1190, 1189⟩,
  ⟨393261, 1190, 1189⟩, ⟨393890, 1190, 1189⟩, ⟨394524, 1190, 1189⟩, ⟨395164, 1190, 1189⟩,
  ⟨395762, 1191, 1189⟩, ⟨396399, 1191, 1190⟩, ⟨397042, 1191, 1190⟩, ⟨397687, 1191, 1190⟩,
  ⟨398338, 1191, 1190⟩, ⟨398996, 1191, 1190⟩, ⟨399662, 1191, 1190⟩, ⟨400299, 1192, 1190⟩,
  ⟨400981, 1192, 1191⟩, ⟨401648, 1192, 1191⟩, ⟨402321, 1192, 1191⟩, ⟨403000, 1192, 1191⟩,
  ⟨403686, 1192, 1191⟩, ⟨404336, 1193, 1191⟩, ⟨405033, 1193, 1192⟩, ⟨405735, 1193, 1192⟩,
  ⟨406436, 1193, 1192⟩, ⟨407145, 1193, 1192⟩, ⟨407846, 1193, 1192⟩, ⟨408554, 1193, 1192⟩,
  ⟨409233, 1194, 1192⟩, ⟨409958, 1194, 1193⟩, ⟨410689, 1194, 1193⟩, ⟨411421, 1194, 1193⟩,
  ⟨412158, 1194, 1193⟩, ⟨412903, 1194, 1193⟩, ⟨413621, 1195, 1193⟩, ⟨414369, 1195, 1194⟩,
  ⟨415124, 1195, 1194⟩, ⟨415886, 1195, 1194⟩, ⟨416649, 1195, 1194⟩, ⟨417414, 1195, 1194⟩,
  ⟨418150, 1196, 1194⟩, ⟨418934, 1196, 1195⟩, ⟨419727, 1196, 1195⟩, ⟨420511, 1196, 1195⟩,
  ⟨421301, 1196, 1195⟩, ⟨422093, 1196, 1195⟩, ⟨422857, 1197, 1195⟩, ⟨423670, 1197, 1196⟩,
  ⟨424488, 1197, 1196⟩, ⟨425314, 1197, 1196⟩, ⟨426149, 1197, 1196⟩, ⟨426933, 1198, 1196⟩,
  ⟨427765, 1198, 1197⟩, ⟨428605, 1198, 1197⟩, ⟨429450, 1198, 1197⟩, ⟨430302, 1198, 1197⟩,
  ⟨431148, 1198, 1197⟩, ⟨431967, 1199, 1197⟩, ⟨432829, 1199, 1198⟩, ⟨433683, 1199, 1198⟩,
  ⟨434543, 1199, 1198⟩, ⟨435411, 1199, 1198⟩, ⟨436253, 1200, 1198⟩, ⟨437145, 1200, 1199⟩,
  ⟨438037, 1200, 1199⟩, ⟨438939, 1200, 1199⟩, ⟨439850, 1200, 1199⟩, ⟨440753, 1200, 1199⟩,
  ⟨441626, 1201, 1199⟩, ⟨442551, 1201, 1200⟩, ⟨443485, 1201, 1200⟩, ⟨444419, 1201, 1200⟩,
  ⟨445360, 1201, 1200⟩, ⟨446274, 1202, 1200⟩, ⟨447223, 1202, 1201⟩, ⟨448181, 1202, 1201⟩,
  ⟨449147, 1202, 1201⟩, ⟨450116, 1202, 1201⟩, ⟨451057, 1203, 1201⟩, ⟨452051, 1203, 1202⟩,
  ⟨453052, 1203, 1202⟩, ⟨454065, 1203, 1202⟩, ⟨455069, 1203, 1202⟩, ⟨456038, 1204, 1202⟩,
  ⟨457058, 1204, 1203⟩, ⟨458082, 1204, 1203⟩, ⟨459117, 1204, 1203⟩, ⟨460160, 1204, 1203⟩,
  ⟨461177, 1205, 1203⟩, ⟨462222, 1205, 1204⟩, ⟨463278, 1205, 1204⟩, ⟨464343, 1205, 1204⟩,
  ⟨465405, 1205, 1204⟩, ⟨466497, 1206, 1205⟩, ⟨467592, 1206, 1205⟩, ⟨468679, 1206, 1205⟩,
  ⟨469777, 1206, 1205⟩, ⟨470848, 1207, 1205⟩, ⟨471969, 1207, 1206⟩, ⟨473102, 1207, 1206⟩,
  ⟨474239, 1207, 1206⟩, ⟨475388, 1207, 1206⟩, ⟨476488, 1208, 1206⟩, ⟨477645, 1208, 1207⟩,
  ⟨478814, 1208, 1207⟩, ⟨479984, 1208, 1207⟩, ⟨481127, 1209, 1207⟩, ⟨482327, 1209, 1208⟩,
  ⟨483539, 1209, 1208⟩, ⟨484740, 1209, 1208⟩, ⟨485945, 1209, 1208⟩, ⟨487113, 1210, 1208⟩,
  ⟨488336, 1210, 1209⟩, ⟨489571, 1210, 1209⟩, ⟨490819, 1210, 1209⟩, ⟨492020, 1211, 1209⟩,
  ⟨493268, 1211, 1210⟩, ⟨494528, 1211, 1210⟩, ⟨495801, 1211, 1210⟩, ⟨497043, 1212, 1210⟩,
  ⟨498344, 1212, 1211⟩, ⟨499636, 1212, 1211⟩, ⟨500932, 1212, 1211⟩, ⟨502198, 1213, 1211⟩,
  ⟨503523, 1213, 1212⟩, ⟨504861, 1213, 1212⟩, ⟨506209, 1213, 1212⟩, ⟨507527, 1213, 1212⟩,
  ⟨508881, 1214, 1213⟩, ⟨510248, 1214, 1213⟩, ⟨511626, 1214, 1213⟩, ⟨513013, 1214, 1213⟩,
  ⟨514362, 1215, 1213⟩, ⟨515749, 1215, 1214⟩, ⟨517150, 1215, 1214⟩, ⟨518566, 1215, 1214⟩,
  ⟨519955, 1216, 1214⟩, ⟨521392, 1216, 1215⟩, ⟨522844, 1216, 1215⟩, ⟨524289, 1216, 1215⟩,
  ⟨525734, 1217, 1216⟩, ⟨527195, 1217, 1216⟩, ⟨528660, 1217, 1216⟩, ⟨530093, 1218, 1216⟩,
  ⟨531591, 1218, 1217⟩, ⟨533083, 1218, 1217⟩, ⟨534590, 1218, 1217⟩, ⟨536056, 1219, 1217⟩,
  ⟨537587, 1219, 1218⟩, ⟨539121, 1219, 1218⟩, ⟨540646, 1219, 1218⟩, ⟨542143, 1220, 1218⟩,
  ⟨543694, 1220, 1219⟩, ⟨545261, 1220, 1219⟩, ⟨546842, 1220, 1219⟩, ⟨548395, 1221, 1219⟩,
  ⟨549982, 1221, 1220⟩, ⟨551582, 1221, 1220⟩, ⟨553195, 1221, 1220⟩, ⟨554780, 1222, 1220⟩,
  ⟨556433, 1222, 1221⟩, ⟨558088, 1222, 1221⟩, ⟨559693, 1223, 1221⟩, ⟨561366, 1223, 1222⟩,
  ⟨563051, 1223, 1222⟩, ⟨564754, 1223, 1222⟩, ⟨566413, 1224, 1222⟩, ⟨568114, 1224, 1223⟩,
  ⟨569833, 1224, 1223⟩, ⟨571570, 1224, 1223⟩, ⟨573279, 1225, 1223⟩, ⟨575043, 1225, 1224⟩,
  ⟨576803, 1225, 1224⟩, ⟨578535, 1226, 1224⟩, ⟨580330, 1226, 1225⟩, ⟨582133, 1226, 1225⟩,
  ⟨583955, 1226, 1225⟩, ⟨585745, 1227, 1225⟩, ⟨587584, 1227, 1226⟩, ⟨589441, 1227, 1226⟩,
  ⟨591259, 1228, 1226⟩, ⟨593139, 1228, 1227⟩, ⟨595036, 1228, 1227⟩, ⟨596938, 1228, 1227⟩,
  ⟨598796, 1229, 1227⟩, ⟨600728, 1229, 1228⟩, ⟨601191, 1229, 1228⟩, ⟨601658, 1229, 1228⟩,
  ⟨602128, 1229, 1228⟩, ⟨602602, 1229, 1228⟩, ⟨603075, 1229, 1228⟩, ⟨603552, 1229, 1228⟩,
  ⟨603985, 1230, 1228⟩, ⟨604476, 1230, 1229⟩, ⟨604971, 1230, 1229⟩, ⟨605467, 1230, 1229⟩,
  ⟨605955, 1230, 1229⟩, ⟨606447, 1230, 1229⟩, ⟨606943, 1230, 1229⟩, ⟨607443, 1230, 1229⟩,
  ⟨607946, 1230, 1229⟩, ⟨608452, 1230, 1229⟩, ⟨608963, 1230, 1229⟩, ⟨609473, 1230, 1229⟩,
  ⟨609987, 1230, 1229⟩, ⟨610457, 1231, 1229⟩, ⟨610987, 1231, 1230⟩, ⟨611521, 1231, 1230⟩,
  ⟨612059, 1231, 1230⟩, ⟨612601, 1231, 1230⟩, ⟨613147, 1231, 1230⟩, ⟨613697, 1231, 1230⟩,
  ⟨614252, 1231, 1230⟩, ⟨614799, 1231, 1230⟩, ⟨615350, 1231, 1230⟩, ⟨615906, 1231, 1230⟩,
  ⟨616461, 1231, 1230⟩, ⟨616972, 1232, 1230⟩, ⟨617543, 1232, 1231⟩, ⟨618118, 1232, 1231⟩,
  ⟨618695, 1232, 1231⟩, ⟨619274, 1232, 1231⟩, ⟨619858, 1232, 1231⟩, ⟨620445, 1232, 1231⟩,
  ⟨621036, 1232, 1231⟩, ⟨621632, 1232, 1231⟩, ⟨622233, 1232, 1231⟩, ⟨622835, 1232, 1231⟩,
  ⟨623429, 1232, 1231⟩, ⟨623978, 1233, 1231⟩, ⟨624589, 1233, 1232⟩, ⟨625205, 1233, 1232⟩,
  ⟨625824, 1233, 1232⟩, ⟨626448, 1233, 1232⟩, ⟨627077, 1233, 1232⟩, ⟨627711, 1233, 1232⟩,
  ⟨628350, 1233, 1232⟩, ⟨628993, 1233, 1232⟩, ⟨629637, 1233, 1232⟩, ⟨630277, 1233, 1232⟩,
  ⟨630939, 1234, 1233⟩, ⟨631605, 1234, 1233⟩, ⟨632277, 1234, 1233⟩, ⟨632940, 1234, 1233⟩,
  ⟨633608, 1234, 1233⟩, ⟨634280, 1234, 1233⟩, ⟨634958, 1234, 1233⟩, ⟨635641, 1234, 1233⟩,
  ⟨636325, 1234, 1233⟩, ⟨637014, 1234, 1233⟩, ⟨637657, 1235, 1233⟩, ⟨638363, 1235, 1234⟩,
  ⟨639076, 1235, 1234⟩, ⟨639794, 1235, 1234⟩, ⟨640517, 1235, 1234⟩, ⟨641245, 1235, 1234⟩,
  ⟨641968, 1235, 1234⟩, ⟨642696, 1235, 1234⟩, ⟨643424, 1235, 1234⟩, ⟨644108, 1236, 1234⟩,
  ⟨644853, 1236, 1235⟩, ⟨645601, 1236, 1235⟩, ⟨646346, 1236, 1235⟩, ⟨647096, 1236, 1235⟩,
  ⟨647851, 1236, 1235⟩, ⟨648612, 1236, 1235⟩, ⟨649380, 1236, 1235⟩, ⟨650153, 1236, 1235⟩,
  ⟨650927, 1236, 1235⟩, ⟨651644, 1237, 1235⟩, ⟨652426, 1237, 1236⟩, ⟨653213, 1237, 1236⟩,
  ⟨654006, 1237, 1236⟩, ⟨654805, 1237, 1236⟩, ⟨655611, 1237, 1236⟩, ⟨656422, 1237, 1236⟩,
  ⟨657240, 1237, 1236⟩, ⟨658060, 1237, 1236⟩, ⟨658834, 1238, 1236⟩, ⟨659671, 1238, 1237⟩,
  ⟨660513, 1238, 1237⟩, ⟨661350, 1238, 1237⟩, ⟨662193, 1238, 1237⟩, ⟨663044, 1238, 1237⟩,
  ⟨663900, 1238, 1237⟩, ⟨664763, 1238, 1237⟩, ⟨665576, 1239, 1237⟩, ⟨666455, 1239, 1238⟩,
  ⟨667340, 1239, 1238⟩, ⟨668233, 1239, 1238⟩, ⟨669132, 1239, 1238⟩, ⟨670039, 1239, 1238⟩,
  ⟨670940, 1239, 1238⟩, ⟨671848, 1239, 1238⟩, ⟨672706, 1240, 1238⟩, ⟨673625, 1240, 1239⟩,
  ⟨674551, 1240, 1239⟩, ⟨675483, 1240, 1239⟩, ⟨676424, 1240, 1239⟩, ⟨677371, 1240, 1239⟩,
  ⟨678324, 1240, 1239⟩, ⟨679286, 1240, 1239⟩, ⟨680201, 1241, 1239⟩, ⟨681166, 1241, 1240⟩,
  ⟨682138, 1241, 1240⟩, ⟨683119, 1241, 1240⟩, ⟨684108, 1241, 1240⟩, ⟨685102, 1241, 1240⟩,
  ⟨686105, 1241, 1240⟩, ⟨687112, 1241, 1240⟩, ⟨688074, 1242, 1240⟩, ⟨689100, 1242, 1241⟩,
  ⟨690134, 1242, 1241⟩, ⟨691163, 1242, 1241⟩, ⟨692200, 1242, 1241⟩, ⟨693245, 1242, 1241⟩,
  ⟨694298, 1242, 1241⟩, ⟨695305, 1243, 1241⟩, ⟨696376, 1243, 1242⟩, ⟨697456, 1243, 1242⟩,
  ⟨698544, 1243, 1242⟩, ⟨699640, 1243, 1242⟩, ⟨700736, 1243, 1242⟩, ⟨701827, 1243, 1242⟩,
  ⟨702873, 1244, 1242⟩, ⟨703988, 1244, 1243⟩, ⟨705108, 1244, 1243⟩, ⟨706236, 1244, 1243⟩,
  ⟨707374, 1244, 1243⟩, ⟨708519, 1244, 1243⟩, ⟨709674, 1244, 1243⟩, ⟨710782, 1245, 1243⟩,
  ⟨711947, 1245, 1244⟩, ⟨713115, 1245, 1244⟩, ⟨714290, 1245, 1244⟩, ⟨715475, 1245, 1244⟩,
  ⟨716668, 1245, 1244⟩, ⟨717815, 1246, 1244⟩, ⟨719035, 1246, 1245⟩, ⟨720263, 1246, 1245⟩,
  ⟨721496, 1246, 1245⟩, ⟨722725, 1246, 1245⟩, ⟨723964, 1246, 1245⟩, ⟨725212, 1246, 1245⟩,
  ⟨726413, 1247, 1245⟩, ⟨727683, 1247, 1246⟩, ⟨728961, 1247, 1246⟩, ⟨730245, 1247, 1246⟩,
  ⟨731539, 1247, 1246⟩, ⟨732843, 1247, 1246⟩, ⟨734085, 1248, 1246⟩, ⟨735403, 1248, 1247⟩,
  ⟨736732, 1248, 1247⟩, ⟨738064, 1248, 1247⟩, ⟨739406, 1248, 1247⟩, ⟨740755, 1248, 1247⟩,
  ⟨742058, 1249, 1247⟩, ⟨743436, 1249, 1248⟩, ⟨744811, 1249, 1248⟩, ⟨746197, 1249, 1248⟩,
  ⟨747587, 1249, 1248⟩, ⟨748988, 1249, 1248⟩, ⟨750342, 1250, 1248⟩, ⟨751774, 1250, 1249⟩,
  ⟨753215, 1250, 1249⟩, ⟨754657, 1250, 1249⟩, ⟨756091, 1250, 1249⟩, ⟨757534, 1250, 1249⟩,
  ⟨758931, 1251, 1249⟩, ⟨760405, 1251, 1250⟩, ⟨761892, 1251, 1250⟩, ⟨763389, 1251, 1250⟩,
  ⟨764891, 1251, 1250⟩, ⟨766346, 1252, 1250⟩, ⟨767861, 1252, 1251⟩, ⟨769389, 1252, 1251⟩,
  ⟨770928, 1252, 1251⟩, ⟨772480, 1252, 1251⟩, ⟨774044, 1252, 1251⟩, ⟨775555, 1253, 1251⟩,
  ⟨777145, 1253, 1252⟩, ⟨778747, 1253, 1252⟩, ⟨780347, 1253, 1252⟩, ⟨781954, 1253, 1252⟩,
  ⟨783506, 1254, 1252⟩, ⟨785139, 1254, 1253⟩, ⟨786785, 1254, 1253⟩, ⟨788445, 1254, 1253⟩,
  ⟨790116, 1254, 1253⟩, ⟨791726, 1255, 1253⟩, ⟨793411, 1255, 1254⟩, ⟨795106, 1255, 1254⟩,
  ⟨796815, 1255, 1254⟩, ⟨798537, 1255, 1254⟩, ⟨800209, 1256, 1254⟩, ⟨801966, 1256, 1255⟩,
  ⟨803715, 1256, 1255⟩, ⟨805478, 1256, 1255⟩, ⟨807254, 1256, 1255⟩, ⟨808974, 1257, 1255⟩,
  ⟨810778, 1257, 1256⟩, ⟨812595, 1257, 1256⟩, ⟨814420, 1257, 1256⟩, ⟨816244, 1257, 1256⟩,
  ⟨818018, 1258, 1256⟩, ⟨819878, 1258, 1257⟩, ⟨821750, 1258, 1257⟩, ⟨823631, 1258, 1257⟩,
  ⟨825526, 1258, 1257⟩, ⟨827373, 1259, 1257⟩, ⟨829291, 1259, 1258⟩, ⟨831223, 1259, 1258⟩,
  ⟨833164, 1259, 1258⟩, ⟨835117, 1259, 1258⟩, ⟨837017, 1260, 1258⟩, ⟨839006, 1260, 1259⟩,
  ⟨840995, 1260, 1259⟩, ⟨842998, 1260, 1259⟩, ⟨844946, 1261, 1259⟩, ⟨846983, 1261, 1260⟩,
  ⟨849032, 1261, 1260⟩, ⟨851098, 1261, 1260⟩, ⟨853181, 1261, 1260⟩, ⟨855193, 1262, 1260⟩,
  ⟨857293, 1262, 1261⟩, ⟨859408, 1262, 1261⟩, ⟨861534, 1262, 1261⟩, ⟨863601, 1263, 1261⟩,
  ⟨865752, 1263, 1262⟩, ⟨867904, 1263, 1262⟩, ⟨870071, 1263, 1262⟩, ⟨872246, 1263, 1262⟩,
  ⟨874458, 1264, 1263⟩, ⟨876678, 1264, 1263⟩, ⟨878916, 1264, 1263⟩, ⟨881155, 1264, 1263⟩,
  ⟨883344, 1265, 1263⟩, ⟨885626, 1265, 1264⟩, ⟨887920, 1265, 1264⟩, ⟨890230, 1265, 1264⟩,
  ⟨892489, 1266, 1264⟩, ⟨894826, 1266, 1265⟩, ⟨897182, 1266, 1265⟩, ⟨899547, 1266, 1265⟩,
  ⟨901864, 1267, 1265⟩, ⟨904277, 1267, 1266⟩, ⟨906706, 1267, 1266⟩, ⟨909137, 1267, 1266⟩,
  ⟨911513, 1268, 1266⟩, ⟨913982, 1268, 1267⟩, ⟨916466, 1268, 1267⟩, ⟨918970, 1268, 1267⟩,
  ⟨921422, 1269, 1267⟩, ⟨923949, 1269, 1268⟩, ⟨926496, 1269, 1268⟩, ⟨929062, 1269, 1268⟩,
  ⟨931579, 1270, 1268⟩, ⟨934195, 1270, 1269⟩, ⟨936823, 1270, 1269⟩, ⟨939456, 1270, 1269⟩,
  ⟨942039, 1271, 1269⟩, ⟨944717, 1271, 1270⟩, ⟨947417, 1271, 1270⟩, ⟨950132, 1271, 1270⟩,
  ⟨952777, 1272, 1270⟩, ⟨955524, 1272, 1271⟩, ⟨958293, 1272, 1271⟩, ⟨961074, 1272, 1271⟩,
  ⟨963806, 1273, 1271⟩, ⟨966641, 1273, 1272⟩, ⟨969477, 1273, 1272⟩, ⟨972254, 1274, 1272⟩,
  ⟨975128, 1274, 1273⟩, ⟨978022, 1274, 1273⟩, ⟨980940, 1274, 1273⟩, ⟨983788, 1275, 1273⟩,
  ⟨986731, 1275, 1274⟩, ⟨989698, 1275, 1274⟩, ⟨992688, 1275, 1274⟩, ⟨995625, 1276, 1274⟩,
  ⟨998666, 1276, 1275⟩, ⟨1001705, 1276, 1275⟩, ⟨1004691, 1277, 1275⟩, ⟨1007785, 1277, 1276⟩,
  ⟨1010904, 1277, 1276⟩, ⟨1014036, 1277, 1276⟩, ⟨1017099, 1278, 1276⟩, ⟨1020272, 1278, 1277⟩,
  ⟨1023467, 1278, 1277⟩, ⟨1026606, 1279, 1277⟩, ⟨1029848, 1279, 1278⟩, ⟨1033094, 1279, 1278⟩,
  ⟨1036365, 1279, 1278⟩, ⟨1039586, 1280, 1278⟩, ⟨1042908, 1280, 1279⟩, ⟨1046255, 1280, 1279⟩,
  ⟨1049532, 1281, 1279⟩, ⟨1052902, 1281, 1280⟩, ⟨1056290, 1281, 1280⟩, ⟨1059705, 1281, 1280⟩,
  ⟨1063065, 1282, 1280⟩, ⟨1066521, 1282, 1281⟩, ⟨1070005, 1282, 1281⟩, ⟨1073425, 1283, 1281⟩,
  ⟨1076961, 1283, 1282⟩, ⟨1080515, 1283, 1282⟩, ⟨1083995, 1284, 1282⟩, ⟨1087582, 1284, 1283⟩,
  ⟨1091198, 1284, 1283⟩, ⟨1094840, 1284, 1283⟩, ⟨1098431, 1285, 1283⟩, ⟨1102111, 1285, 1284⟩,
  ⟨1105815, 1285, 1284⟩, ⟨1109467, 1286, 1284⟩, ⟨1113241, 1286, 1285⟩, ⟨1117010, 1286, 1285⟩,
  ⟨1120728, 1287, 1285⟩, ⟨1124568, 1287, 1286⟩, ⟨1128435, 1287, 1286⟩, ⟨1132242, 1288, 1286⟩,
  ⟨1136146, 1288, 1287⟩, ⟨1140077, 1288, 1287⟩, ⟨1143956, 1289, 1287⟩, ⟨1147951, 1289, 1288⟩,
  ⟨1151974, 1289, 1288⟩, ⟨1155932, 1289, 1288⟩, ⟨1160003, 1290, 1289⟩, ⟨1164095, 1290, 1289⟩,
  ⟨1168221, 1290, 1289⟩, ⟨1172270, 1291, 1289⟩, ⟨1176448, 1291, 1290⟩, ⟨1180650, 1291, 1290⟩,
  ⟨1184795, 1292, 1290⟩, ⟨1189061, 1292, 1291⟩, ⟨1193348, 1292, 1291⟩, ⟨1197568, 1293, 1291⟩,
  ⟨1201920, 1293, 1292⟩, ⟨1204903, 1293, 1292⟩, ⟨1207818, 1294, 1292⟩, ⟨1210848, 1294, 1293⟩,
  ⟨1213885, 1294, 1293⟩, ⟨1216943, 1294, 1293⟩, ⟨1220022, 1294, 1293⟩, ⟨1223029, 1295, 1293⟩,
  ⟨1226158, 1295, 1294⟩, ⟨1229307, 1295, 1294⟩, ⟨1232467, 1295, 1294⟩, ⟨1235555, 1296, 1294⟩,
  ⟨1238765, 1296, 1295⟩, ⟨1241992, 1296, 1295⟩, ⟨1245240, 1296, 1295⟩, ⟨1248416, 1297, 1295⟩,
  ⟨1251705, 1297, 1296⟩, ⟨1255016, 1297, 1296⟩, ⟨1258351, 1297, 1296⟩, ⟨1261613, 1298, 1296⟩,
  ⟨1265000, 1298, 1297⟩, ⟨1268397, 1298, 1297⟩, ⟨1271817, 1298, 1297⟩, ⟨1275164, 1299, 1297⟩,
  ⟨1278637, 1299, 1298⟩, ⟨1282134, 1299, 1298⟩, ⟨1285645, 1299, 1298⟩, ⟨1289081, 1300, 1298⟩,
  ⟨1292643, 1300, 1299⟩, ⟨1296218, 1300, 1299⟩, ⟨1299818, 1300, 1299⟩, ⟨1303345, 1301, 1299⟩,
  ⟨1306991, 1301, 1300⟩, ⟨1310661, 1301, 1300⟩, ⟨1314357, 1301, 1300⟩, ⟨1317979, 1302, 1300⟩,
  ⟨1321728, 1302, 1301⟩, ⟨1325493, 1302, 1301⟩, ⟨1329283, 1302, 1301⟩, ⟨1332999, 1303, 1301⟩,
  ⟨1336847, 1303, 1302⟩, ⟨1340723, 1303, 1302⟩, ⟨1344614, 1303, 1302⟩, ⟨1348425, 1304, 1302⟩,
  ⟨1352370, 1304, 1303⟩, ⟨1356344, 1304, 1303⟩, ⟨1360247, 1305, 1303⟩, ⟨1364268, 1305, 1304⟩,
  ⟨1368317, 1305, 1304⟩, ⟨1372393, 1305, 1304⟩, ⟨1376396, 1306, 1304⟩, ⟨1380533, 1306, 1305⟩,
  ⟨1384687, 1306, 1305⟩, ⟨1388869, 1306, 1305⟩, ⟨1392981, 1307, 1305⟩, ⟨1397228, 1307, 1306⟩,
  ⟨1401503, 1307, 1306⟩, ⟨1405688, 1308, 1306⟩, ⟨1410014, 1308, 1307⟩, ⟨1414365, 1308, 1307⟩,
  ⟨1418745, 1308, 1307⟩, ⟨1423055, 1309, 1307⟩, ⟨1427489, 1309, 1308⟩, ⟨1431952, 1309, 1308⟩,
  ⟨1436343, 1310, 1308⟩, ⟨1440879, 1310, 1309⟩, ⟨1445441, 1310, 1309⟩, ⟨1450023, 1310, 1309⟩,
  ⟨1454532, 1311, 1309⟩, ⟨1459184, 1311, 1310⟩, ⟨1463862, 1311, 1310⟩, ⟨1468455, 1312, 1310⟩,
  ⟨1473197, 1312, 1311⟩, ⟨1477971, 1312, 1311⟩, ⟨1482773, 1312, 1311⟩, ⟨1487499, 1313, 1311⟩,
  ⟨1492364, 1313, 1312⟩, ⟨1497256, 1313, 1312⟩, ⟨1502076, 1314, 1312⟩, ⟨1507048, 1314, 1313⟩,
  ⟨1512045, 1314, 1313⟩, ⟨1516948, 1315, 1313⟩, ⟨1522006, 1315, 1314⟩, ⟨1527098, 1315, 1314⟩,
  ⟨1532113, 1316, 1314⟩, ⟨1537266, 1316, 1315⟩, ⟨1542456, 1316, 1315⟩, ⟨1547681, 1316, 1315⟩,
  ⟨1552829, 1317, 1315⟩, ⟨1558135, 1317, 1316⟩, ⟨1563463, 1317, 1316⟩, ⟨1568714, 1318, 1316⟩,
  ⟨1574118, 1318, 1317⟩, ⟨1579559, 1318, 1317⟩, ⟨1584913, 1319, 1317⟩, ⟨1590422, 1319, 1318⟩,
  ⟨1595967, 1319, 1318⟩, ⟨1601438, 1320, 1318⟩, ⟨1607072, 1320, 1319⟩, ⟨1612726, 1320, 1319⟩,
  ⟨1618297, 1321, 1319⟩, ⟨1624034, 1321, 1320⟩, ⟨1629804, 1321, 1320⟩, ⟨1635486, 1322, 1320⟩,
  ⟨1641334, 1322, 1321⟩, ⟨1647221, 1322, 1321⟩, ⟨1653027, 1323, 1321⟩, ⟨1658988, 1323, 1322⟩,
  ⟨1664990, 1323, 1322⟩, ⟨1670912, 1324, 1322⟩, ⟨1676998, 1324, 1323⟩, ⟨1683128, 1324, 1323⟩,
  ⟨1689161, 1325, 1323⟩, ⟨1695368, 1325, 1324⟩, ⟨1701615, 1325, 1324⟩, ⟨1707788, 1326, 1324⟩,
  ⟨1714114, 1326, 1325⟩, ⟨1720482, 1326, 1325⟩, ⟨1726761, 1327, 1325⟩, ⟨1733211, 1327, 1326⟩,
  ⟨1739692, 1327, 1326⟩, ⟨1746096, 1328, 1326⟩, ⟨1752681, 1328, 1327⟩, ⟨1759304, 1328, 1327⟩,
  ⟨1765836, 1329, 1327⟩, ⟨1772549, 1329, 1328⟩, ⟨1779303, 1329, 1328⟩, ⟨1785977, 1330, 1328⟩,
  ⟨1792820, 1330, 1329⟩, ⟨1799710, 1330, 1329⟩, ⟨1806518, 1331, 1329⟩, ⟨1813510, 1331, 1330⟩,
  ⟨1820536, 1331, 1330⟩, ⟨1827476, 1332, 1330⟩, ⟨1834603, 1332, 1331⟩, ⟨1841652, 1333, 1331⟩,
  ⟨1848866, 1333, 1332⟩, ⟨1856132, 1333, 1332⟩, ⟨1863320, 1334, 1332⟩, ⟨1870702, 1334, 1333⟩,
  ⟨1878110, 1334, 1333⟩, ⟨1885443, 1335, 1333⟩, ⟨1892967, 1335, 1334⟩, ⟨1900537, 1335, 1334⟩,
  ⟨1908012, 1336, 1334⟩, ⟨1915685, 1336, 1335⟩, ⟨1923272, 1337, 1335⟩, ⟨1931059, 1337, 1336⟩,
  ⟨1938880, 1337, 1336⟩, ⟨1946616, 1338, 1336⟩, ⟨1954547, 1338, 1337⟩, ⟨1962531, 1338, 1337⟩,
  ⟨1970420, 1339, 1337⟩, ⟨1978504, 1339, 1338⟩, ⟨1986607, 1339, 1338⟩, ⟨1994817, 1340, 1339⟩,
  ⟨2003057, 1340, 1339⟩, ⟨2011217, 1341, 1339⟩, ⟨2019586, 1341, 1340⟩, ⟨2028012, 1341, 1340⟩,
  ⟨2036334, 1342, 1340⟩, ⟨2044868, 1342, 1341⟩, ⟨2053316, 1343, 1341⟩, ⟨2061969, 1343, 1342⟩,
  ⟨2070663, 1343, 1342⟩, ⟨2079278, 1344, 1342⟩, ⟨2088099, 1344, 1343⟩, ⟨2096983, 1344, 1343⟩,
  ⟨2097151, 1344, 1343⟩
]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma dyadic_rank_thresholds_valid : RankThresholds dyadicRankThresholds 0 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma candidate_count_30001 : (candidatePrefix 30001).card ≤ 3265 := by decide +kernel

private lemma prime_count_30001 : (30001:ℕ).primesBelow.card ≤ 3265 :=
  (primes_le_candidates 30000).trans candidate_count_30001

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
  exact le_min (count_from_intervals_valid _ 30001 300000 3265 (n+1) _
      (by decide) (by omega) prime_count_30001 dyadic_rank_intervals_valid) (wheel_prime_count_upper n)

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

def analyticCountingBound (n f : ℕ) : ℕ :=
  (104*(n-1) + 64*(∑ j ∈ range n.log2, countingBound (n/2^(j+1)))) / (f-64)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma analytic_rank_intervals_valid :
    NumericRankIntervals dyadicRankThresholds analyticCountingBound 300001 (2^21-1) analyticRankIntervals := by
  decide +kernel

theorem bridge_rank_product (k : ℕ) (hk₁ : 30001 ≤ k) (hk₂ : k ≤ 300000) :
    (k-1).factorial < ∏ i ∈ range (retainedCount k), rankBound (i+1) :=
  rank_intervals_bound _ 30001 300000 3265 k _ dyadic_rank_thresholds_valid
    (by decide) hk₁ hk₂ prime_count_30001 dyadic_rank_intervals_valid

theorem analytic_rank_product (k : ℕ) (hk₁ : 300001 ≤ k) (hk₂ : k < 2^21)
    (hEstimate : ∀ n f, 64 < f → 2^f ≤ n^64 → ((range n).filter Nat.Prime).card ≤ analyticCountingBound n f) :
    (k-1).factorial < ∏ i ∈ range (retainedCount k), rankBound (i+1) :=
  numeric_rank_intervals_bound _ _ 300001 (2^21-1) k _ dyadic_rank_thresholds_valid
    (by decide) hk₁ (by omega) hEstimate analytic_rank_intervals_valid

end Erdos137OddBridge
