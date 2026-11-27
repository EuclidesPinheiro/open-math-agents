import FormalConjectures.Arxiv.«0805.3777».TensorRank

namespace OMA.R_Arxiv_0805_3777_isGenericRank_three_odd_R1

open scoped Arxiv.«0805.3777»

-- The exceptional lower bound excludes rank at most 3p + 1 on a dense open set.
def H1 : Prop :=
  ∀ (p : ℕ), 1 ≤ p →
    ∃ U : Set (Holor ℂ [3, 2 * p + 1, 2 * p + 1]),
      IsOpen U ∧ Dense U ∧ ∀ T ∈ U, 3 * p + 2 ≤ T.cprank

-- The upper bound supplies decompositions with at most 3p + 2 summands.
def H2 : Prop :=
  ∀ (p : ℕ), 1 ≤ p →
    ∃ V : Set (Holor ℂ [3, 2 * p + 1, 2 * p + 1]),
      IsOpen V ∧ Dense V ∧ ∀ T ∈ V, T.cprank ≤ 3 * p + 2

theorem main : H1 → H2 → type_of% @Arxiv.«0805.3777».isGenericRank_three_odd := by
  intro hLower hUpper p hp
  have hDen : 0 < 4 * p + 3 := by omega
  have hNumerator : 3 * (2 * p + 1) ^ 2 = (4 * p + 3) * (3 * p) + (3 * p + 3) := by
    ring
  have hCeil : 3 * (2 * p + 1) ^ 2 ⌈/⌉ (4 * p + 3) = 3 * p + 1 := by
    apply Nat.le_antisymm
    · apply (ceilDiv_le_iff_le_mul hDen).2
      rw [hNumerator, Nat.mul_add, Nat.mul_one]
      omega
    · by_contra! h
      have hSmall : 3 * (2 * p + 1) ^ 2 ⌈/⌉ (4 * p + 3) ≤ 3 * p := by omega
      have hLe := (ceilDiv_le_iff_le_mul hDen).1 hSmall
      rw [hNumerator] at hLe
      omega
  rw [hCeil]
  obtain ⟨U, hUOpen, hUDense, hURank⟩ := hLower p hp
  obtain ⟨V, hVOpen, hVDense, hVRank⟩ := hUpper p hp
  refine ⟨U ∩ V, hUOpen.inter hVOpen, hUDense.inter_of_isOpen_left hVDense hUOpen, ?_⟩
  intro T hT
  exact Nat.le_antisymm (hVRank T hT.2) (hURank T hT.1)

end OMA.R_Arxiv_0805_3777_isGenericRank_three_odd_R1
