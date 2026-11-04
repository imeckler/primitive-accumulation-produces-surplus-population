import Lean.Elab.Tactic.Omega

/-!
An aggregate model of production on acquired land in one common accounting
period. One unit of land originally supports one person, so acquiring `land`
units displaces exactly `land` people. Employment is among those displaced.

Time is measured in blocks of `h` hours, where `h > 0` is the fixed labor
requirement for one product. Each worker has the same available `workday` in
these blocks. Each land unit can yield at most one product per period; it cannot
be reused within that period. Each employed person receives one subsistence
product. The model does not provide subsistence for the unemployed.
-/

namespace PrimitiveAccumulation

/-- Counts in one period; `land` is the cumulative amount acquired. -/
structure State where
  land : Nat
  employed : Nat
  workday : Nat
  output : Nat
  deriving DecidableEq, Repr

/-- The one-person-per-land-unit displacement assumption, by construction. -/
def State.displaced (s : State) : Nat := s.land

/-- People displaced but not employed in this model. -/
def State.surplusPopulation (s : State) : Nat := s.displaced - s.employed

/-- Products left after subsistence for employed workers. -/
def State.surplusProduct (s : State) : Nat := s.output - s.employed

/-- Production respects both capacities and supports all employed workers. -/
structure Feasible (s : State) : Prop where
  landCapacity : s.output ≤ s.land
  laborCapacity : s.output ≤ s.employed * s.workday
  subsistence : s.employed ≤ s.output

/-- Positive physical surplus, before any costs outside this model. -/
def Profitable (s : State) : Prop := s.employed < s.output

theorem surplus_product_pos_iff {s : State} :
    0 < s.surplusProduct ↔ Profitable s := by
  unfold State.surplusProduct Profitable
  omega

/-- Feasibility implies that employment is bounded by the displaced population. -/
theorem employed_le_displaced {s : State} (feasible : Feasible s) :
    s.employed ≤ s.displaced :=
  Nat.le_trans feasible.subsistence feasible.landCapacity

/-- Natural subtraction loses no people in a feasible state. -/
theorem population_partition {s : State} (feasible : Feasible s) :
    s.surplusPopulation + s.employed = s.displaced := by
  exact Nat.sub_add_cancel (employed_le_displaced feasible)

/-- Unused acquired land also contributes to the displaced, unemployed count. -/
theorem surplus_population_accounting {s : State} (feasible : Feasible s) :
    s.surplusPopulation = s.surplusProduct + (s.land - s.output) := by
  have land := feasible.landCapacity
  have subsistence := feasible.subsistence
  unfold State.surplusPopulation State.surplusProduct State.displaced
  omega

theorem surplus_product_le_surplus_population {s : State} (feasible : Feasible s) :
    s.surplusProduct ≤ s.surplusPopulation := by
  have accounting := surplus_population_accounting feasible
  omega

/-- The core argument: `employed < output ≤ land = displaced`. -/
theorem positive_profit_produces_surplus_population {s : State}
    (feasible : Feasible s) (profit : Profitable s) :
    0 < s.surplusPopulation := by
  have land := feasible.landCapacity
  unfold Profitable at profit
  unfold State.surplusPopulation State.displaced
  omega

theorem positive_profit_requires_employment {s : State}
    (feasible : Feasible s) (profit : Profitable s) :
    0 < s.employed := by
  by_cases zero : s.employed = 0
  · have capacity : s.output ≤ 0 := by
      simpa [zero] using feasible.laborCapacity
    unfold Profitable at profit
    omega
  · omega

/-- A workday of at most `h` hours cannot yield surplus at the fixed technique. -/
theorem positive_profit_requires_extended_workday {s : State}
    (feasible : Feasible s) (profit : Profitable s) :
    1 < s.workday := by
  by_cases extended : 1 < s.workday
  · exact extended
  · have day : s.workday ≤ 1 := by omega
    have capacity : s.output ≤ s.employed := by
      calc
        s.output ≤ s.employed * s.workday := feasible.laborCapacity
        _ ≤ s.employed * 1 := Nat.mul_le_mul_left s.employed day
        _ = s.employed := Nat.mul_one _
    unfold Profitable at profit
    omega

theorem full_employment_precludes_profit {s : State}
    (feasible : Feasible s) (full : s.employed = s.displaced) :
    ¬ Profitable s := by
  intro profit
  have positive := positive_profit_produces_surplus_population feasible profit
  simp [State.surplusPopulation, full] at positive

end PrimitiveAccumulation
