import PrimitiveAccumulation.Model

/-!
Frontier expansion and finite histories. A step permits acquisition of more
land and any feasible change in employment, workday, and output. It does not
assume surplus population or force profitability.

The general theorem is conditional on positive surplus extraction. A concrete
family of reachable profitable states then shows that the condition is
consistent and that surplus population emerges from a full-employment baseline.
-/

namespace PrimitiveAccumulation

/-- Immediately after the initial seizure: all `n` displaced people work at
subsistence, with neither surplus product nor surplus population. -/
def subsistenceState (n : Nat) : State where
  land := n
  employed := n
  workday := 1
  output := n

theorem subsistence_feasible (n : Nat) : Feasible (subsistenceState n) := by
  constructor <;> simp [subsistenceState]

theorem subsistence_no_surplus_population (n : Nat) :
    (subsistenceState n).surplusPopulation = 0 := by
  simp [subsistenceState, State.surplusPopulation, State.displaced]

theorem subsistence_no_surplus_product (n : Nat) :
    (subsistenceState n).surplusProduct = 0 := by
  simp [subsistenceState, State.surplusProduct]

/-- Land acquisition is cumulative; production in the next period is feasible. -/
structure FrontierStep (before after : State) : Prop where
  landMonotone : before.land ≤ after.land
  feasibleAfter : Feasible after

/-- Any finite sequence of frontier steps, including a history with no steps. -/
inductive Evolves (start : State) : State → Prop where
  | refl : Evolves start start
  | step {before after : State} :
      Evolves start before → FrontierStep before after → Evolves start after

theorem Evolves.feasible {start finish : State}
    (history : Evolves start finish) (initial : Feasible start) : Feasible finish := by
  cases history with
  | refl => exact initial
  | step _ transition => exact transition.feasibleAfter

theorem Evolves.land_monotone {start finish : State}
    (history : Evolves start finish) : start.land ≤ finish.land := by
  induction history with
  | refl => exact Nat.le_refl _
  | step _ transition previous => exact Nat.le_trans previous transition.landMonotone

/-- Displacement increases by newly acquired land, without double counting it. -/
theorem FrontierStep.population_balance {before after : State}
    (transition : FrontierStep before after) (initial : Feasible before) :
    after.surplusPopulation + after.employed =
      before.surplusPopulation + before.employed + (after.land - before.land) := by
  have beforePartition := population_partition initial
  have afterPartition := population_partition transition.feasibleAfter
  have monotone := transition.landMonotone
  unfold State.displaced at beforePartition afterPartition
  omega

/-- With employment fixed, every newly acquired land unit adds one surplus person. -/
theorem FrontierStep.fixed_employment_population_growth {before after : State}
    (transition : FrontierStep before after) (initial : Feasible before)
    (fixedEmployment : after.employed = before.employed) :
    after.surplusPopulation =
      before.surplusPopulation + (after.land - before.land) := by
  have balance := transition.population_balance initial
  omega

/-- Every profitable state reached from subsistence has a surplus population. -/
theorem evolution_produces_surplus_population {n : Nat} {finish : State}
    (history : Evolves (subsistenceState n) finish) (profit : Profitable finish) :
    0 < finish.surplusPopulation :=
  positive_profit_produces_surplus_population
    (history.feasible (subsistence_feasible n)) profit

theorem profitable_evolution_requires_extended_workday {n : Nat} {finish : State}
    (history : Evolves (subsistenceState n) finish) (profit : Profitable finish) :
    1 < finish.workday :=
  positive_profit_requires_extended_workday
    (history.feasible (subsistence_feasible n)) profit

/-- Keeping the initial workforce while extracting surplus requires more land. -/
theorem profitable_evolution_with_fixed_employment_expands_frontier
    {n : Nat} {finish : State} (history : Evolves (subsistenceState n) finish)
    (profit : Profitable finish) (fixedEmployment : finish.employed = n) :
    n < finish.land := by
  have capacity := (history.feasible (subsistence_feasible n)).landCapacity
  unfold Profitable at profit
  omega

/-- An explicit expansion policy: retain `n` workers, extend the workday by one
block each step, and acquire the land needed to use all their productive labor.
At stage `t`, acquired land and output are `n * (t + 1)`.
There is no upper workday bound in this witness family. -/
def expandingState (n t : Nat) : State where
  land := n + n * t
  employed := n
  workday := t + 1
  output := n + n * t

theorem expandingState_zero (n : Nat) : expandingState n 0 = subsistenceState n := by
  simp [expandingState, subsistenceState]

theorem expandingState_feasible (n t : Nat) : Feasible (expandingState n t) := by
  constructor
  · exact Nat.le_refl _
  · change n + n * t ≤ n * (t + 1)
    simp [Nat.mul_add, Nat.add_comm]
  · change n ≤ n + n * t
    omega

theorem expandingState_step (n t : Nat) :
    FrontierStep (expandingState n t) (expandingState n (t + 1)) := by
  refine ⟨?_, expandingState_feasible n (t + 1)⟩
  change n + n * t ≤ n + n * (t + 1)
  simp only [Nat.mul_add, Nat.mul_one]
  omega

theorem expandingState_reachable (n t : Nat) :
    Evolves (subsistenceState n) (expandingState n t) := by
  induction t with
  | zero =>
      rw [expandingState_zero]
      exact Evolves.refl
  | succ t previous => exact Evolves.step previous (expandingState_step n t)

theorem expandingState_surplus_population (n t : Nat) :
    (expandingState n t).surplusPopulation = n * t := by
  simp [expandingState, State.surplusPopulation, State.displaced]

theorem expandingState_surplus_product (n t : Nat) :
    (expandingState n t).surplusProduct = n * t := by
  simp [expandingState, State.surplusProduct]

theorem expandingState_profitable {n t : Nat} (workers : 0 < n) (later : 0 < t) :
    Profitable (expandingState n t) := by
  have positive := Nat.mul_pos workers later
  unfold Profitable expandingState
  dsimp
  omega

/-- A constructive evolution from zero surplus population to `n * t > 0`.
The initial population may be any positive size, and the stage any positive
natural number. Reachability and profitability are proved, not postulated. -/
theorem constructive_frontier_theorem {n t : Nat} (workers : 0 < n) (later : 0 < t) :
    Evolves (subsistenceState n) (expandingState n t) ∧
    Profitable (expandingState n t) ∧
    (expandingState n t).surplusPopulation = n * t ∧
    0 < (expandingState n t).surplusPopulation := by
  have history := expandingState_reachable n t
  have profit := expandingState_profitable workers later
  exact ⟨history, profit, expandingState_surplus_population n t,
    evolution_produces_surplus_population history profit⟩

end PrimitiveAccumulation
