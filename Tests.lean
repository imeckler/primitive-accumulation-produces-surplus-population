import PrimitiveAccumulation

/-! Boundary cases and counterexamples to stronger, unintended claims. -/

namespace PrimitiveAccumulation.Tests

-- No workers means no output, even with land and an extended workday.
example : ¬ Feasible { land := 1, employed := 0, workday := 2, output := 1 } := by
  intro feasible
  have impossible := feasible.laborCapacity
  contradiction

-- Zero initial population cannot generate surplus at any stage.
example (t : Nat) : ¬ Profitable (expandingState 0 t) := by
  simp [Profitable, expandingState]

-- Land acquisition can support full employment without generating any surplus.
example (n : Nat) :
    FrontierStep (subsistenceState n) (subsistenceState (n + 1)) ∧
    (subsistenceState (n + 1)).surplusPopulation = 0 := by
  exact ⟨⟨by simp [subsistenceState], subsistence_feasible (n + 1)⟩,
    subsistence_no_surplus_population (n + 1)⟩

-- An extended workday alone does not imply surplus production.
private def idleLabor : State :=
  { land := 3, employed := 3, workday := 2, output := 3 }

example : Feasible idleLabor ∧ 1 < idleLabor.workday ∧ ¬ Profitable idleLabor := by
  exact ⟨by constructor <;> decide, by decide, by unfold Profitable; decide⟩

-- Unused acquired land makes surplus population strictly exceed surplus product.
private def idleLand : State :=
  { land := 7, employed := 2, workday := 2, output := 4 }

example : Feasible idleLand ∧ Profitable idleLand ∧
    idleLand.surplusProduct = 2 ∧ idleLand.surplusPopulation = 5 := by
  exact ⟨by constructor <;> decide, by unfold Profitable; decide, by decide, by decide⟩

-- Hiring can reduce surplus population even while land and output grow.
private def beforeHiring : State :=
  { land := 10, employed := 2, workday := 2, output := 4 }

private def afterHiring : State :=
  { land := 11, employed := 5, workday := 2, output := 10 }

example : Feasible beforeHiring ∧ FrontierStep beforeHiring afterHiring ∧
    Profitable beforeHiring ∧ Profitable afterHiring ∧
    afterHiring.surplusPopulation < beforeHiring.surplusPopulation := by
  exact ⟨by constructor <;> decide,
    ⟨by decide, by constructor <;> decide⟩,
    by unfold Profitable; decide, by unfold Profitable; decide, by decide⟩

-- With three initial workers, two expansions displace nine people in total.
-- Three remain employed; six form the surplus population.
example : Evolves (subsistenceState 3) (expandingState 3 2) ∧
    Profitable (expandingState 3 2) ∧
    (expandingState 3 2).displaced = 9 ∧
    (expandingState 3 2).surplusPopulation = 6 := by
  exact ⟨expandingState_reachable 3 2,
    expandingState_profitable (by decide) (by decide), by decide, by decide⟩

end PrimitiveAccumulation.Tests

/-- info: 'PrimitiveAccumulation.evolution_produces_surplus_population' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PrimitiveAccumulation.evolution_produces_surplus_population

/-- info: 'PrimitiveAccumulation.constructive_frontier_theorem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PrimitiveAccumulation.constructive_frontier_theorem

/-- info: 'PrimitiveAccumulation.positive_profit_requires_extended_workday' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PrimitiveAccumulation.positive_profit_requires_extended_workday
