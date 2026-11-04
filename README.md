# Surplus population at the frontier

A Lean 4 development of the model in [idea](idea). It proves that every feasible
state with positive surplus product has a surplus population, and constructs an
evolution from full employment at subsistence to such a state.

The development is abstract: the frontier is the cumulative amount of acquired
land. It does not use coordinates or assume a shape for the frontier.

## Build and check

The project pins Lean **4.31.0** in `lean-toolchain` and uses only modules shipped
with Lean. No Mathlib or other package downloads are needed once that toolchain
is installed.

```sh
lake build
lake test
```

The default build checks both the library and the tests. Warnings are errors,
including warnings about unfinished proofs. The tests also check the axiom
dependencies of the main theorems: only Lean's `propext` and `Quot.sound` occur;
there are no added axioms or admitted proofs.

Lake's commands and configuration are described in the
[official Lake manual](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/).

## Assumptions and units

All quantities are natural numbers for a common production period.

| Quantity | Meaning |
| --- | --- |
| `land` (`L`) | Total land acquired so far |
| `displaced` | Exactly `L` people, by the one-person-per-land-unit assumption |
| `employed` (`E`) | Employed people among the displaced |
| `workday` (`d`) | Available labor per worker, in blocks of `h` hours |
| `output` (`Q`) | Products made during this period |
| `surplusProduct` | `Q - E` products after employed workers' subsistence |
| `surplusPopulation` | `L - E` displaced people without employment |

One block is the fixed positive labor requirement `h` for one product. The model
normalizes that block to one time unit and restricts the common available
workday to whole blocks. It does not represent fractional workdays or each
worker's individual hours.

`Feasible` imposes three inequalities:

1. `Q ≤ L`: each land unit yields at most one product in the period. Longer
   working hours cannot reuse that land for another product in the same period.
2. `Q ≤ E * d`: each product requires one labor block at the fixed technique.
3. `E ≤ Q`: output covers one subsistence product for each employed worker.

Together these imply `E ≤ L`, so natural-number subtraction does not truncate
the population count. Acquiring land removes its former inhabitants' access to
subsistence land; there is no outside employment or reacquisition in this model.
The populations are aggregate counts rather than individually tracked people.

`Profitable` means `E < Q`: a positive physical surplus available for
appropriation. It is not monetary profit. Subsistence for unemployed people,
other production costs, population change, and a physical upper limit on working
hours are outside the model. In particular, if all `L` displaced people also had
to receive subsistence from this output, `Q ≤ L` would leave no positive surplus.

## What is proved

The core argument is:

```text
E < Q ≤ L = displaced
therefore 0 < L - E = surplusPopulation
```

The stronger accounting identity is:

```text
surplusPopulation = surplusProduct + (L - Q)
```

The counts use different physical units; this numerical identity follows from
the model's unit ratios. With full land utilization (`Q = L`), the counts are
equal. With unused acquired land, surplus population is larger.

| Theorem | Result |
| --- | --- |
| `positive_profit_produces_surplus_population` | Positive surplus in any feasible state implies surplus population |
| `positive_profit_requires_extended_workday` | Positive surplus requires `d > 1` |
| `full_employment_precludes_profit` | Employing everyone displaced leaves no positive surplus |
| `FrontierStep.population_balance` | Displacement increases by newly acquired land without double counting |
| `FrontierStep.fixed_employment_population_growth` | With employment fixed, each new land unit adds one surplus person |
| `evolution_produces_surplus_population` | Every profitable state reached from the subsistence baseline has surplus population |
| `constructive_frontier_theorem` | An explicit evolution reaches profitable states with exactly `n * t` surplus people |

All theorem names are in the `PrimitiveAccumulation` namespace.

## Evolution

`subsistenceState n` represents the position immediately after the initial
seizure: `n` land units have displaced `n` people, all employed, each with a
one-block workday producing one subsistence product. Both surpluses are zero.
It is not a representation of indigenous ownership before seizure.

A `FrontierStep` keeps acquired land nondecreasing and requires feasible
production in the next period. Employment and workday can change. `Evolves`
records any finite sequence of such steps; feasibility and cumulative land
acquisition are proved to hold along it. The general result has this signature:

```lean
theorem evolution_produces_surplus_population {n : Nat} {finish : State}
    (history : Evolves (subsistenceState n) finish) (profit : Profitable finish) :
    0 < finish.surplusPopulation
```

Profitability is an explicit condition, rather than a consequence of every
possible step. Acquisition alone need not produce surplus population: a step
can employ everyone newly displaced at subsistence. This counterexample is
checked in `Tests.lean`.

For a constructive witness, `expandingState n t` keeps `n` workers, gives them
`t + 1` labor blocks each, and acquires enough land to use all their labor:

```text
land = output = n + n * t
employed = n
workday = t + 1
surplusPopulation = surplusProduct = n * t
```

Lean proves feasibility at every stage, reachability from `subsistenceState n`,
and profitability whenever `n > 0` and `t > 0`. Each step acquires `n` new land
units, displaces `n` additional people, and adds `n` surplus people. This is one
explicit policy, with no upper workday bound; it is not asserted to be the only
possible evolution. Surplus population need not increase along other profitable
histories if employment also changes, as another checked example demonstrates.

## Files

- [Model.lean](PrimitiveAccumulation/Model.lean): quantities, feasibility, and the
  accounting and workday theorems.
- [Evolution.lean](PrimitiveAccumulation/Evolution.lean): transitions, finite
  histories, population balance, and the constructive evolution.
- [Tests.lean](Tests.lean): boundary cases, counterexamples, and axiom checks.
