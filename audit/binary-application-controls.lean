import NK.Certificates.BinaryApplication

open NK NK.Certificates

#print axioms binary_component

example : binary_component.base = 4 ^ 1000000000000000 := binary_component_base
example : binary_component.root = 2 ^ 1000000000000000 := binary_component_root
example : binary_component.f = (15494199041779 / 100000000000000 : ℝ) := binary_component_f

example : binary_component.f < (75806770413 / 100000000000 : ℝ) := by
  rw [binary_component_f]
  norm_num

example : (binary_component.base : ℝ) ^ (75806770413 / 100000000000 : ℝ) ≤
    binary_component.alphabet.moment binary_component.f := binary_component.moment_bound
