import NK.Certificates.EvenApplications
#print axioms NK.Certificates.fourth_power_bound
#print axioms NK.Certificates.sixth_power_bound
open NK NK.RationalMomentCertificate
-- A zero width and a false upper endpoint cannot pass the numerical checker.
example : ¬ (PowerData.mk 0 0 0 0).UnitValid (10^24) 4 0 1 2 := by decide
example : ¬ (PowerData.mk 1 2 0 1).Valid (10^24) 2 1 1 2 := by decide
-- A supplied dyadic shift has to satisfy its exact domain inequalities.
example : ¬ (PowerData.mk 3 2 0 (2*10^24)).Valid (10^24) 2 1 1 2 := by decide
