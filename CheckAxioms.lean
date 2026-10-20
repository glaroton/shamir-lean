import Shamir

-- Each theorem must depend only on Lean's standard axioms:
-- propext, Classical.choice and Quot.sound (no `sorry`, no `native_decide`).
#print axioms Shamir.reconstruct
#print axioms Shamir.shares_bijective
#print axioms Shamir.shares_uniform
#print axioms Shamir.shares_indistinguishable
#print axioms Shamir.Example.share_at_1
