/-
Erdős 592 campaign — the audit. This file is the RECEIPT.

`#print axioms` on every banked result. A result is banked only if its axiom set is a subset of
{propext, Classical.choice, Quot.sound} — i.e. no `sorryAx`, no ad-hoc axiom.
-/

import Erdos592Frontier
import Erdos592Reduction

namespace Erdos592

-- §2 the relation itself
#print axioms ramsey_card_zero
#print axioms OrdinalCardinalRamsey.mono_card
#print axioms P_zero
#print axioms blue_neighborhood_isClique
#print axioms typeLT_eq_omega0_of_infinite

-- §4 the summand count
#print axioms indecCount_zero
#print axioms indecCount_of_lt_omega0
#print axioms indecCount_one
#print axioms indecCount_two
#print axioms indecCount_three
#print axioms indecCount_four

-- §5 the classification is a partition
#print axioms isPrincipal_of_isOpow
#print axioms gamma_unique
#print axioms frontier_exhaustive
#print axioms frontier_exclusive

-- §6 the known instances land where the literature says
#print axioms omega_mem_ClassC
#print axioms omega_sq_mem_ClassC
#print axioms nat_mem_ClassB
#print axioms omega_pow_four_mem_ClassE

-- §6 the open case, pinned and minimal
#print axioms omega_pow_three_open
#print axioms ClassD_nonempty
#print axioms three_le_of_indecCount_three
#print axioms omega_pow_three_least
#print axioms ClassD_least

-- §7 no monotonicity bridge
#print axioms no_monotone_bridge

-- reduction file
#print axioms galvin_larson_conjecture_false
#print axioms galvin_larson_conjecture_false'
#print axioms erdos592_reduces_to_ClassD
#print axioms erdos592_answer_dichotomy

end Erdos592
