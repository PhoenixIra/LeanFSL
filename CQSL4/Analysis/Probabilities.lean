import Mathlib.Topology.UnitInterval

namespace unitInterval

open Classical

noncomputable def conditionProbability (p : Prop) (i j : I) : I :=
    if p then i else j

noncomputable def conditionOneProbability (p : Prop) : I :=
    conditionProbability p 1 0


end unitInterval
