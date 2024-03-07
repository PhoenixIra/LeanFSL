import Mathlib.Topology.UnitInterval

namespace unitInterval

open Classical

noncomputable def conditionProbability (p : Prop) : I :=
    if p then 1 else 0


end unitInterval
