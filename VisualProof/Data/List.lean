namespace List

/-- Two lists are disjoint when no member of the first occurs in the second. -/
def Disjoint (first second : List α) : Prop :=
  ∀ value, value ∈ first → value ∉ second

end List
