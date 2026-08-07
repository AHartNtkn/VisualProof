import VisualProof.Concrete.StepTags

open VisualProof.Concrete

private def jsonString (value : String) : String :=
  "\"" ++ value ++ "\""

def main : IO Unit :=
  IO.println ("[" ++ String.intercalate ","
    (StepTag.serializedAll.map jsonString) ++ "]")
