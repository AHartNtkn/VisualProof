import VisualProof.Correspondence.StepTags

open VisualProof.Rule

private def jsonString (value : String) : String :=
  "\"" ++ value ++ "\""

def main : IO Unit :=
  IO.println ("[" ++ String.intercalate ","
    (StepTag.serializedAll.map jsonString) ++ "]")
