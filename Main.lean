import CogitoCore


def main (args : List String) : IO UInt32 := do
  IO.println s!"CogitoCore {CogitoCore.version}"
  pure 0
