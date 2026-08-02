import Formalize.Report

def main (args : List String) : IO UInt32 := do
  Formalize.Report.runDefault args
