import Lean4Mergesort.Basic

def main : IO Unit :=
  runBenchmark 400000 50
