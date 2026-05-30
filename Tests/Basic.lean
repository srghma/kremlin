import Compcert.lib

open Compcert

def test_pos_num_toNat : IO Unit := do
  let n1 := pos_num.one
  let n2 := pos_num.bit0 pos_num.one -- 2
  let n3 := pos_num.bit1 pos_num.one -- 3
  if n1.toNat != 1 then throw (IO.userError "test_pos_num_toNat failed for one")
  if n2.toNat != 2 then throw (IO.userError "test_pos_num_toNat failed for bit0 one")
  if n3.toNat != 3 then throw (IO.userError "test_pos_num_toNat failed for bit1 one")
  IO.println "test_pos_num_toNat passed"

def test_negate_comparison : IO Unit := do
  if negate_comparison comparison.Ceq != comparison.Cne then throw (IO.userError "test_negate_comparison failed for Ceq")
  if negate_comparison comparison.Cne != comparison.Ceq then throw (IO.userError "test_negate_comparison failed for Cne")
  IO.println "test_negate_comparison passed"

def main : IO Unit := do
  test_pos_num_toNat
  test_negate_comparison
  IO.println "All tests passed!"
