import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Basic

namespace Compcert

/- * Useful tactics -/

macro "sorry'" : term => `(sorry)

/- * Standard library additions -/

namespace int

def nat_mod (a : Int) (b : Nat) : Nat :=
  (a % (b : Int)).toNat

def quot (a b : Int) : Int :=
  a / b

def rem (a b : Int) : Int :=
  a % b

end int

namespace nat

def size (n : Nat) : Nat :=
  if n = 0 then 0 else (Nat.log2 n) + 1

end nat

/- binary positive integers -/
inductive pos_num : Type
| one  : pos_num
| bit1 : pos_num → pos_num
| bit0 : pos_num → pos_num
deriving DecidableEq

namespace pos_num
  def toNat : pos_num → Nat
  | one => 1
  | bit1 n => 2 * toNat n + 1
  | bit0 n => 2 * toNat n

  instance : Coe pos_num Nat := ⟨toNat⟩
end pos_num

/- * Comparison functions -/

inductive comparison : Type
| Ceq : comparison  /- equals -/
| Cne : comparison  /- not equals -/
| Clt : comparison  /- less than -/
| Cle : comparison  /- less than or equal -/
| Cgt : comparison  /- greater than -/
| Cge : comparison  /- greater than or equal -/
deriving DecidableEq

def negate_comparison : comparison → comparison
| comparison.Ceq => comparison.Cne
| comparison.Cne => comparison.Ceq
| comparison.Clt => comparison.Cge
| comparison.Cle => comparison.Cgt
| comparison.Cgt => comparison.Cle
| comparison.Cge => comparison.Clt

def swap_comparison : comparison → comparison
| comparison.Ceq => comparison.Ceq
| comparison.Cne => comparison.Cne
| comparison.Clt => comparison.Cgt
| comparison.Cle => comparison.Cge
| comparison.Cgt => comparison.Clt
| comparison.Cge => comparison.Cle

/- * Semidecidable propositions -/

class semidecidable (p : Prop) : Type where
  get : Option (PLift p)

end Compcert
