import Compcert.lib
import Compcert.word

/- Stub file for Flocq definitions -/

namespace Compcert
namespace flocq

def binary32 : Type := Unit
def binary64 : Type := Unit
def split_bits : Nat → Nat → Int → Bool × Int × Int := fun _ _ _ => (false, 0, 0)

def nan_pl (n : Nat) := Compcert.word n

def int_round_odd (x : Int) (p : Nat) : Int :=
  let p2 := (2^p : Nat)
  (if x % (p2 : Int) = 0 || (x / (p2 : Int)) % 2 = 1 then x / (p2 : Int) else x / (p2 : Int) + 1) * (p2 : Int)

end flocq
end Compcert
