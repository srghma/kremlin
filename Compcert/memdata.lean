import Compcert.ast
import Compcert.integers
import Compcert.values

namespace Compcert
namespace memdata

open Compcert.ast Compcert.integers Compcert.values Compcert.word Compcert.floats

inductive quantity : Type | Q32 | Q64
deriving DecidableEq

def quantity.size : quantity → Nat
| Q32 => 4
| Q64 => 8

lemma quantity.size_pos (q : quantity) : q.size > 0 :=
by cases q <;> decide

inductive memval : Type
| Undef
| Byte (b : byte)
| Fragment (v : val) (q : quantity) (n : Nat)

instance : Inhabited memval := ⟨memval.Undef⟩

end memdata
end Compcert
