import Compcert.values

namespace Compcert
namespace switch

open Compcert.values Compcert.word Compcert.integers Compcert.maps

inductive switch_argument : Bool → val → (w : Nat) → word w → Prop
| switch_argument_32 (i : word 32) : switch_argument false (val.Vint i) 32 i
| switch_argument_64 (i : word 64) : switch_argument true (val.Vlong i) 64 i

end switch
end Compcert
