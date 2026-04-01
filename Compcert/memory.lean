import Compcert.ast
import Compcert.integers
import Compcert.values
import Compcert.memdata

namespace Compcert
namespace memory

open Compcert.ast Compcert.integers Compcert.values Compcert.memdata

inductive permission : Type
| Freeable
| Writable
| Readable
| Nonempty
deriving DecidableEq

def perm_order : permission → permission → Prop
| permission.Freeable, _ => true
| permission.Writable, permission.Writable => true
| permission.Writable, permission.Readable => true
| permission.Writable, permission.Nonempty => true
| permission.Readable, permission.Readable => true
| permission.Readable, permission.Nonempty => true
| permission.Nonempty, permission.Nonempty => true
| _, _ => false

instance : DecidableRel perm_order := fun _ _ => sorry

axiom mem : Type
instance : Inhabited mem := ⟨sorry⟩

axiom load : memory_chunk → mem → ident → ptrofs → Option val
axiom store : memory_chunk → mem → ident → ptrofs → val → Option mem
axiom alloc : mem → Int → Int → mem × ident
axiom free : mem → ident → Int → Int → Option mem

axiom perm : mem → ident → ptrofs → permission → Prop
axiom valid_block : mem → ident → Prop

end memory
end Compcert
