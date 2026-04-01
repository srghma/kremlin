import Compcert.ast
import Compcert.errors
import Compcert.linking

namespace Compcert
namespace ctypes

open Compcert.ast Compcert.errors Compcert.linking

inductive signedness : Type
| Signed : signedness
| Unsigned : signedness
deriving DecidableEq

inductive intsize : Type
| I8 : intsize
| I16 : intsize
| I32 : intsize
| IBool : intsize
deriving DecidableEq

inductive floatsize : Type
| F32 : floatsize
| F64 : floatsize
deriving DecidableEq

inductive type : Type
| Tvoid : type
| Tint : intsize → signedness → type
| Tlong : signedness → type
| Tfloat : floatsize → type
| Tpointer : type → type
| Tarray : type → Int → type
| Tfunction : List type → type → calling_convention → type
| Tstruct : ident → type
| Tunion : ident → type
| Tcomp_ptr : ident → type

instance : Inhabited type := ⟨type.Tvoid⟩

instance : DecidableEq type := fun _ _ => sorry

end ctypes
end Compcert
