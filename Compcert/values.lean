import Compcert.lib
import Compcert.integers
import Compcert.floats
import Compcert.ast

namespace Compcert
namespace values

open Compcert.integers Compcert.ast Compcert.floats Compcert.word

noncomputable section

inductive val : Type
| Vundef
| Vint (n : word 32)
| Vlong (n : word 64)
| Vfloat (f : float)
| Vsingle (f : float32)
| Vptr (b : ident) (ofs : word (if archi.ptr64 then 64 else 32))
deriving Inhabited

instance : DecidableEq val := fun _ _ => sorry

namespace val

def type_of : val → typ
| Vundef     => typ.Tany64
| Vint _     => typ.Tint
| Vlong _    => typ.Tlong
| Vfloat _   => typ.Tfloat
| Vsingle _  => typ.Tsingle
| Vptr _ _   => Tptr

def has_type : val → typ → Prop := sorry

def has_type_list : List val → List typ → Prop := sorry

/- subtyping on lists of types -/

def subtype_list : List typ → List typ → Bool
| [], [] => true
| ty1 :: tyl1, ty2 :: tyl2 => ast.subtype ty1 ty2 && subtype_list tyl1 tyl2
| _, _ => false

/- Arithmetic operations -/

def negint : val → val
| Vint n => Vint (word.neg n)
| _ => Vundef

def neglong : val → val
| Vlong n => Vlong (word.neg n)
| _ => Vundef

def negf : val → val
| Vfloat f => Vfloat (float_neg f)
| _ => Vundef

def negs : val → val
| Vsingle f => Vsingle (float32_neg f)
| _ => Vundef

end val

end
end values
end Compcert
