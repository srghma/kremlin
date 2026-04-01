import Compcert.ctypes
import Compcert.memory

namespace Compcert
namespace cop

open Compcert.ast Compcert.integers Compcert.floats Compcert.values Compcert.memory Compcert.ctypes Compcert.word

inductive unary_operation : Type
| Onotbool          /- boolean negation ([!] in C) -/
| Onotint           /- integer complement ([~] in C) -/
| Oneg              /- opposite (unary [-]) -/
| Oabsfloat         /- floating-point absolute value -/
deriving DecidableEq

inductive binary_operation : Type
| Oadd              /- addition (binary [+]) -/
| Osub              /- subtraction (binary [-]) -/
| Omul              /- multiplication (binary [*]) -/
| Odiv              /- division (binary [/]) -/
| Omod              /- modulus (binary [%]) -/
| Oand              /- bitwise and (binary [&]) -/
| Oor               /- bitwise or (binary [|]) -/
| Oxor              /- bitwise xor (binary [^]) -/
| Oshl              /- left shift (binary [<<]) -/
| Oshr              /- right shift (binary [>>]) -/
| Oeq               /- equality (binary [==]) -/
| One               /- inequality (binary [!=]) -/
| Olt               /- less than (binary [<]) -/
| Ole               /- less than or equal (binary [<=]) -/
| Ogt               /- greater than (binary [>]) -/
| Oge               /- greater than or equal (binary [>=]) -/
deriving DecidableEq

inductive incr_or_decr : Type | Incr | Decr
deriving DecidableEq

end cop
end Compcert
