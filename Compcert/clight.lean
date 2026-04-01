import Compcert.ctypes
import Compcert.cop
import Compcert.globalenvs

namespace Compcert
namespace clight

open Compcert.ctypes Compcert.integers Compcert.ast Compcert.maps Compcert.floats Compcert.values Compcert.memory Compcert.word Compcert.cop Compcert.globalenvs Compcert.errors

inductive expr : Type
| Econst_int   (n : int32) (ty : type)
| Econst_float (f : float) (ty : type)
| Econst_single (f : float32) (ty : type)
| Econst_long  (n : int64) (ty : type)
| Evar         (id : ident) (ty : type)
| Etempvar     (id : ident) (ty : type)
| Ederef       (e : expr) (ty : type)
| Eaddrof      (e : expr) (ty : type)
| Eunop        (op : unary_operation) (e : expr) (ty : type)
| Ebinop       (op : binary_operation) (e1 e2 : expr) (ty : type)
| Ecast        (e : expr) (ty : type)
| Efield       (e : expr) (id : ident) (ty : type)
| Esizeof      (ty' : type) (ty : type)
| Ealignof     (ty' : type) (ty : type)
deriving Inhabited

inductive statement : Type
| Sskip : statement
| Sassign : expr → expr → statement
| Sset : ident → expr → statement
| Scall : Option ident → expr → List expr → statement
| Sbuiltin : builtin_res ident → external_function → List expr → statement
| Ssequence : statement → statement → statement
| Sifthenelse : expr → statement → statement → statement
| Sloop : statement → statement → statement
| Sbreak : statement
| Scontinue : statement
| Sreturn : Option expr → statement
| Sswitch : expr → List (Option Int × statement) → statement
| Slabel : ident → statement → statement
| Sgoto : ident → statement
deriving Inhabited

structure function : Type where
  fn_return : type
  fn_callconv : calling_convention
  fn_params : List (ident × type)
  fn_vars : List (ident × type)
  fn_temps : List (ident × type)
  fn_body : statement
deriving Inhabited

abbrev fundef := Compcert.ast.fundef function
abbrev program := Compcert.ast.program fundef type

end clight
end Compcert
