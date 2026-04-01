import Compcert.events
import Compcert.switch
import Compcert.cop

namespace Compcert
namespace cminor

open Compcert.integers Compcert.ast Compcert.cop maps values memory events globalenvs switch

inductive const : Type
| Ointconst    : int32 → const
| Ofloatconst  : floats.float → const
| Osingleconst : floats.float32 → const
| Olongconst   : int64 → const
| Oaddrsymbol  : ident → ptrofs → const
deriving Inhabited

inductive expr : Type
| Evar      : ident → expr
| Econst    : const → expr
| Eunop     : unary_operation → expr → expr
| Ebinop    : binary_operation → expr → expr → expr
| Eload     : memory_chunk → expr → expr
deriving Inhabited

inductive stmt : Type
| Sskip     : stmt
| Sassign   : ident → expr → stmt
| Sstore    : memory_chunk → expr → expr → stmt
| Scall     : Option ident → signature → expr → List expr → stmt
| Stailcall : signature → expr → List expr → stmt
| Sbuiltin  : ast.builtin_res ident → external_function → List expr → stmt
| Sseq      : stmt → stmt → stmt
| Sifthenelse : expr → stmt → stmt → stmt
| Sloop     : stmt → stmt
| Sblock    : stmt → stmt
| Sexit     : Nat → stmt
| Sswitch   : Bool → expr → List (Option Int × Nat) → Nat → stmt
| Sreturn   : Option expr → stmt
| Slabel    : ident → stmt → stmt
| Sgoto     : ident → stmt
deriving Inhabited

structure function : Type where
  fn_sig: signature
  fn_params: List ident
  fn_vars: List ident
  fn_stackspace: Int
  fn_body: stmt
deriving Inhabited

abbrev fundef := Compcert.ast.fundef function
abbrev program := Compcert.ast.program fundef Unit

end cminor
end Compcert
