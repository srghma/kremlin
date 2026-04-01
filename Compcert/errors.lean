import Compcert.lib

namespace Compcert
namespace errors

inductive errcode : Type
| MSG: String -> errcode
| CTX: Compcert.pos_num -> errcode    /- a top-level identifier -/
| POS: Compcert.pos_num -> errcode    /- a positive integer, e.g. a PC -/

def errmsg: Type := List errcode

def msg (s: String) : errmsg := [errcode.MSG s]

inductive res (A : Type) : Type
| OK    : A -> res A
| error : errmsg -> res A

namespace res

def bind {A B : Type} : res A → (A → res B) → res B
| (OK a), f => f a
| (error e), _ => error e

end res

instance : Monad res where
  pure := res.OK
  bind := res.bind

end errors
end Compcert
