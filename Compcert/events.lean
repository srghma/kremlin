module

public import Compcert.ast
public import Compcert.integers
public import Compcert.values
public import Compcert.memory
public import Compcert.globalenvs

@[expose] public section

namespace Compcert
namespace events

open Compcert.ast Compcert.integers Compcert.values Compcert.memory Compcert.globalenvs

inductive event : Type
| syscall (name : ident) (args : List val) (res : val)
| volatile_load (chunk : memory_chunk) (id : ident) (ofs : ptrofs) (res : val)
| volatile_store (chunk : memory_chunk) (id : ident) (ofs : ptrofs) (arg : val)
| annot (text : String) (args : List val)

def trace := List event

inductive external_call {F V} : external_function → genv F V → List val → mem → trace → val → mem → Prop

end events
end Compcert
