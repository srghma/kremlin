module

public import Compcert.ast
public import Compcert.maps
public import Compcert.lib

@[expose] public section

namespace Compcert
namespace linking

open Compcert.ast Compcert.maps

class Linker (A : Type) where
  link : A → A → Option A
  linkorder : A → A → Prop

end linking
end Compcert
