import Compcert.ast
import Compcert.maps
import Compcert.lib

namespace Compcert
namespace linking

open Compcert.ast Compcert.maps

class Linker (A : Type) where
  link : A → A → Option A
  linkorder : A → A → Prop

end linking
end Compcert
