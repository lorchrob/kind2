(* This file is part of the Kind 2 model checker.

   Copyright (c) 2015 by the Board of Trustees of the University of Iowa

   Licensed under the Apache License, Version 2.0 (the "License"); you
   may not use this file except in compliance with the License.  You
   may obtain a copy of the License at

   http://www.apache.org/licenses/LICENSE-2.0 

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
   implied. See the License for the specific language governing
   permissions and limitations under the License. 

*)


(** Handles models for the C2I algorithm. *)


(** Updates the white, grey and black model lists.
    
    In theory thanks to the cost function the intersection between the new sets
    and the old ones is empty. *)
val update_colors : int ->
  Model.t list -> (Model.t * Model.t) list -> Model.t list ->
  Model.t list -> Model.t list -> Model.t list -> (
    Model.t list * (Model.t * Model.t) list * Model.t list
  )


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
