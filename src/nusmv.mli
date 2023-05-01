val int_lowerbound : int ref
val int_upperbound : int ref
val help_message : string
val pp_print_nusmv_symbol_node : Format.formatter -> Symbol.symbol -> unit
val pp_print_nusmv_symbol : Format.formatter -> Symbol.t -> unit
val pp_print_nusmv_type_node : Format.formatter -> Type.kindtype -> unit
val pp_print_nusmv_type : Format.formatter -> Type.t -> unit
val pp_print_nusmv_var : Numeral.t -> Format.formatter -> Term.t -> unit
val pp_print_nusmv_term : Format.formatter -> Term.t -> unit
val pp_print_nusmv_var_declaration : Format.formatter -> StateVar.t -> unit
val pp_print_nusmv_init : Format.formatter -> Term.t list -> unit
val pp_print_nusmv_constr : Format.formatter -> Term.t list -> unit
val pp_print_nusmv_prop : Format.formatter -> Property.t -> unit
val pp_print_nusmv_trans_sys : Format.formatter -> TransSys.t -> unit
