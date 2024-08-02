val codegen : Parser.Types.statements -> ( Parser.Types.ident*int)list -> Parser.Types.ident-> [`Success of string | `Error of string * int]
