val ( let* ) : [< `Error of 'a | `Success of 'b ] ->
        ('b -> ([> `Error of 'a | `Success of 'd ] as 'c)) -> 'c
val ( let** ) : [< `Error of string * 'a | `Success of 'b ] * string ->
         ('b -> ([> `Error of string * 'a | `Success of 'd ] as 'c)) -> 'c