val ( let* ) : [< `Error of 'a | `Success of 'b ] -> ('b -> ([> `Error of 'a | `Success of 'd ] as 'c)) -> 'c