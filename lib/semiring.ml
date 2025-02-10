type semiring_t =
 Tropical | Arctic | Arithmetic
let string_of_semiring_t = function
 | Tropical    -> "tropical"
 | Arctic      -> "arctic"
 | Arithmetic  -> "arithmetic"
let pp_semiring_t sr =
let str = string_of_semiring_t sr in
Printf.sprintf "%s" str 

let of_string s = 
  match s with  
|"tropical" -> Tropical
|"arctic" -> Arctic 
|"arithmetic" -> Arithmetic
|_ -> assert false