



let q1 () =
  Assume.compatible "identity" [%ty : 'a -> 'a]; 
  Check.name1 "identity" [%ty : unit -> unit]  
     [();()]





  

(** set result *)
let () =
  Result.set (Result.questions [q1])