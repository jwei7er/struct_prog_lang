(* Written by Jordan Weiler *)
(* December 4, 2013         *)

exception EmptyList
exception LTZero

let report x =
    print_string "Result: "; print_string x; print_newline();;

let report_i x =
    report (string_of_int x)

let report_xi x =
    print_string "Error: ";
    print_string (string_of_int x);
    print_string " is not a whole number";
    print_newline();;

let report_f x =
    report (string_of_float x)

let report_b x =
    report (string_of_bool x)

let report_l x =
    print_string "Result list: ";
    let rec pl l =
        match l with
        | hd::tl -> print_int hd; print_string " "; pl tl
        | [] -> print_newline() 
    in pl x;;

(* ------------------ *)
(* QUESTION 1 ANSWERS *)
(* ------------------ *)

(* Integer CSP Functions *)
let addk a b k =
    k (a + b)

let subk a b k = 
    k (a - b)

let timesk a b k = 
    k (a * b)

(* Float CSP Functions *)
let plusk a b k =
    k (a +. b)

let take_awayk a b k =
    k (a -. b)

let multk a b k =
    k (a *. b)

(* String CSP Functions *)
let catk a b k = 
    k (a ^ b)

(* List CSP Functions *)
let consk a b k =
    k (a :: b)

let hdk l k =
    match l with
    |  [] -> raise EmptyList
    | hd::tl -> k hd

let tlk l k =
    match l with
    | [] -> raise EmptyList
    | hd::tl -> k tl

(* Boolean CSP Functions *)
let lessk a b k =
    k (a < b)

let eqk a b k =
    k (a = b)


(* Used for testing *)
let _ = print_string "Testing question 1"; print_newline();;
let _ = addk 3 4 report_i
(*
    let _ = subk 7 9 report_i
    let _ = timesk 3 4 report_i
    let _ = plusk 3.3 4.2 report_f
    let _ = take_awayk 3.3 4.2 report_f
    let _ = multk 2.3 4.9 report_f
    let _ = catk "Hello" "World" report
    let _ = lessk 5 4 report_b
    let _ = eqk 3 3 report_b
*)


(* ------------------ *)
(* QUESTION 2 ANSWERS *)
(* ------------------ *)

(* Function returns (a + (b * c)) + (d * a) calculation *)
let abcdk a b c d k =
    multk b c (fun bc -> multk d a (fun da -> plusk a bc (fun abc -> plusk abc da k)))

(* Used for testing *)
let _ = print_string "Testing question 2"; print_newline();;
let _ = abcdk 2.0 3.0 4.0 5.0 report_f


(* ------------------ *)
(* QUESTION 3 ANSWERS *)
(* ------------------ *)

(* direct style *)
let rec fact_range n m =
    if n < m then 1
    else n * fact_range (n-1) m

(* CSP style *)
let rec fact_rangek n m k =
    lessk n m
    (fun b -> if b then k 1
              else subk n 1
                   (fun s -> fact_rangek s m
                             (fun r -> timesk n r k)))

(* Used for testing *)
let _ = print_string "Testing question 3"; print_newline();;
let _ = report_i (fact_range 5 1)
let _ = fact_rangek 7 5 report_i


(* ------------------ *)
(* QUESTION 4 ANSWERS *)
(* ------------------ *)

(* direct style *)
let rec app_all flst x =
    match flst with
    | hd::tl -> (hd x)::(app_all tl x)
    | _ -> []

(* CSP style *)
let rec app_allk flstk x k =
    eqk flstk []                                                                (* check if list is empty *)
    (fun b -> if b then k []                                                    (* return empty list if list is empty *)
              else hdk flstk                                                    (* get head from list *)
                   (fun hd -> hd x                                              (* evaluate head function on x *)
                              (fun v -> tlk flstk                               (* get tail from list *)
                                        (fun tl -> app_allk tl x                (* call function on tail list *)
                                                   (fun r -> consk v r k)))))   (* cons the value of the head with the value of the tail *)

(* Used for testing *)
let _ = print_string "Testing question 4"; print_newline();;
let _ = report_l (app_all [((+) 1); (fun x -> x * x); (fun x -> 13)] 5)
let _ = report_l (app_allk [(addk 1); (fun x -> timesk x x); (fun x -> (fun k -> k 13))] 5 (fun x -> x))


(* ------------------ *)
(* QUESTION 5 ANSWERS *)
(* ------------------ *)

(* Used as an example *)
(* NOTE: does not pass offending value to output so technically incorrect *)
(*
let sum_wholes list =
    let rec sum_wholes_aux l =
        match l with
        | [] -> 0
        | hd::tl -> if hd < 0 then raise LTZero
                    else hd + (sum_wholes_aux tl)
    in
    try sum_wholes_aux list with LTZero -> -1
*)

(* Used as an example *)
(*
    exception Zero
    
    let rec list_mult_aux list =
        match list with
            [] -> 1
        | x::xs -> if x = 0 then raise Zero
                   else x * list_mult_aux xs;;
    
    let rec list_mult list =
        try list_mult_aux list with Zero -> 0;;
    
    let _ = report_i (list_mult [3; 4; 2;])
    let _ = report_i (list_mult [7; 4; 0; 8;])
*)


let rec sum_wholesk l k xk =
    eqk l []                                                                          (* check if the list is empty *)
    (fun bempty -> if bempty then k 0                                                 (* if the list is empty call k on 0 *)
                   else hdk l                                                         (* get the head of the list *)
                        (fun hd -> lessk hd 0                                         (* check if head < 0 *)
                                   (fun b0 -> if b0 then xk hd                        (* if the head < 0 call exception k on head value *)
                                              else tlk l                              (* get the tail of the list *)
                                                   (fun tl -> sum_wholesk tl          (* call sum_wholesk on the tail *)
                                                              (fun r -> addk hd r k)  (* add the value of the head with the recursive value of the tail *)
                                                              xk)))) 

(* Used as an example *)
(*
    let rec list_multk_aux list k kexcp =
        match list with
        | [] -> k 1
        | x:: xs -> if x = 0 then kexcp 0
                    else list_multk_aux xs
                         (fun r -> timesk x r k) kexcp
    
    let rec list_multk list k = list_multk_aux list k k
    
    let _ = list_multk [3; 4; 2;] report_i
*)

(* Used for testing *)
let _ = print_string "Testing question 5"; print_newline();;
(*
let _ = report_i (sum_wholes [0; -1; 2; 3;])
*)
let _ = sum_wholesk [0; -1; 2; 3;] report_i report_xi
let _ = sum_wholesk [1; 2; 3; 4; 5; 6; 7; 8; 9; 10;] report_i report_xi
let _ = sum_wholesk [] report_i report_xi


