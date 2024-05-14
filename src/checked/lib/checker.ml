(* Names: Joshua Hizgiaev & Matthew Soltys
   Pledge: I pledge my honor that I have abided by the Stevens Honor System.
   Date: 04/18/2024 *)

open ReM
open Dst
open Parser_plaf.Ast
open Parser_plaf.Parser
       
let rec chk_expr : expr -> texpr tea_result = function 
  | Int _n -> return IntType
  | Var id -> apply_tenv id
  | IsZero(e) ->
    chk_expr e >>= fun t ->
    if t=IntType
    then return BoolType
    else error "isZero: expected argument of type int"
  | Add(e1,e2) | Sub(e1,e2) | Mul(e1,e2)| Div(e1,e2) ->
    chk_expr e1 >>= fun t1 ->
    chk_expr e2 >>= fun t2 ->
    if (t1=IntType && t2=IntType)
    then return IntType
    else error "arith: arguments must be ints"
  | ITE(e1,e2,e3) ->
    chk_expr e1 >>= fun t1 ->
    chk_expr e2 >>= fun t2 ->
    chk_expr e3 >>= fun t3 ->
    if (t1=BoolType && t2=t3)
    then return t2
    else error "ITE: condition not boolean or types of then and else do not match"
  | Let(id,e,body) ->
    chk_expr e >>= fun t ->
    extend_tenv id t >>+
    chk_expr body
  | Proc(var,Some t1,e) ->
    extend_tenv var t1 >>+
    chk_expr e >>= fun t2 ->
    return @@ FuncType(t1,t2)
  | Proc(_var,None,_e) ->
    error "proc: type declaration missing"
  | App(e1,e2) ->
    chk_expr e1 >>=
    pair_of_funcType "app: " >>= fun (t1,t2) ->
    chk_expr e2 >>= fun t3 ->
    if t1=t3
    then return t2
    else error "app: type of argument incorrect"
  | Letrec([(_id,_param,None,_,_body)],_target) | Letrec([(_id,_param,_,None,_body)],_target) ->
    error "letrec: type declaration missing"
  | Letrec([(id,param,Some tParam,Some tRes,body)],target) ->
    extend_tenv id (FuncType(tParam,tRes)) >>+
    (extend_tenv param tParam >>+
     chk_expr body >>= fun t ->
     if t=tRes 
     then chk_expr target
     else error
         "LetRec: Type of recursive function does not match
declaration")
  | Record([]) -> error "record: no fields"
  | Record(fs) -> 
    let (ids,bes) = List.split fs in let (_bs,es) = List.split bes in 
    if List.length (List.sort_uniq compare ids) = List.length ids then 
      chk_exprs es >>= fun ts -> 
      return (RecordType (List.combine ids ts))
    else error "record: duplicate fields"
  | Proj(e,id) -> 
    chk_expr e >>= fun te ->
      (match te with
      | RecordType fs ->
        (match List.assoc_opt id fs with 
        | Some t -> return t 
        | None -> error "proj: field does not exist")
      | _ -> error "proj: target not a record")
  | NewRef(e) ->
    chk_expr e >>= fun e1 -> return (RefType (e1))
  | DeRef(e) -> 
    chk_expr e >>= fun t ->
      (match t with
      | RefType(e) -> return e
      | _ -> error "Error: Reference expected!")
  | SetRef(e1,e2) -> 
    chk_expr e1 >>= fun t1 ->
      (match t1 with
      | RefType(t) -> chk_expr e2 >>= fun t2 ->
        if t = t2 then return UnitType else error "Error: Type mismatch for setRef!"
      | _ -> error "Error: Reference expected!")
  | BeginEnd([]) -> return UnitType
  | BeginEnd(es) -> chk_exprs es >>= fun tlist -> return (List.hd (List.rev tlist))
  | EmptyList(t) -> 
    (match t with
    | Some t -> return (ListType(t))
    | _ -> error "Error: Not a type!") 
  | Cons(e1,e2) -> 
    chk_expr e1 >>= fun t ->
    chk_expr e2 >>= fun t2 ->
    (match t2 with
    | ListType(d) -> 
      if t = d 
      then return (ListType(d)) 
      else error "cons: type of head and tail do not match"
    | _ -> error "Must be a ListType for Cons")
  | IsEmpty(e) -> 
    chk_expr e >>= fun t ->
    (match t with
    | ListType(_) -> return BoolType
    | TreeType(_) -> return BoolType
    | _ -> error "Error: Not a ListType or a TreeType!") 
  | Hd(e) -> chk_expr e >>= fun t ->
    (match t with
    | ListType(t1) -> return t1
    | _ -> error "Error: Used Hd on a non-list type")
  | Tl(e) -> chk_expr e >>= fun t -> 
    (match t with
    | ListType(d) -> return (ListType(d))
    | _ -> error "Error: Used Tl on a non-list type")
  | EmptyTree(t) -> 
    (match t with
    | Some t -> return (TreeType(t))
    | _ -> error "Error: Not a type!") 
  | Node(de, le, re) -> 
    chk_expr de >>= fun e1 ->
      chk_expr le >>= fun e2 ->
        chk_expr re >>= fun e3 ->
          (match (e2,e3) with
          | (TreeType(t1),TreeType(t2)) -> 
            if (t1 = e1 && t2 = e1) then return (TreeType(e1)) else error "Error: Tree data type mismatch"
          | _ -> error "Not a tree")
  | CaseT(target, emptycase, id1, id2, id3, nodecase) -> 
    chk_expr target >>= fun e1 ->
    (match e1 with
    | TreeType(_) -> chk_expr emptycase >>= fun e2 -> extend_tenv id1 e2 >>+ extend_tenv id2 e2 >>+ extend_tenv id3 e2 >>+ chk_expr nodecase >>= fun e3 ->
      if e2=e3
      then return e2
      else error "Error: Tree data type mismatch for CaseT"
    | _ -> error "Error: Not a TreeType for CaseT!")
  | Debug(_e) ->
    string_of_tenv >>= fun str ->
    print_endline str;
    error "Debug: reached breakpoint"
  | _ -> failwith "chk_expr: implement"    
and
  chk_prog (AProg(_,e)) =
  chk_expr e
and
  chk_exprs es =
  match es with
  | [] -> return []
  | h::t ->
    chk_expr h >>= fun th ->
    chk_exprs t >>= fun l ->
    return (th::l)

(* Type-check an expression *)
let chk (e:string) : texpr result =
  let c = e |> parse |> chk_prog
  in run_teac c

let chkpp (e:string) : string result =
  let c = e |> parse |> chk_prog
  in run_teac (c >>= fun t -> return @@ string_of_texpr t)



