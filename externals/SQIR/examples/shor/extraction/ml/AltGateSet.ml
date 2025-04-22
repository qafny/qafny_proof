open Nat

type 'u ucom =
| Coq_useq of 'u ucom * 'u ucom
| Coq_uapp of Z.t * 'u * Z.t list

type coq_U =
| U_X
| U_H
| U_U1 of float
| U_U2 of float * float
| U_U3 of float * float * float
| U_CX
| U_CU1 of float
| U_SWAP
| U_CCX
| U_CSWAP
| U_C3X
| U_C4X

(** val coq_X : Z.t -> coq_U ucom **)

let coq_X q =
  Coq_uapp ((Z.succ Z.zero), U_X, (q :: []))

(** val coq_H : Z.t -> coq_U ucom **)

let coq_H q =
  Coq_uapp ((Z.succ Z.zero), U_H, (q :: []))

(** val coq_U1 : float -> Z.t -> coq_U ucom **)

let coq_U1 r1 q =
  Coq_uapp ((Z.succ Z.zero), (U_U1 r1), (q :: []))

(** val coq_U2 : float -> float -> Z.t -> coq_U ucom **)

let coq_U2 r1 r2 q =
  Coq_uapp ((Z.succ Z.zero), (U_U2 (r1, r2)), (q :: []))

(** val coq_U3 : float -> float -> float -> Z.t -> coq_U ucom **)

let coq_U3 r1 r2 r3 q =
  Coq_uapp ((Z.succ Z.zero), (U_U3 (r1, r2, r3)), (q :: []))

(** val coq_T : Z.t -> coq_U ucom **)

let coq_T q =
  coq_U1 (( /. ) Float.pi 4.0) q

(** val coq_Tdg : Z.t -> coq_U ucom **)

let coq_Tdg q =
  coq_U1 (((-.) 0.0) (( /. ) Float.pi 4.0)) q

(** val coq_ID : Z.t -> coq_U ucom **)

let coq_ID q =
  coq_U1 0.0 q

(** val coq_SKIP : coq_U ucom **)

let coq_SKIP =
  coq_ID Z.zero

(** val coq_CX : Z.t -> Z.t -> coq_U ucom **)

let coq_CX q1 q2 =
  Coq_uapp ((Z.succ (Z.succ Z.zero)), U_CX, (q1 :: (q2 :: [])))

(** val coq_CU1 : float -> Z.t -> Z.t -> coq_U ucom **)

let coq_CU1 r q1 q2 =
  Coq_uapp ((Z.succ (Z.succ Z.zero)), (U_CU1 r), (q1 :: (q2 :: [])))

(** val coq_SWAP : Z.t -> Z.t -> coq_U ucom **)

let coq_SWAP q1 q2 =
  Coq_uapp ((Z.succ (Z.succ Z.zero)), U_SWAP, (q1 :: (q2 :: [])))

(** val coq_CCX : Z.t -> Z.t -> Z.t -> coq_U ucom **)

let coq_CCX q1 q2 q3 =
  Coq_uapp ((Z.succ (Z.succ (Z.succ Z.zero))), U_CCX,
    (q1 :: (q2 :: (q3 :: []))))

(** val coq_CSWAP : Z.t -> Z.t -> Z.t -> coq_U ucom **)

let coq_CSWAP q1 q2 q3 =
  Coq_uapp ((Z.succ (Z.succ (Z.succ Z.zero))), U_CSWAP,
    (q1 :: (q2 :: (q3 :: []))))

(** val coq_C3X : Z.t -> Z.t -> Z.t -> Z.t -> coq_U ucom **)

let coq_C3X q1 q2 q3 q4 =
  Coq_uapp ((Z.succ (Z.succ (Z.succ (Z.succ Z.zero)))), U_C3X,
    (q1 :: (q2 :: (q3 :: (q4 :: [])))))

(** val coq_C4X : Z.t -> Z.t -> Z.t -> Z.t -> Z.t -> coq_U ucom **)

let coq_C4X q1 q2 q3 q4 q5 =
  Coq_uapp ((Z.succ (Z.succ (Z.succ (Z.succ (Z.succ Z.zero))))), U_C4X,
    (q1 :: (q2 :: (q3 :: (q4 :: (q5 :: []))))))

(** val decompose_CH : Z.t -> Z.t -> coq_U ucom **)

let decompose_CH a b =
  Coq_useq ((Coq_useq ((coq_U3 (( /. ) Float.pi 4.0) 0.0 0.0 b),
    (coq_CX a b))), (coq_U3 (((-.) 0.0) (( /. ) Float.pi 4.0)) 0.0 0.0 b))

(** val decompose_CU1 : float -> Z.t -> Z.t -> coq_U ucom **)

let decompose_CU1 r1 a b =
  Coq_useq ((Coq_useq ((Coq_useq ((Coq_useq ((coq_U1 (( /. ) r1 2.0) a),
    (coq_U1 (( /. ) r1 2.0) b))), (coq_CX a b))),
    (coq_U1 (((-.) 0.0) (( /. ) r1 2.0)) b))), (coq_CX a b))

(** val decompose_CU2 : float -> float -> Z.t -> Z.t -> coq_U ucom **)

let decompose_CU2 r1 r2 a b =
  Coq_useq ((Coq_useq ((Coq_useq ((Coq_useq ((Coq_useq
    ((coq_U1 (( /. ) (( +. ) r2 r1) 2.0) a),
    (coq_U1 (( /. ) (( -. ) r2 r1) 2.0) b))), (coq_CX a b))),
    (coq_U3 (((-.) 0.0) (( /. ) Float.pi 4.0)) 0.0
      (( /. ) (((-.) 0.0) (( +. ) r1 r2)) 2.0) b))), (coq_CX a b))),
    (coq_U3 (( /. ) Float.pi 4.0) r1 0.0 b))

(** val decompose_CU3 :
    float -> float -> float -> Z.t -> Z.t -> coq_U ucom **)

let decompose_CU3 r1 r2 r3 a b =
  Coq_useq ((Coq_useq ((Coq_useq ((Coq_useq ((Coq_useq
    ((coq_U1 (( /. ) (( +. ) r3 r2) 2.0) a),
    (coq_U1 (( /. ) (( -. ) r3 r2) 2.0) b))), (coq_CX a b))),
    (coq_U3 (((-.) 0.0) (( /. ) r1 2.0)) 0.0
      (( /. ) (((-.) 0.0) (( +. ) r2 r3)) 2.0) b))), (coq_CX a b))),
    (coq_U3 (( /. ) r1 2.0) r2 0.0 b))

(** val decompose_CSWAP : Z.t -> Z.t -> Z.t -> coq_U ucom **)

let decompose_CSWAP a b c =
  Coq_useq ((Coq_useq ((coq_CCX a b c), (coq_CCX a c b))), (coq_CCX a b c))

(** val decompose_CCX : Z.t -> Z.t -> Z.t -> coq_U ucom **)

let decompose_CCX a b c =
  Coq_useq ((Coq_useq ((Coq_useq ((Coq_useq ((Coq_useq ((Coq_useq ((Coq_useq
    ((Coq_useq ((Coq_useq ((Coq_useq ((Coq_useq ((Coq_useq ((Coq_useq
    ((Coq_useq ((coq_H c), (coq_CX b c))), (coq_Tdg c))), (coq_CX a c))),
    (coq_T c))), (coq_CX b c))), (coq_Tdg c))), (coq_CX a c))),
    (coq_CX a b))), (coq_Tdg b))), (coq_CX a b))), (coq_T a))), (coq_T b))),
    (coq_T c))), (coq_H c))

(** val control' : Z.t -> coq_U ucom -> Z.t -> coq_U ucom **)

let rec control' a c n =
  (fun fO fS n -> if Z.equal n Z.zero then fO () else fS (Z.pred n))
    (fun _ -> coq_SKIP)
    (fun n' ->
    match c with
    | Coq_useq (c1, c2) -> Coq_useq ((control' a c1 n'), (control' a c2 n'))
    | Coq_uapp (_, u, l) ->
      (match u with
       | U_X ->
         (match l with
          | [] -> coq_SKIP
          | b :: l0 -> (match l0 with
                        | [] -> coq_CX a b
                        | _ :: _ -> coq_SKIP))
       | U_H ->
         (match l with
          | [] -> coq_SKIP
          | b :: l0 ->
            (match l0 with
             | [] -> decompose_CH a b
             | _ :: _ -> coq_SKIP))
       | U_U1 r ->
         (match l with
          | [] -> coq_SKIP
          | b :: l0 ->
            (match l0 with
             | [] -> coq_CU1 r a b
             | _ :: _ -> coq_SKIP))
       | U_U2 (r1, r2) ->
         (match l with
          | [] -> coq_SKIP
          | b :: l0 ->
            (match l0 with
             | [] -> decompose_CU2 r1 r2 a b
             | _ :: _ -> coq_SKIP))
       | U_U3 (r1, r2, r3) ->
         (match l with
          | [] -> coq_SKIP
          | b :: l0 ->
            (match l0 with
             | [] -> decompose_CU3 r1 r2 r3 a b
             | _ :: _ -> coq_SKIP))
       | U_CX ->
         (match l with
          | [] -> coq_SKIP
          | b :: l0 ->
            (match l0 with
             | [] -> coq_SKIP
             | c0 :: l1 ->
               (match l1 with
                | [] -> coq_CCX a b c0
                | _ :: _ -> coq_SKIP)))
       | U_CU1 r ->
         (match l with
          | [] -> coq_SKIP
          | b :: l0 ->
            (match l0 with
             | [] -> coq_SKIP
             | c0 :: l1 ->
               (match l1 with
                | [] -> control' a (decompose_CU1 r b c0) n'
                | _ :: _ -> coq_SKIP)))
       | U_SWAP ->
         (match l with
          | [] -> coq_SKIP
          | b :: l0 ->
            (match l0 with
             | [] -> coq_SKIP
             | c0 :: l1 ->
               (match l1 with
                | [] -> coq_CSWAP a b c0
                | _ :: _ -> coq_SKIP)))
       | U_CCX ->
         (match l with
          | [] -> coq_SKIP
          | b :: l0 ->
            (match l0 with
             | [] -> coq_SKIP
             | c0 :: l1 ->
               (match l1 with
                | [] -> coq_SKIP
                | d :: l2 ->
                  (match l2 with
                   | [] -> coq_C3X a b c0 d
                   | _ :: _ -> coq_SKIP))))
       | U_CSWAP ->
         (match l with
          | [] -> coq_SKIP
          | b :: l0 ->
            (match l0 with
             | [] -> coq_SKIP
             | c0 :: l1 ->
               (match l1 with
                | [] -> coq_SKIP
                | d :: l2 ->
                  (match l2 with
                   | [] -> control' a (decompose_CSWAP b c0 d) n'
                   | _ :: _ -> coq_SKIP))))
       | U_C3X ->
         (match l with
          | [] -> coq_SKIP
          | b :: l0 ->
            (match l0 with
             | [] -> coq_SKIP
             | c0 :: l1 ->
               (match l1 with
                | [] -> coq_SKIP
                | d :: l2 ->
                  (match l2 with
                   | [] -> coq_SKIP
                   | e :: l3 ->
                     (match l3 with
                      | [] -> coq_C4X a b c0 d e
                      | _ :: _ -> coq_SKIP)))))
       | U_C4X ->
         (match l with
          | [] -> coq_SKIP
          | b :: l0 ->
            (match l0 with
             | [] -> coq_SKIP
             | c0 :: l1 ->
               (match l1 with
                | [] -> coq_SKIP
                | d :: l2 ->
                  (match l2 with
                   | [] -> coq_SKIP
                   | e :: l3 ->
                     (match l3 with
                      | [] -> coq_SKIP
                      | f :: l4 ->
                        (match l4 with
                         | [] ->
                           control' a
                             (control' b
                               (control' c0 (decompose_CCX d e f) n') n') n'
                         | _ :: _ -> coq_SKIP))))))))
    n

(** val fuel_CU1 : Z.t **)

let fuel_CU1 =
  Z.succ (Z.succ (Z.succ (Z.succ Z.zero)))

(** val fuel_CSWAP : Z.t **)

let fuel_CSWAP =
  Z.succ (Z.succ Z.zero)

(** val fuel_CCX : Z.t **)

let fuel_CCX =
  Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ
    (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ
    (Z.succ (Z.succ (Z.succ (Z.succ Z.zero)))))))))))))))))))))

(** val fuel : coq_U ucom -> Z.t **)

let rec fuel = function
| Coq_useq (c1, c2) -> Z.succ (max (fuel c1) (fuel c2))
| Coq_uapp (_, u, _) ->
  (match u with
   | U_CU1 _ -> Z.succ fuel_CU1
   | U_CSWAP -> Z.succ fuel_CSWAP
   | U_C4X -> Z.succ fuel_CCX
   | _ -> Z.zero)

(** val control : Z.t -> coq_U ucom -> coq_U ucom **)

let control a c =
  control' a c (Z.succ (fuel c))

(** val map_qubits : (Z.t -> Z.t) -> coq_U ucom -> coq_U ucom **)

let rec map_qubits f = function
| Coq_useq (c1, c2) -> Coq_useq ((map_qubits f c1), (map_qubits f c2))
| Coq_uapp (n, g, qs) -> Coq_uapp (n, g, (List.map f qs))

(** val npar : Z.t -> coq_U -> coq_U ucom **)

let rec npar n u =
  (fun fO fS n -> if Z.equal n Z.zero then fO () else fS (Z.pred n))
    (fun _ -> coq_SKIP)
    (fun n' ->
    (fun fO fS n -> if Z.equal n Z.zero then fO () else fS (Z.pred n))
      (fun _ -> Coq_uapp ((Z.succ Z.zero), u, (Z.zero :: [])))
      (fun _ -> Coq_useq ((npar n' u), (Coq_uapp ((Z.succ Z.zero), u,
      (n' :: [])))))
      n')
    n

(** val invert : coq_U ucom -> coq_U ucom **)

let rec invert = function
| Coq_useq (u1, u2) -> Coq_useq ((invert u2), (invert u1))
| Coq_uapp (_, g, qs) ->
  (match g with
   | U_X ->
     (match qs with
      | [] -> coq_SKIP
      | q1 :: l -> (match l with
                    | [] -> coq_X q1
                    | _ :: _ -> coq_SKIP))
   | U_H ->
     (match qs with
      | [] -> coq_SKIP
      | q1 :: l -> (match l with
                    | [] -> coq_H q1
                    | _ :: _ -> coq_SKIP))
   | U_U1 r1 ->
     (match qs with
      | [] -> coq_SKIP
      | q1 :: l ->
        (match l with
         | [] -> coq_U1 (((-.) 0.0) r1) q1
         | _ :: _ -> coq_SKIP))
   | U_U2 (r1, r2) ->
     (match qs with
      | [] -> coq_SKIP
      | q1 :: l ->
        (match l with
         | [] ->
           coq_U2 (( -. ) (((-.) 0.0) r2) Float.pi)
             (( +. ) (((-.) 0.0) r1) Float.pi) q1
         | _ :: _ -> coq_SKIP))
   | U_U3 (r1, r2, r3) ->
     (match qs with
      | [] -> coq_SKIP
      | q1 :: l ->
        (match l with
         | [] -> coq_U3 (((-.) 0.0) r1) (((-.) 0.0) r3) (((-.) 0.0) r2) q1
         | _ :: _ -> coq_SKIP))
   | U_CX ->
     (match qs with
      | [] -> coq_SKIP
      | q1 :: l ->
        (match l with
         | [] -> coq_SKIP
         | q2 :: l0 -> (match l0 with
                        | [] -> coq_CX q1 q2
                        | _ :: _ -> coq_SKIP)))
   | U_CU1 r ->
     (match qs with
      | [] -> coq_SKIP
      | q1 :: l ->
        (match l with
         | [] -> coq_SKIP
         | q2 :: l0 ->
           (match l0 with
            | [] -> coq_CU1 (((-.) 0.0) r) q1 q2
            | _ :: _ -> coq_SKIP)))
   | U_SWAP ->
     (match qs with
      | [] -> coq_SKIP
      | q1 :: l ->
        (match l with
         | [] -> coq_SKIP
         | q2 :: l0 ->
           (match l0 with
            | [] -> coq_SWAP q1 q2
            | _ :: _ -> coq_SKIP)))
   | U_CCX ->
     (match qs with
      | [] -> coq_SKIP
      | q1 :: l ->
        (match l with
         | [] -> coq_SKIP
         | q2 :: l0 ->
           (match l0 with
            | [] -> coq_SKIP
            | q3 :: l1 ->
              (match l1 with
               | [] -> coq_CCX q1 q2 q3
               | _ :: _ -> coq_SKIP))))
   | U_CSWAP ->
     (match qs with
      | [] -> coq_SKIP
      | q1 :: l ->
        (match l with
         | [] -> coq_SKIP
         | q2 :: l0 ->
           (match l0 with
            | [] -> coq_SKIP
            | q3 :: l1 ->
              (match l1 with
               | [] -> coq_CSWAP q1 q2 q3
               | _ :: _ -> coq_SKIP))))
   | U_C3X ->
     (match qs with
      | [] -> coq_SKIP
      | q1 :: l ->
        (match l with
         | [] -> coq_SKIP
         | q2 :: l0 ->
           (match l0 with
            | [] -> coq_SKIP
            | q3 :: l1 ->
              (match l1 with
               | [] -> coq_SKIP
               | q4 :: l2 ->
                 (match l2 with
                  | [] -> coq_C3X q1 q2 q3 q4
                  | _ :: _ -> coq_SKIP)))))
   | U_C4X ->
     (match qs with
      | [] -> coq_SKIP
      | q1 :: l ->
        (match l with
         | [] -> coq_SKIP
         | q2 :: l0 ->
           (match l0 with
            | [] -> coq_SKIP
            | q3 :: l1 ->
              (match l1 with
               | [] -> coq_SKIP
               | q4 :: l2 ->
                 (match l2 with
                  | [] -> coq_SKIP
                  | q5 :: l3 ->
                    (match l3 with
                     | [] -> coq_C4X q1 q2 q3 q4 q5
                     | _ :: _ -> coq_SKIP)))))))
