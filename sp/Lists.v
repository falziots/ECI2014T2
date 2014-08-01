(** * Lists: Trabajando con Datos Estructurados *)

Require Export Induction.

Module NatList. 

(* ###################################################### *)
(** * Pares de Numeros *)

(** En una definicion de tipo inductivo ([Inductive]), cada
    constructor puede tomar cualquier numero de argumentos -- ninguno
    (como con [true] y [O]), uno (como con [S]), o mas de uno, como en
    esta definicion: *)

Inductive natprod : Type :=
  pair : nat -> nat -> natprod.

(** Esta declaracion puede ser leida como: "Hay una unica manera de
    construir un par de numeros: aplicando el constructor [pair] a dos
    argumentos de tipo [nat]". *)

(** Podemos construir un elemento de [natprod] asi: *)

Check (pair 3 5).

(** Aqui hay dos funciones sencillas para extraer el primer y el
    segundo componente de un par.  (Las definiciones tambien ilustran
    como hacer pattern matching con constructores con dos
    argumentos). *)

Definition fst (p : natprod) : nat := 
  match p with
  | pair x y => x
  end.
Definition snd (p : natprod) : nat := 
  match p with
  | pair x y => y
  end.

Eval compute in (fst (pair 3 5)).
(* ===> 3 *)

(** Como los pares se usan seguido, es mejor poder trabajar con la
    notacion matematica standard [(x,y)] en vez de [pair x y].
    Podemos hacer esto con el comando [Notation] de Coq. *)

Notation "( x , y )" := (pair x y).

(** La nueva notacion puede ser utilizada tanto en expresiones como en
    pattern matches (de hecho, ya vimos esto en el capitulo anterior
    -- esta notacion es provista en la libreria estandard de Coq): *)

Eval compute in (fst (3,5)).

Definition fst' (p : natprod) : nat := 
  match p with
  | (x,y) => x
  end.
Definition snd' (p : natprod) : nat := 
  match p with
  | (x,y) => y
  end.

Definition swap_pair (p : natprod) : natprod := 
  match p with
  | (x,y) => (y,x)
  end.

(** Intentemos probar algunos teoremas basicos de pares.  De acuerdo a
    como definimos un teorema, vamos a poder probarlo simplemente con
    [reflexivity] (y su simplificacion interna): *)

Theorem surjective_pairing' : forall (n m : nat),
  (n,m) = (fst (n,m), snd (n,m)).
Proof.
  reflexivity.  Qed.

(** Note que [reflexivity] no es suficiente si escribimos el lema en
    una forma mas natural: *)

Theorem surjective_pairing_stuck : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  simpl. (* No reduce nada! *)
Abort.

(** Tenemos que exponer la estructura de [p] de forma tal que [simpl]
    pueda realizar el patern matching en [fst] y [snd].  Podemos hacer esto con 
    [destruct].

    Note que, a diferencia de para [nat]urales, [destruct] no genera
    un sub-objetivo extra.  Esto es porque los [natprod]s solo pueden
    ser construidos en una sola forma.  *)

Theorem surjective_pairing : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intros p.  destruct p as [n m].  simpl.  reflexivity.  Qed.

(** **** Ejercicio: 1 star (snd_fst_is_swap) *)
Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Ejercicio: 1 star, optional (fst_swap_is_snd) *)
Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ###################################################### *)
(** * Listas de Numeros *)

(** Generalizando la definicion de pares un poco, vamos a describir el
    tipo de _listas_ de numeros de la siguiente forma: "Una lista es o
    la lista vacia, o un par conteniendo un numero y otra
    lista". *)

Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

(** Por ejemplo, aqui hay una lista con tres elementos: *)

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

(** Como con pares, es conveniente escribir listas con la notacion
    familiar.  Las siguientes declaraciones nos permite escribir [::]
    como operador infijo de [cons], y corchetes como notacion para
    construir listas. *)

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

(** No es necesario entender enteramente estas declaraciones, pero en
    caso de que este interesado, aqui hay una descripcion breve de lo
    que esta pasando.

    La anotacion [right associativity] le dice a Coq como parentizar
    expresiones involucrando varios usos de [::] de forma que, por
    ejemplo, las siguientes declaraciones signifiquen exactamente lo
    mismo: *)

Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].

(** La anotacion [at level 60] dice a Coq como parentizar expresiones
    que involucren tanto a [::] como a otro operador infijo.  Por
    ejemplo, como definimos [+] como operador infijo para la funcion
    [plus] a nivel 50, 

    Notation "x + y" := (plus x y) (at level 50, left associativity).  

    el operador [+] va a tener prioridad por sobre [::] de forma que
    [1 + 2 :: [3]] va a ser interpretado, como esperariamos, como [(1
    + 2) :: [3]] en vez de [1 + (2 :: [3])].

   (Dicho sea de paso, es importante recalcar que la expresion como
   "[1 + 2 :: [3]]" puede ser un poco confusa de leer en un archivo
   .v.  Los corchetes internos, alrededor de 3, indican una lista,
   pero los externos, que son invisibles en la version HTML, indican a
   la herramienta de impresion "coqdoc" que lo que esta entre
   parentesis deben ser mostrados como codigo Coq en vez de texto
   plano).

   La segunda y tercer declaracion [Notation] de arriba introducen las
   notaciones estandard de listas con corchetes.  En el lado derecho
   de la tercera se puede apreciar la notacion para declarar
   notaciones n-arias, en este caso resultando en una sequencia de
   [cons] anidados. *)

(** A continuacion, una serie de funciones utiles para manipular
    listas.  Por ejemplo, la funcion [repeat] que toma un numero [n] y
    otro [count] y produce una lista con [count] repeticiones del
    elemento [n]. *)

Fixpoint repeat (n count : nat) : natlist := 
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

(** La funcion [length] calcula el largo de una lista. *)

Fixpoint length (l:natlist) : nat := 
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

(** La funcion [app] ("append" en ingles) concatena dos listas. *)

Fixpoint app (l1 l2 : natlist) : natlist := 
  match l1 with
  | nil    => l2
  | h :: t => h :: (app t l2)
  end.

(** Como [app] va a ser utilizado en muchas partes a continuacion,
    creamos una notacion infija. *)

Notation "x ++ y" := (app x y) 
                     (right associativity, at level 60).

Example test_app1:             [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity.  Qed.
Example test_app2:             nil ++ [4;5] = [4;5].
Proof. reflexivity.  Qed.
Example test_app3:             [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity.  Qed.

(** Aqui hay dos pequenios ejemplos de programacion con listas.  La
    funcion [hd] retorna el primer elemento (la cabeza, "head") de una
    lista, mientras que [tl] retorna la lista sin la cabeza (es decir,
    la cola, "tail").  Por supuesto, la lista vacia no tiene primer
    elemento, asi que debemos pasar un valor para ser retornado en ese
    caso.  *)

Definition hd (default:nat) (l:natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Definition tl (l:natlist) : natlist :=
  match l with
  | nil => nil  
  | h :: t => t
  end.

Example test_hd1:             hd 0 [1;2;3] = 1.
Proof. reflexivity.  Qed.
Example test_hd2:             hd 0 [] = 0.
Proof. reflexivity.  Qed.
Example test_tl:              tl [1;2;3] = [2;3].
Proof. reflexivity.  Qed.

(** **** Ejercicio: 2 stars (list_funs) *)
(** Complete las definiciones de [nonzeros], [oddmembers] y
    [countoddmembers] de mas abajo.  Echele un vistazo a los tests
    para entender que deberian hacer estas funciones. *)

Fixpoint nonzeros (l:natlist) : natlist :=
  (* FILL IN HERE *) admit.

Example test_nonzeros:            nonzeros [0;1;0;2;3;0;0] = [1;2;3].
 (* FILL IN HERE *) Admitted.

Fixpoint oddmembers (l:natlist) : natlist :=
  (* FILL IN HERE *) admit.

Example test_oddmembers:            oddmembers [0;1;0;2;3;0;0] = [1;3].
 (* FILL IN HERE *) Admitted.

Fixpoint countoddmembers (l:natlist) : nat :=
  (* FILL IN HERE *) admit.

Example test_countoddmembers1:    countoddmembers [1;0;3;1;4;5] = 4.
 (* FILL IN HERE *) Admitted.
Example test_countoddmembers2:    countoddmembers [0;2;4] = 0.
 (* FILL IN HERE *) Admitted.
Example test_countoddmembers3:    countoddmembers nil = 0.
 (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Ejercicio: 3 stars, advanced (alternate) *)
(** Complete la definicion de [alternate], que "zippea" dos listas en
    una, alternando entre los elementos tomados de la primera lista y
    los de la segunda.  Mire a los tests abajo para entenderlo con
    ejemplos especificos.

    Nota: una forma natural y elegante de escribir [alternate] puede
    no satisfacer el requerimiento de Coq de que toda definicion
    [Fixpoint] debe ser "obviamente terminante".  Si se encuentra con
    este problema, considere una solucion mas verbosa que considera a
    los elementos de ambas listas a la vez.  (Otra solucion podria ser
    utilizar un tipo diferente de pares, pero esta no es la unica
    forma).  *)


Fixpoint alternate (l1 l2 : natlist) : natlist :=
  (* FILL IN HERE *) admit.


Example test_alternate1:        alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
 (* FILL IN HERE *) Admitted.
Example test_alternate2:        alternate [1] [4;5;6] = [1;4;5;6].
 (* FILL IN HERE *) Admitted.
Example test_alternate3:        alternate [1;2;3] [4] = [1;4;2;3].
 (* FILL IN HERE *) Admitted.
Example test_alternate4:        alternate [] [20;30] = [20;30].
 (* FILL IN HERE *) Admitted. 
(** [] *)

(* ###################################################### *)
(** ** Bolsas ("Bags") via Listas *)

(** Una bolsa "[bag]" (o multiconjunto "[multiset]") es como un
    conjunto, pero cada elemento puede aparecer muchas veces en vez de
    solamente una.  Una forma razonable de implementar bags es
    representandolas como listas de numeros naturales. *)

Definition bag := natlist.  

(** **** Ejercicio: 3 stars (bag_functions) *)
(** Complete las siguientes definiciones para las funciones [count],
    [sum], [add], y [member] para bags. *)

Fixpoint count (v:nat) (s:bag) : nat := 
  (* FILL IN HERE *) admit.

(** Todas estas pruebas deben solucionarse con [reflexivity]. *)

Example test_count1:              count 1 [1;2;3;1;4;1] = 3.
 (* FILL IN HERE *) Admitted.
Example test_count2:              count 6 [1;2;3;1;4;1] = 0.
 (* FILL IN HERE *) Admitted.

(** La operacion [sum] de multiset es similar a la [union] de sets:
    [sum a b] contiene los elementos de [a] y [b].  (Los matematicos
    usualmente definen [union] ligeramente diferente, y por ello no
    usamos el mismo nombre para esta operacion).  Para [sum] le damos
    un hint: no nombre los argumentos de la funcion.  Es mas,
    escribimos [Definition] en vez de [Fixpoint], de forma que si
    incluso persiste en dar nombres para los argumentos, no podra
    procesarlos recursivamente.  El punto de establecer el problema de
    este modo es para promover otras formas de crear esta funcion, tal
    vez utilizando funciones que ya han sido definidas.  *)

Definition sum : bag -> bag -> bag := 
  (* FILL IN HERE *) admit.

Example test_sum1:              count 1 (sum [1;2;3] [1;4;1]) = 3.
 (* FILL IN HERE *) Admitted.

Definition add (v:nat) (s:bag) : bag := 
  (* FILL IN HERE *) admit.

Example test_add1:                count 1 (add 1 [1;4;1]) = 3.
 (* FILL IN HERE *) Admitted.
Example test_add2:                count 5 (add 1 [1;4;1]) = 0.
 (* FILL IN HERE *) Admitted.

Definition member (v:nat) (s:bag) : bool := 
  (* FILL IN HERE *) admit.

Example test_member1:             member 1 [1;4;1] = true.
 (* FILL IN HERE *) Admitted.
Example test_member2:             member 2 [1;4;1] = false.
 (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Ejercicio: 3 stars, optional (bag_more_functions) *)
(** Aqui hay algunas otras funciones sobre bags para que practique. *)

Fixpoint remove_one (v:nat) (s:bag) : bag :=
  (* Cuando remove_one es aplicado a un bag sin el numero en cuestion,
     debe retornar el mismo bag sin cambiar. *)
  (* FILL IN HERE *) admit.

Example test_remove_one1:         count 5 (remove_one 5 [2;1;5;4;1]) = 0.
 (* FILL IN HERE *) Admitted.
Example test_remove_one2:         count 5 (remove_one 5 [2;1;4;1]) = 0.
 (* FILL IN HERE *) Admitted.
Example test_remove_one3:         count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
 (* FILL IN HERE *) Admitted.
Example test_remove_one4:         count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
 (* FILL IN HERE *) Admitted.

Fixpoint remove_all (v:nat) (s:bag) : bag :=
  (* FILL IN HERE *) admit.

Example test_remove_all1:          count 5 (remove_all 5 [2;1;5;4;1]) = 0.
 (* FILL IN HERE *) Admitted.
Example test_remove_all2:          count 5 (remove_all 5 [2;1;4;1]) = 0.
 (* FILL IN HERE *) Admitted.
Example test_remove_all3:          count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
 (* FILL IN HERE *) Admitted.
Example test_remove_all4:          count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
 (* FILL IN HERE *) Admitted.

Fixpoint subset (s1:bag) (s2:bag) : bool :=
  (* FILL IN HERE *) admit.

Example test_subset1:              subset [1;2] [2;1;4;1] = true.
 (* FILL IN HERE *) Admitted.
Example test_subset2:              subset [1;2;2] [2;1;4;1] = false.
 (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Ejercicio: 3 stars (bag_theorem) *)
(** Escriba un teorema interesante sobre bags involucrando las
    funciones [count] y [add], y demuestrelo.  Note que, como el
    problema no esta totalmente especificado, es posible que usted
    cree un teorema que es cierto, pero cuya prueba requira tecnicas
    que no ha aprendido todavia.  Sientase libre de preguntar por
    ayuda si se queda estancado! *)

(* FILL IN HERE *)
(** [] *)

(* ###################################################### *)
(** * Razonando acerca de listas *)

(** De igual manera que con los numeros, se pueden probar muchos hechos
    simples acerca de funciones sobre listas con simplificacion.  Por
    ejemplo, la simplificacion realizada por [reflexivity] es
    suficiente para este teorema... *)

Theorem nil_app : forall l:natlist,
  [] ++ l = l.
Proof. reflexivity. Qed.

(** ... porque el [[]] es sustituido en la posicion del match en la
    definicion de [app], permitiendo que el match pueda ser
    simplificado. *)

(** Tambien, como con los numeros, a veces es util realizar un
    analisis por caso en las posibles formas (vacia o no vacia) que
    puede tener una lista desconocida. *)

Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tl l).
Proof.
  intros l. destruct l as [| n l'].
  Case "l = nil".
    reflexivity.
  Case "l = cons n l'". 
    reflexivity.  Qed.

(** Aqui, el caso para [nil] fuciona porque decidimos definir [tl nil
    = nil].  Note que la anotacion [as] en la tactica [destruct]
    introduce dos nombres, [n] y [l'], correspondiendo al hecho que el
    operador [cons] para listas tomas dos argumentos (la cabeza y cola
    de la lista que se esta construyendo). *)

(** Usualmente, sin embargo, ciertos teoremas interesantes acerca de
    listas requiere induccion para sus pruebas. *)

(* ###################################################### *)
(** ** Micro-Sermon *)

(** Simplemente leer pruebas no le va a permitir llegar muy lejos!  Es
    muy importante entender los pasos involucrados en cada prueba,
    usando Coq y pensando en cada paso que razonamiento se esta
    llevando a cabo.  De otra forma, esta garantizado que los
    ejercicios no van a tener ningun sentido.  *)

(* ###################################################### *)
(** ** Induccion sobre Listas *)

(** Pruebas por induccion en tipos de datos como [natlist] son quizas
    un poco menos familiares que induccion sobre numeros naturales,
    pero la idea basica es la misma.  Cada declaracion [Inductive]
    define un conjunto de constructores que establecen como construir
    un elemento del tipo: un booleano puede ser [true] o [false]; un
    numero puede ser [O] o [S] aplicado a otro numero; una lista puede
    ser [nil] o [cons] aplicado a un numero y una lista.

    Es mas, la aplicacion de los constructores declarados en un tipo
    inductivo a si mismos es la _unica_ forma que los valores del tipo
    inductivo pueden tomar.  Este hecho da forma a un estilo de
    razonamiento acerca conjuntos definidos inductivamente: un numero
    es [O] o es [S] aplicado a otro numero _mas pequenio_; una lista
    es [nil] o [cons] aplicado a un numero y una lista _mas pequnia_;
    etc.  Entonces, si tenemos en mente una proposicion [P] que
    menciona una lista [l] y queremos argumentar que [P] vale para
    _todas_ las listas, podemos razonar de la siguiente manera:

      - Primero, mostrar que [P] es verdadero para [l] cuando [l] es [nil].

      - Luego mostrar que [P] es verdadero para [l] cuando [l] es
        [cons n l'] para algun numero [n] y alguna lista mas chica [l'],
        asumiendo que [P] es verdadero para [l'].

    Como listas largas solo pueden ser construidas de listas mas
    cortas, eventualmente llegando a [nil], estos dos principios
    bastan para establecer la prueba de [P] para toda lista [l].  Aqui
    hay un ejemplo concreto: *)

Theorem app_ass : forall l1 l2 l3 : natlist, 
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).   
Proof.
  intros l1 l2 l3. induction l1 as [| n l1'].
  Case "l1 = nil".
    reflexivity.
  Case "l1 = cons n l1'".
    simpl. rewrite -> IHl1'. reflexivity.  Qed.

(** De vuelta, esta prueba en Coq no es muy iluminadora como documento
    estatico -- es mas facil ver que esta pasando si se esta
    trabajando en una sesion interactiva de Coq, donde se puede ver el
    estado del objetivo actual y su contexto en cada paso, pero este
    estado no es visible en la prueba estatica.  Entonces, la prueba
    en lenguaje natural -- es decir, apta para humanos -- debe incluir
    informacion mas explicita; en particular, puede ayudar recordarle
    al lector cual es la hipotesis inductiva en el segundo caso.  *)

(** _Teorema_: Para todas listas [l1], [l2], y [l3], 
   [(l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3)].

   _Prueba_: Por induccion en [l1].

   - Primero, suponga [l1 = []].  Debemos mostrar
       ([] ++ l2) ++ l3 = [] ++ (l2 ++ l3),
     que se desprende directamente de la definicion de [++].

   - Ahora suponga [l1 = n::l1'], con
       (l1' ++ l2) ++ l3 = l1' ++ (l2 ++ l3)
     (la hipotesis inductiva). Debemos mostrar
       ((n :: l1') ++ l2) ++ l3 = (n :: l1') ++ (l2 ++ l3).
  
     Por definicion de [++], esto se sigue de
       n :: ((l1' ++ l2) ++ l3) = n :: (l1' ++ (l2 ++ l3)),
     que es inmediato utilizando la hipotesis inductiva.  []

  Aqui hay una prueba similar: *)

Theorem app_length : forall l1 l2 : natlist, 
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  (* WORKED IN CLASS *)
  intros l1 l2. induction l1 as [| n l1'].
  Case "l1 = nil".
    reflexivity.
  Case "l1 = cons".
    simpl. rewrite -> IHl1'. reflexivity.  Qed.

(** Para un ejemplo un poco mas complejo sobre induccion en listas,
    suponga que definimos la funcion "cons a la derecha" como... *)

Fixpoint snoc (l:natlist) (v:nat) : natlist := 
  match l with
  | nil    => [v]
  | h :: t => h :: (snoc t v)
  end.

(** ... y la usamos para definir la funcion [rev] para revertir una lista: *)

Fixpoint rev (l:natlist) : natlist := 
  match l with
  | nil    => nil
  | h :: t => snoc (rev t) h
  end.

Example test_rev1:            rev [1;2;3] = [3;2;1].
Proof. reflexivity.  Qed.
Example test_rev2:            rev nil = nil.
Proof. reflexivity.  Qed.

(** Pasemos ahora a probar algunos teoremas sobre las nuevas funciones
    [snoc] y [rev].  Probemos una propiedad un poco mas compleja que
    las que hemos visto hasta ahora, que revertir una lista no cambia
    su largo.  Nuestro primer intento se va a quedar estancado en el
    caso [cons]... *)

Theorem rev_length_firsttry : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l'].
  Case "l = []".
    reflexivity.
  Case "l = n :: l'".
    (* Este es el caso dificil.  Empezemos por simplificar la ecuacion. *)
    simpl. 
    (* Ahora parece que estamos estancados: el objetivo es una
       igualdad involucrando [snoc], pero no tenemos ninguna ecuacion
       en el contexto local o en el ambiente global que diga algo
       sobre [snoc]!

       Podemos hacer un poco de progreso si reescribimos la hipotesis inductiva... *)
    rewrite <- IHl'.
    (* ... pero ya no podemos hacer nada. *)
Abort.

(** Entonces tomemos la ecuacion sobre [snoc] que nos permite hacer
    progreso y provemosla como un lema separado. *)

Theorem length_snoc : forall n : nat, forall l : natlist,
  length (snoc l n) = S (length l).
Proof.
  intros n l. induction l as [| n' l'].
  Case "l = nil".
    reflexivity.
  Case "l = cons n' l'".
    simpl. rewrite -> IHl'. reflexivity.  Qed. 

(** Note que hicimos el lema lo mas _general_ posible: en particular,
    cuantificamos sobre _toda_ [natlist], no solo aquella que resulta
    de la aplicacion de [rev].  Esto debe resultar natural, puesto que
    la verdad del objetivo no depende de que la lista haya sido
    revertida.  Es mas, es mucho mas facil provar la propiedad mas
    general.  *)
    
(** Ahora podemos completar la prueba original. *)

Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l'].
  Case "l = nil".
    reflexivity.
  Case "l = cons".
    simpl. rewrite -> length_snoc. 
    rewrite -> IHl'. reflexivity.  Qed.

(** Para comparar, aqui estan las pruebas informales de estos dos teoremas: 

    _Teorema_: Para todo numero [n] y lista [l],
       [length (snoc l n) = S (length l)].
 
    _Prueba_: Por induccion en [l].

    - Primero, suponga [l = []].  Debemos probar
        length (snoc [] n) = S (length []),
      que resulta inmediato de las definiciones de
      [length] y [snoc].

    - Luego, suponga [l = n'::l'], con
        length (snoc l' n) = S (length l').
      Tenemos que mostrar
        length (snoc (n' :: l') n) = S (length (n' :: l')).
      Por la definicion de [length] y [snoc], esto es equivalente a
        S (length (snoc l' n)) = S (S (length l')),
      que es inmediato por la hipotesis inductiva. [] *)
                        
(** _Teorema_: Para toda lista [l], [length (rev l) = length l].
    
    _Prueba_: Por induccion en [l].  

      - Primero, suponga [l = []].  Debemos mostrar
          length (rev []) = length [],
        que resulta inmediato de considerar las definiciones de [length] 
        y [rev].
    
      - Luego, suponga [l = n::l'], con
          length (rev l') = length l'.
        Tenemos que mostrar que
          length (rev (n :: l')) = length (n :: l').
        Porla definicion de [rev], esto es equivalente a
          length (snoc (rev l') n) = S (length l')
        que, por el lema anterior, es lo mismo que
          S (length (rev l')) = S (length l').
        Concluimos gracias a la hipotesis inductiva. [] *)

(** Obviamente, el estilo de estas pruebas es mas bien verborragica y
    pedante.  Luego de un par, podemos encontrar mas facil de seguir
    pruebas que no muestran tanto detalle (puesto que podemos
    entenderlas en nuestras mentes o en un papel borrador si es
    necesario) y simplemente resaltar los pasos no obvios.  En este
    estilo mas comprimido, la prueba de arriba puede verse mas como:
    *)

(** _Teorema_:
     Para toda lista [l], [length (rev l) = length l].

    _Prueba_: Primero, observe que length (snoc l n) = S (length l)
       para cualquier [l].  Esto se desprende de una simple induccion
       en [l].  La propiedad principal se desprende tambien por otra
       simple induccion en [l], usando la observacion junto con la
       hipotesis inductiva en el caso donde [l = n'::l']. [] *)

(** Que estilo es preferible en una determinada situacion depende en
    la sofisticacion de la audencia y en que tan similar la prueba en
    cuestion sea a otras a las que la audencia se haya ya
    expuesto.  El estilo mas pedante es un buen default por ahora. *)

(* ###################################################### *)
(** ** [SearchAbout] *)

(** Hemos visto que las pruebas pueden hacer uso de otros teoremas que
    ya se han provado, usando [rewrite], y mas tarde vamos a ver otras
    formas de reusar teoremas.  Pero para referirse a un teorema, es
    necesario saber su nombre, y recordar los nombres de todos los
    posibles teoremas que podamos querer usar puede ser una tarea muy
    dificil!  Usualmente es imposible recordar los teoremas que se han
    demostrado; mucho menos sus nombres.

    El comando de Coq [SearchAbout] es bastante util para esto.
    Escribiendo [SearchAbout foo] hace que Coq muestre una lista de
    teoremas involucrando a [foo].  Por ejemplo, observe la lista que
    muestra el siguiente comando, mostrando los teoremas que demostramos
    sobre [rev]: *)

SearchAbout rev.

(** Mantenga [SearchAbout] en mente cuando haga los siguientes
    ejercicios, y durante el resto del curso; puede salvarle mucho
    tiempo!  *)
    


(* ###################################################### *)
(** ** Ejercicios Sobre Listas, Parte 1 *)

(** **** Ejercicio: 3 stars (list_exercises) *)
(** Mas practica sobre listas. *)

Theorem app_nil_end : forall l : natlist, 
  l ++ [] = l.   
Proof.
  (* FILL IN HERE *) Admitted.


Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  (* FILL IN HERE *) Admitted.

(** Hay una solucion corta al siguiente ejercicio.  Si usted se
    encuentra en un embrollo, vuelva atras y busque una solucion mas
    facil. *)

Theorem app_ass4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem snoc_append : forall (l:natlist) (n:nat),
  snoc l n = l ++ [n].
Proof.
  (* FILL IN HERE *) Admitted.


Theorem distr_rev : forall l1 l2 : natlist,
  rev (l1 ++ l2) = (rev l2) ++ (rev l1).
Proof.
  (* FILL IN HERE *) Admitted.

(** Un ejercicio acerca de su implementacion de [nonzeros]: *)

Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ###################################################### *)
(** ** Ejercicios Sobre Listas, Part 2 *)

(** **** Ejercicio: 2 stars (list_design) *)
(** Ejercicio de disenio: 
     - Escriba un teorema no trivial involucrando [cons]
       ([::]), [snoc], y [app] ([++]).  
     - Demuestrelo. *) 

(* FILL IN HERE *)
(** [] *)

(** **** Ejercicio: 3 stars, advanced (bag_proofs) *)
(** Aqui hay un par de pequenios teoremas para demostrar acerca de su
    definicion de bags. *)

Theorem count_member_nonzero : forall (s : bag),
  ble_nat 1 (count 1 (1 :: s)) = true.
Proof.
  (* FILL IN HERE *) Admitted.

(** El siguiente lema acerca [ble_nat] puede ayudarle en la siguiente prueba. *)

Theorem ble_n_Sn : forall n,
  ble_nat n (S n) = true.
Proof.
  intros n. induction n as [| n'].
  Case "0".  
    simpl.  reflexivity.
  Case "S n'".
    simpl.  rewrite IHn'.  reflexivity.  Qed.

Theorem remove_decreases_count: forall (s : bag),
  ble_nat (count 0 (remove_one 0 s)) (count 0 s) = true.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Ejercicio: 3 stars, optional (bag_count_sum) *)  
(** Escriba un teorema interesante acerca de bags involucrando las
    funciones [count] y [sum], y demuestrelo.*)

(* FILL IN HERE *)
(** [] *)

(** **** Ejercicio: 4 stars, advanced (rev_injective) *)
(** Demuestre que la funcion [rev] es injectiva, es decir,

    forall (l1 l2 : natlist), rev l1 = rev l2 -> l1 = l2.

Hay una forma dificil y otra facil de resolver este ejercicio.
*)

(* FILL IN HERE *)
(** [] *)


(* ###################################################### *)
(** * Opciones (Options) *)

(** Aqui hay otra definicion de tipo que es usada comunmente en
    programacion: *)

Inductive natoption : Type :=
  | Some : nat -> natoption
  | None : natoption.  

(** El uso de [natoption] es una forma de retornar "error" en
    funciones.  Por ejemplo, suponga que queremos escribir una funcion
    que retorne el elemento [n]-ario de una lista.  Si le damos tipo
    [nat -> natlist -> nat], entonces vamos a tener que retornar un
    numero arbitrario cuando la lista es muy corta! *)

Fixpoint index_bad (n:nat) (l:natlist) : nat :=
  match l with
  | nil => 42  (* arbitrario! *)
  | a :: l' => match beq_nat n O with 
               | true => a 
               | false => index_bad (pred n) l' 
               end
  end.

(** Por otro lado, si le damos el tipo [nat -> natlist -> natoption],
    entonces podemos retornar [None] cuando la lista es muy corta y
    [Some a] cuando la lista tiene suficientes elementos y [a] aparece
    en la posicion [n]. *)

Fixpoint index (n:nat) (l:natlist) : natoption :=
  match l with
  | nil => None 
  | a :: l' => match beq_nat n O with 
               | true => Some a
               | false => index (pred n) l' 
               end
  end.

Example test_index1 :    index 0 [4;5;6;7]  = Some 4.
Proof. reflexivity.  Qed.
Example test_index2 :    index 3 [4;5;6;7]  = Some 7.
Proof. reflexivity.  Qed.
Example test_index3 :    index 10 [4;5;6;7] = None.
Proof. reflexivity.  Qed.

(** Este ejemplo es una buena oportunidad para traer a colacion otra
    pequenia caracteristica del lenguaje de programacion de Coq: las
    expresiones condicionales... *)

Fixpoint index' (n:nat) (l:natlist) : natoption :=
  match l with
  | nil => None 
  | a :: l' => if beq_nat n O then Some a else index' (pred n) l'
  end.

(** Los condicionales de Coq son como aquellos encontrados en
    cualquier otro lenguaje, con una pequenia generalizacion.  Como el
    tipo booleano no esta insertado en la logica subyacente, Coq
    permite expresiones condicionales de _cualquier_ tipo inductivo
    definido con exactamente dos constructores.  La guarda es
    considerada [true] si evalua al primer constructor en la
    definicion [Inductive] y [false] si evalua al segundo. *)

(** La funcion de abajo extrae el [nat] de un [natoption], retornando
    un default especificado en el caso [None]. *)

Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.

(** **** Ejercicio: 2 stars (hd_opt) *)
(** Usando la misma idea, modifique la funcion [hd] definida
   anteriormente de forma que no tengamos que pasar un elemento por
   default en el caso [nil].  *)

Definition hd_opt (l : natlist) : natoption :=
  (* FILL IN HERE *) admit.

Example test_hd_opt1 : hd_opt [] = None.
 (* FILL IN HERE *) Admitted.

Example test_hd_opt2 : hd_opt [1] = Some 1.
 (* FILL IN HERE *) Admitted.

Example test_hd_opt3 : hd_opt [5;6] = Some 5.
 (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Ejercicio: 1 star, optional (option_elim_hd) *)
(** Este ejercicio relaciona [hd_opt] con el viejo [hd]. *)

Theorem option_elim_hd : forall (l:natlist) (default:nat),
  hd default l = option_elim default (hd_opt l).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Ejercicio: 2 stars (beq_natlist) *)
(** Complete la definicion de [beq_natlist], que compara dos listas de
    numeros por igualdad.  Demuestre que [beq_natlist l l] retorna [true]
    para toda lista [l]. *)

Fixpoint beq_natlist (l1 l2 : natlist) : bool :=
  (* FILL IN HERE *) admit.

Example test_beq_natlist1 :   (beq_natlist nil nil = true).
 (* FILL IN HERE *) Admitted.
Example test_beq_natlist2 :   beq_natlist [1;2;3] [1;2;3] = true.
 (* FILL IN HERE *) Admitted.
Example test_beq_natlist3 :   beq_natlist [1;2;3] [1;2;4] = false.
 (* FILL IN HERE *) Admitted.

Theorem beq_natlist_refl : forall l:natlist,
  true = beq_natlist l l.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ###################################################### *)
(** * Diccionarios *)

(** Como ejemplo final sobre como se pueden definir tipos de datos
    fundamentales, aqui hay una declaracion de un simple tipo de datos
    [dictionary], usando numeros para tanto las claves como los
    valores guardados en esas claves.  (Es decir, un diccionario
    representa un mapeo finito de numeros a numeros).  *)

Module Dictionary.

Inductive dictionary : Type :=
  | empty  : dictionary 
  | record : nat -> nat -> dictionary -> dictionary. 

(** Esta declaracion puede ser leida como: "Hay dos formas de
    construir un [dictionary]: mediante el constructor [empty], para
    representar el diccionario vacio, o mediante el constructor
    [record] aplicado a una clave, un valor, y un [dictionary] ya
    existente, para construir un diccionario con el mapeo clave-valor
    nuevo".  *)

Definition insert (key value : nat) (d : dictionary) : dictionary :=
  (record key value d).

(** Aqui hay una funcion [find] que busca un [dictionary] por una
    determinada clave.  Evalua a [None] si la clave no se encontro, y
    a [Some val] si la clave [key] esta mapeada a [val] en el
    diccionario.  Si la misma clave esta mapeada a multiples valores, [find]
    retorna la primera que encuentra. *)

Fixpoint find (key : nat) (d : dictionary) : natoption := 
  match d with 
  | empty         => None
  | record k v d' => if (beq_nat key k) 
                       then (Some v) 
                       else (find key d')
  end.


(** **** Ejercicio: 1 star (dictionary_invariant1) *)
(** Complete la siguiente prueba. *)

Theorem dictionary_invariant1' : forall (d : dictionary) (k v: nat),
  (find k (insert k v d)) = Some v.
Proof.
 (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Ejercicio: 1 star (dictionary_invariant2) *)
(** Complete la siguiente prueba. *)

Theorem dictionary_invariant2' : forall (d : dictionary) (m n o: nat),
  beq_nat m n = false -> find m d = find m (insert n o d).
Proof.
 (* FILL IN HERE *) Admitted.
(** [] *)



End Dictionary.

End NatList.

(* $Date: 2013-07-17 16:19:11 -0400 (Wed, 17 Jul 2013) $ *)

