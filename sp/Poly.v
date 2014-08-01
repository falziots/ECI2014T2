(** * Poly: Polimorfismo y Funciones de Alto-Orden *)

(** En este capitulo continuamos con el desarrollo de conceptos
    basicos de programacion funcional.  Las ideas nuevas son
    fundamentales: _polimorfismo_ (abstraccion de funciones sobre los
    tipos de datos que manipulan) y _funciones de alto-orden_
    (tratando funciones como datos).  *)

Require Export Lists.   

(* ###################################################### *)
(** * Polimorfismo *)
(* ###################################################### *)
(** ** Listas Polimorficas *)

(** En los ultimos capitulos hemos trabajado con listas de numeros
    unicamente.  Obviamente, programas mas interesantes tambien
    necesitan manipular listas con elementos de otros tipos -- listas
    de strings, listas de booleanos, listas de listas, etc.  Podemos
    definir tipos inductivos para cada uno de ellos, por ejemplo... *)

Inductive boollist : Type :=
  | bool_nil : boollist
  | bool_cons : bool -> boollist -> boollist.

(** ... pero esto rapidamente se convierte tedioso, en parte porque
    tenemos que crear nombres para cada nuevo constructor de cada tipo
    de datos, pero principalmente porque tenemos que definir nuevas
    versiones de todas las funciones manipulando listas ([length],
    [rev], etc.) para cada tipo de dato nuevo. *)

(** Para evitar esta repeticion, Coq soporta definiciones de tipos
    _polimorficas_.  Por ejemplo, aqui esta la definicion de una lista
    _polimorfica_. *)

Inductive list (X:Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.

(** Esto es exactamente como la definicion de [natlist] del capitulo
    anterior, excepto que el argumento [nat] del constructor [cons] ha
    sido reemplazado por un tipo arbitrario [X], que se encuentra
    ligado al [X] definido en el encabezado del tipo, y las
    ocurrencias de [natlist] fueron reemplazadas por [list X].
    (Podemos reusar los nombres de los constructores [nil] y [cons]
    porque hemos puesto las definiciones de [natlist] dentro de una
    definicion [Module] que se encuentra fuera del contexto actual.) *)

(** Que cosa es [list]?  Una forma acertada es pensar que [list] es
    una _funcion_ de tipos [Type] a definiciones inductivas
    [Inductive]; o, para ponerlo de otra forma, [list] es una funcion
    de [Type]s a [Type]s.  Para cualquier [X] particular, el tipo
    [list X] es un tipo definido inductivamente definiendo un conjunto
    de listas cuyos elementos son cosas de tipo [X]. *)

(** Con esta definicion, cuando usamos los constructores [nil] y
    [cons] para construir listas, tenemos que decirle a Coq el tipo de
    los elementos en las listas que estamos construyendo -- es decir,
    [nil] y [cons] son ahora _constructores polimorficos_.  Observe el
    tipo de estos constructores: *)

Check nil.
(* ===> nil : forall X : Type, list X *)
Check cons.
(* ===> cons : forall X : Type, X -> list X -> list X *)

(** El "[forall X]" en estos tipos puede ser leido como un argumento
    adicional a los constructores que determina los tipos esperados en
    los argumentos que siguen.  Cuando [nil] y [cons] son usados,
    estos arguemntos son provistos como cualquier otro.  Por
    ejemplo, la lista conteniendo [2] y [1] se escribe asi: *)

Check (cons nat 2 (cons nat 1 (nil nat))).

(** (Volvemos a escribir [nil] y [cons] explicitamente aqui porque
    todavia no hemos definido la notacion [ [] ] y [::] para la nueva
    version de lista.  Haremos eso en un segundo.) *)

(** Podemos volver atras y hacer polimorficas (o "genericas") las
    versiones de las funciones sobre listas que definimos antes.  Aqui
    esta [length], por ejemplo: *)

Fixpoint length (X:Type) (l:list X) : nat :=
  match l with
  | nil      => 0
  | cons h t => S (length X t)
  end.

(** Note que los usos de [nil] y [cons] en los patrones del [match] no
    requieren ninguna anotacion: Coq ya sabe que la lista [l] contiene
    elementos de tipo [X], con lo que no hay razon para incluir [X] en
    el patron.  (Mas precisamente, el tipo [X] es un parametero de
    toda la definicion de [list], no de cada constructor individual.
    Volveremos a este punto mas adelante.)

    Como con [nil] y [cons], podemos usar [length] aplicandola primero
    a un tipo y luego a una lista: *)

Example test_length1 :
    length nat (cons nat 1 (cons nat 2 (nil nat))) = 2.
Proof. reflexivity.  Qed.

(** Para usar nuestra definicion de [length] con otros tipos de
    listas, simplemente tenemos que instanciar apropiadamente el
    parametro de tipo: *)

Example test_length2 :
    length bool (cons bool true (nil bool)) = 1.
Proof. reflexivity.  Qed.

(** Terminamos esta subseccion reimplementando algunas otras funciones
    estandard sobre listas polimorficas: *)

Fixpoint app (X : Type) (l1 l2 : list X)
                : (list X) :=
  match l1 with
  | nil      => l2
  | cons h t => cons X h (app X t l2)
  end.

Fixpoint snoc (X:Type) (l:list X) (v:X) : (list X) :=
  match l with
  | nil      => cons X v (nil X)
  | cons h t => cons X h (snoc X t v)
  end.

Fixpoint rev (X:Type) (l:list X) : list X :=
  match l with
  | nil      => nil X
  | cons h t => snoc X (rev X t) h
  end.



Example test_rev1 :
    rev nat (cons nat 1 (cons nat 2 (nil nat)))
  = (cons nat 2 (cons nat 1 (nil nat))).
Proof. reflexivity.  Qed.

Example test_rev2:
  rev bool (nil bool) = nil bool.
Proof. reflexivity.  Qed.

Module MumbleBaz.
(** **** Ejercicio: 2 stars (mumble_grumble) *)
(** Considere los siguientes dos tipos inductivos. *)

Inductive mumble : Type :=
  | a : mumble
  | b : mumble -> nat -> mumble
  | c : mumble.
Inductive grumble (X:Type) : Type :=
  | d : mumble -> grumble X
  | e : X -> grumble X.

(** Cual de los siguientes son elementos bien tipados de [grumble X] para
    algun tipo [X]?
      - [d (b a 5)]
      - [d mumble (b a 5)]
      - [d bool (b a 5)]
      - [e bool true]
      - [e mumble (b c 0)]
      - [e bool (b c 0)]
      - [c] 
(* FILL IN HERE *)
[] *)


(** **** Ejercicio: 2 stars (baz_num_elts) *)
(** Considere la siguiente definicion inductiva: *)

Inductive baz : Type :=
   | x : baz -> baz
   | y : baz -> bool -> baz.

(** _Cuantos_ elementos tiene el tipo [baz]? 
(* FILL IN HERE *)
[] *)

End MumbleBaz.

(* ###################################################### *)
(** *** Inferencia de Tipos *)

(** Escribamos de vuelta la definicion de [app], pero esta vez sin
    especificar ninguno de los tipos de los argumentos.  Coq va a
    aceptar esta definicion? *)

Fixpoint app' X l1 l2 : list X :=
  match l1 with
  | nil      => l2
  | cons h t => cons X h (app' X t l2)
  end.

(** En efecto, la acepta.  Veamos que tipo le asigno Coq a [app']: *)

Check app'.
(* ===> forall X : Type, list X -> list X -> list X *)
Check app.
(* ===> forall X : Type, list X -> list X -> list X *)

(** Tiene exactamente el mismo tipo que [app].  Coq utilizo un proceso
    que se llama _inferencia de tipos_ que deduce cual debe ser el
    tipo de [X], [l1], y [l2], basado en como son utilizados.  Por
    ejemplo, como [X] es utilizado como primer argumento de [cons],
    debe ser un [Type], puesto que [cons] espera un [Type] como primer
    argumento; "matcheando" [l1] con [nil] y [cons] significa que debe
    ser una lista; y asi sucesivamente.

    Esta poderosa herramienta significa que no tenemos que escribir
    explicitamente abitacuibes de tipo todo el tiempo, aunque las
    anotaciones de tipos muchas veces son util como documentacion y
    "checkeo de sanidad".  Usted debera encontrar el balance en su
    propio codigo entre un exceso de anotaciones (tantas que distraen
    y confunden), y una falta de anotaciones (que obligan al lector a
    realizar inferencia de tipos en sus cavezas para poder entender su
    codigo).  *)

(* ###################################################### *)
(** *** Sintesis de Argumentos de Tipos *)

(** En cada lugar donde usamos una funcion polimorfica debemos pasar
    uno o mas tipos, ademas de los otros argumentos.  Por ejemplo, en
    la llamada recursiva en el cuerpo de la funcion [length] de arriba
    debemos pasar tambien el tipo [X].  Pero proveer este tipo de
    anotaciones explicitas todo el tiempo es pesado y verborragico.
    Como el segundo argumento de [length] es una lista de [X]s,
    resulta obvio que el primer argumento solo puede ser [X] -- por
    que debemos escribirlo explicitamente?

    Afortunadamente, Coq permite evitar esta clase de redundancia.  En
    lugar de cualquier argumento podemos escribir el "argumento
    implicito" [_], que puede leerse como "Por favor, encontra por mi
    que tipo debe ir aca".  Mas precisamente, cuando Coq encuentra un
    [_], intenta _unificar_ la informacion local a disposicion -- el
    tipo de la funcion siendo aplicada, los tipos de los otros
    argumentos, y el tipo esperado en el contexto en el que la
    aplicacion se encuentra -- para determinar que tipo concreto debe
    reemplazar el [_].

    Esto puede sonar similar a la inferencia de anotaciones de tipos
    -- y, de hecho, los dos procedimientos se basan en los mismos
    mechanismos subyacentes.  En vez de simplemente omitir el tipo de
    algunos argumentos en una funcion, como
      app' X l1 l2 : list X := 
    tambien podemos reemplazar los tipos con [_], como
      app' (X : _) (l1 l2 : _) : list X := 
    que le dice a Coq que intente inferir la informacion faltante,
    exactamente igual a con la sintesis de argumentos.

    Usando argumentos implicitos, la funcion [length] puede ser
    escrita de la siguiente forma: *)

Fixpoint length' (X:Type) (l:list X) : nat :=
  match l with
  | nil      => 0
  | cons h t => S (length' _ t)
  end.

(** En este ejemplo, no salvamos mucho escribiendo [_] en vez de [X].
    Pero en muchos casos la diferencia puede ser significativa.  Por
    ejemplo, suponga que queremos escribir una lista conteniendo los
    numeros [1], [2], y [3].  En vez de escribir... *)

Definition list123 :=
  cons nat 1 (cons nat 2 (cons nat 3 (nil nat))).

(** ...podemos utilizar la sintesis de argumentos y escribir: *)

Definition list123' := cons _ 1 (cons _ 2 (cons _ 3 (nil _))).

(* ###################################################### *)
(** *** Argumentos Implicitos *)

(** De hecho, podemos ir mas lejos.  Para evitar llenar de [_]s en
    todos nuestros programas, podemos decirle a Coq que _siempre_
    infiera los argumentos de tipos de una dada funcion.  La directiva
    [Implicit Arguments] (Coq 8.3) o [Arguments] (Coq 8.4) especifica
    el nombre de la funcion o constructor, y luego la lista de
    argumentos (entre {} o [] dependiendo de la version) indicado que
    tal argumento debe ser tratado como implicito.  *)

(* Coq 8.4
Arguments nil {X}.
Arguments cons {X} _ _.  (* marcar con [_] por cada argumento que no tiene nombre *)
Arguments length {X} l.
Arguments app {X} l1 l2.
Arguments rev {X} l. 
Arguments snoc {X} l v.
*)
(* Coq 8.3 *)
Implicit Arguments nil [[X]].
Implicit Arguments cons [[X]].
Implicit Arguments length [[X]].
Implicit Arguments app [[X]].
Implicit Arguments rev [[X]]. 
Implicit Arguments snoc [[X]].


(* notar: no se requiere nigun _  *)
Definition list123'' := cons 1 (cons 2 (cons 3 nil)).
Check (length list123'').

(** Alternativamente, uno puede declarar un argumento como implicito
    mientras se define la funcion, encerrandolo entre llaves.  Por
    ejemplo: *)

Fixpoint length'' {X:Type} (l:list X) : nat :=
  match l with
  | nil      => 0
  | cons h t => S (length'' t)
  end.

(** (Note que no tenemos que proveer el argumento la llamada recursiva
    de [length'']; de hecho, seria invalido proveer uno).
    Utilizaremos este estilo siempre que sea posible, aunque
    continuaremos utilizando la delcaracion [Argument] para
    constructores inductivos. *)

(** Un pequenio problema al declarar los argumentos como implicitos es
    que, ocasionalmente, Coq no tiene suficiente informacion para
    determinar el argumento de tipo; en tales casos, necesitamos
    decirle a Coq que queremos proveer los argumentos explicitamente
    por esta vez, aunque lo hayamos declarado globalmente como
    [Implicit]o.  Por ejemplo, supongoamos que escribimos esto: *)

(* Definition mynil := nil.  *)

(** Si descomentamos esta definicion, Coq va a darnos un error, porque
    no sabe que tipo darle al argumento de tipo de [nil].  Podemos
    ayudarlo con una declaracion explicita (de forma que Coq tenga mas
    informacion a mano cuando analize la aplicacion implicita de
    [nil]): *)

Definition mynil : list nat := nil.

(** Alternativamente, podemos forzar que los argumentos implicitos
   sean tratados explicitimante prefijando [@] al nombre de la
   funcion.  *)

Check @nil.

Definition mynil' := @nil nat.

(** Usando la sintesis de argumentos y argumentos implicitos, podemos
    definir convenientemente notacion para listas, como antes.  Como
    hicimos el argumento de tipo de los constructores implicitos, Coq
    sabra inferirlo automaticamente cuando usemos las notaciones.*)

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

(** Ahora las listas pueden ser escritas como antes: *)

Definition list123''' := [1; 2; 3].





(* ###################################################### *)
(** *** Ejercicios: Listas Polimorficas *)

(** **** Ejercicio: 2 stars, optional (poly_exercises) *)
(** Aqui hay algunos simples ejercicios, como los del capitulo
   [Lists], para practicar con polimorfismo.  Llene las definiciones y
   complete las pruebas debajo. *)

Fixpoint repeat {X : Type} (n : X) (count : nat) : list X :=
  (* FILL IN HERE *) admit.

Example test_repeat1:
  repeat true 2 = cons true (cons true nil).
 (* FILL IN HERE *) Admitted.

Theorem nil_app : forall X:Type, forall l:list X,
  app [] l = l.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem rev_snoc : forall X : Type,
                     forall v : X,
                     forall s : list X,
  rev (snoc s v) = v :: (rev s).
Proof.
  (* FILL IN HERE *) Admitted.

Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
(* FILL IN HERE *) Admitted.

Theorem snoc_with_append : forall X : Type,
                         forall l1 l2 : list X,
                         forall v : X,
  snoc (l1 ++ l2) v = l1 ++ (snoc l2 v).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ###################################################### *)
(** ** Pares Polimorficos *)

(** Siguiendo el mismo patron, la definicion de tipo que dimos en el
    capitulo anterior para un par de numeros puede generalizarse a
    _pares polimorficos_ (o _productos_): *)

Inductive prod (X Y : Type) : Type :=
  pair : X -> Y -> prod X Y.

(* Coq 8.4
Arguments pair {X} {Y} _ _.
*)
(* Coq 8.3 *)
Implicit Arguments pair [[X] [Y]].

(** Como con listas, hacemos los argumentos de tipo implicitos y
    definimos la notacion familiar. *)

Notation "( x , y )" := (pair x y).

(** Podemos utilizar el mecanismo de [Notation] para definir la
    notacion estandard para el _tipo_ del par: *)

Notation "X * Y" := (prod X Y) : type_scope.

(** (La anotacion [: type_scope] le dice a Coq que esta abreviacion
    debe ser utilizada cuando se "parsean" (consideran) tipos.  Esto
    evita que se superponga con el simbolo de multiplicacion de los
    naturales). *)

(** Nota: es facil al principio confundirse [(x,y)] con [X*Y].
    Recuerde que [(x,y)] es un _valor_ construido de dos valores; [X*Y]
    es un _tipo_ construido con otros dos tipos.  Si [x] tiene tipo
    [X] e [y] tiene tipo [Y], entonces [(x,y)] tiene tipo [X*Y]. *)

(** Las funciones de la primer y segunda proyeccion del par se
    escriben casi como en cualquier otro lenguaje de programacion
    funcional.  *)

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with (x,y) => x end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with (x,y) => y end.

(** La siguiente funcion toma dos listas y las combina en una lista de
    pares.  En muchos lenguajes de programacion, esta funcion es
    llamada [zip].  Aqui la llamamos [combine] por consistencia con la
    libreria estandard de Coq. *)
(** Note de vuelta que la notacion para par puede ser usada en
    expresiones y en patrones... *)

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
           : list (X*Y) :=
  match (lx,ly) with
  | ([],_) => []
  | (_,[]) => []
  | (x::tx, y::ty) => (x,y) :: (combine tx ty)
  end.

(** **** Ejercicio: 1 star, opcional (combine_checks) *)
(** Trate respondiendo la siguiente pregunta en papel y verificar sus
    respuestas en Coq:
    - Cual es el tipo de [combine] (es decir, que retorna [Check
      @combine]?)
    - Que responde
        Eval compute in (combine [1;2] [false;false;true;true]).
      ?
*)

(** **** Ejercicio: 2 stars (split) *)
(** La funcion [split] es el inverso de [combine]: toma una lista de
    pares y retorna ina lista de listas.  En muchos lenguajes de
    programacion funcionales, esta funcion se llama [unzip].

    Complete la definicion de [split].  Asegurese que pasa los test
    unitarios dados. *)

Fixpoint split
           {X Y : Type} (l : list (X*Y))
           : (list X) * (list Y) :=
(* FILL IN HERE *) admit.

Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(* ###################################################### *)
(** ** "Options" Polimorficos *)

(** Un ultimo tipo polimorfico por el momento: _opciones
    polimorficas_.  La declarcion de tipo generaliza la que dimos para
    [natoption] en el capitulo anterior: *)

Inductive option (X:Type) : Type :=
  | Some : X -> option X
  | None : option X.

(* Coq 8.4
Arguments Some {X} _. 
Arguments None {X}. 
*)
(* Coq 8.3 *)
Implicit Arguments Some [[X]]. 
Implicit Arguments None [[X]]. 


(** Ahora podemos reescribir la funcion [index] para que funcione con
    cualquier tipo de listas.  *)

Fixpoint index {X : Type} (n : nat)
               (l : list X) : option X :=
  match l with
  | [] => None
  | a :: l' => if beq_nat n O then Some a else index (pred n) l'
  end.

Example test_index1 :    index 0 [4;5;6;7]  = Some 4.
Proof. reflexivity.  Qed.
Example test_index2 :    index  1 [[1];[2]]  = Some [2].
Proof. reflexivity.  Qed.
Example test_index3 :    index  2 [true]  = None.
Proof. reflexivity.  Qed.

(** **** Ejercicio: 1 star, opcional (hd_opt_poly) *)
(** Complete la definicion de una version polimorfica de la funcion
    [hd_opt] del capitulo anterior.  Asegurese que pase los tests
    unitarios de abajo.  *)

Definition hd_opt {X : Type} (l : list X)  : option X :=
  (* FILL IN HERE *) admit.

(** De vuelta, para forzar a Coq a hacer explicitos los argumentos
    implicitos podemos usar [@] antes del nombre de la funcion.  *)

Check @hd_opt.

Example test_hd_opt1 :  hd_opt [1;2] = Some 1.
 (* FILL IN HERE *) Admitted.
Example test_hd_opt2 :   hd_opt  [[1];[2]]  = Some [1].
 (* FILL IN HERE *) Admitted.
(** [] *)

(* ###################################################### *)
(** * Funciones como Datos *)
(* ###################################################### *)
(** ** Funciones de Alto-Orden *)

(** Como muchos lenguajes de programacion modernos -- incluyendo
    _todos_ los lenguajes de programacion funcionales (ML, Haskell,
    Scheme, etc.) -- Coq trata a las funciones como ciudadanos de
    primera, permitiendo a las funciones ser pasadas como argumentos
    de otras funciones, retornadas como resultado, almacenadas en
    tipos de datos, etc.

    Las funciones que manipulan otras funciones se llaman usalmente
    funciones de _alto-orden_.  Aqui hay un ejemplo sencillo: *)

Definition doit3times {X:Type} (f:X->X) (n:X) : X :=
  f (f (f n)).

(** El argumento [f] aqui es en si mismo una funcion (de [X] a [X]);
    el cuerpo de [doit3times] aplica [f] tres veces a algun valor
    [n]. *)

Check @doit3times.
(* ===> doit3times : forall X : Type, (X -> X) -> X -> X *)

Example test_doit3times: doit3times minustwo 9 = 3.
Proof. reflexivity.  Qed.

Example test_doit3times': doit3times negb true = false.
Proof. reflexivity.  Qed.

(* ###################################################### *)
(** ** Aplicacion Parcial *)

(** De hecho, las funciones con varios argumentos que vimos son de por
    si ejemplos de funciones que utilizan funciones como datos.  Para
    ver porque, recuerde el tipo de [plus]. *)

Check plus.
(* ==> nat -> nat -> nat *)

(** Cada [->] en esta expresion es, de hecho, un operador _binario_ en
    tipos.  (Esto es lo mismo que decir que Coq primitivamente acepta
    solo funciones con un solo argumento -- puede ver porque?)  Este
    operador es _asociado a derecha_, con lo que el tipo de [plus] es
    realmente una version corta de [nat -> (nat -> nat)] -- es decir,
    puede ser leido como "[plus] es una funcion con un argumento que
    toma un natural y retorna una funcion con un argumento de tipo
    [nat] que retorna un [nat]".  En los ejemplos de arriba, siempre
    aplicamos [plus] a ambos de sus argumentos a la vez, pero si
    queremos podemos suplir solo el primer argumento.  Esto se llama
    _aplicacion parcial_. *)

Definition plus3 := plus 3.
Check plus3.

Example test_plus3 :    plus3 4 = 7.
Proof. reflexivity.  Qed.
Example test_plus3' :   doit3times plus3 0 = 9.
Proof. reflexivity.  Qed.
Example test_plus3'' :  doit3times (plus 3) 0 = 9.
Proof. reflexivity.  Qed.

(* ###################################################### *)
(** ** Disgresion: Currificacion *)

(** **** Ejercicio: 2 stars, avanzado (currying) *)
(** En Coq, una funcion [f : A -> B -> C] realmente tiene tipo [A ->
    (B -> C)].  Es decir, si se provee a [f] un valor de tipo [A],
    retorna un valor [f' : B -> C].  Si entonces se le provee a [f']
    un valor de tipo [B], va a retornar un valor de tipo [C].  Esto
    permite aplicaciones parciales, como en [plus3].  Procesar una
    lista de argumentos con funciones que retornan funciones se llama
    _currificacion_, en honor al logico Haskell Curry.

    Contrariamente, podemos reinterpretar el tipo [A -> B -> C] como
    [(A * B) -> C].  Esot es llamado _descurryficacion_.  Con una
    funcion binaria descurrificada, ambos argumentos son dados de una
    como un par; no admite aplicacion parcial.  *)

(** Podemos definir currificacion de la siguiente manera: *)

Definition prod_curry {X Y Z : Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

(** Como ejercicio, defina su inverso, [prod_uncurry].  Luego
    demuestre el teorma de abajo de que ambas son inversas.  *)

Definition prod_uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (p : X * Y) : Z :=
  (* FILL IN HERE *) admit.

(** (Ejercicio mental: antes de ejecutar estos comandos, puede
    calcular los tipos de [prod_curry] y [prod_uncurry]?) *)

Check @prod_curry.
Check @prod_uncurry.

Theorem uncurry_curry : forall (X Y Z : Type) (f : X -> Y -> Z) x y,
  prod_curry (prod_uncurry f) x y = f x y.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem curry_uncurry : forall (X Y Z : Type)
                               (f : (X * Y) -> Z) (p : X * Y),
  prod_uncurry (prod_curry f) p = f p.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ###################################################### *)
(** ** Filtro *)

(** Aqui hay una funcion de alto-orden muy util, que toma una lista de
    [X]s y un _predicado_ booleano en [X] (una funcion de [X] a
    [bool]) que "filtra" la lista, retornando una nueva lista
    conteniendo solo aquellos elementos para los cuales el predicado
    retorna [true]. *)

Fixpoint filter {X:Type} (test: X->bool) (l:list X)
                : (list X) :=
  match l with
  | []     => []
  | h :: t => if test h then h :: (filter test t)
                        else       filter test t
  end.

(** Por ejemplo, si aplicamos [filter] al predicado [evenb] y una
    lista de numeros [l], retorna una lista conteniendo solo los
    numeros pares de [l].  *)

Example test_filter1: filter evenb [1;2;3;4] = [2;4].
Proof. reflexivity.  Qed.

Definition length_is_1 {X : Type} (l : list X) : bool :=
  beq_nat (length l) 1.

Example test_filter2:
    filter length_is_1
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity.  Qed.

(** Podemos usar [filter] para dar una version concisa de la funcion
    [countoddmembers] del capitulo [Lists]. *)

Definition countoddmembers' (l:list nat) : nat :=
  length (filter oddb l).

Example test_countoddmembers'1:   countoddmembers' [1;0;3;1;4;5] = 4.
Proof. reflexivity.  Qed.
Example test_countoddmembers'2:   countoddmembers' [0;2;4] = 0.
Proof. reflexivity.  Qed.
Example test_countoddmembers'3:   countoddmembers' nil = 0.
Proof. reflexivity.  Qed.

(* ###################################################### *)
(** ** Funciones Anonimas *)

(** Es un poco molesto estar obligado a definir una funcion
    [length_is_1] y darle un nombre solo para poder pasarla como
    argumento de [filter], puesto que posiblemente no la volvamos a
    usar de vuelta.  Es mas, esto no es un caso aislado.  Cuando las
    funciones de alto-orden se utilizan continuamente, es comun pasar
    funciones que jamas vamos a usar en otros contextos; tener que dar
    un nombre a cada una de estas funciones es tedioso.

    Por suerte, hay forma de hacer esto mejor.  Es posible construir
    una funcion "al vuelo" sin declararla en el "nivel superior" (top
    level, donde se declaran las funciones) ni darle un nombre. *)

Example test_anon_fun':
  doit3times (fun n => n * n) 2 = 256.
Proof. reflexivity.  Qed.

(** Reescribimos el ejemplo motivador de antes, ahora utilizando una
    funcion anonima. *)

Example test_filter2':
    filter (fun l => beq_nat (length l) 1)
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity.  Qed.

(** **** Ejercicio: 2 stars (filter_even_gt7) *)

(** Use [filter] (en vez de [Fixpoint]) para escribir una funcion en
    Coq [filter_even_gt7] que toma una lista de numeros naturales y
    retorna una lista de solo aquellos numeros que son mayores que
    7. *)

Definition filter_even_gt7 (l : list nat) : list nat :=
  (* FILL IN HERE *) admit.

Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
 (* FILL IN HERE *) Admitted.

Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
 (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Ejercicio: 3 stars (partition) *)
(** Use [filter] para escribir una funcion [partition]: partition :
  forall X : Type, (X -> bool) -> list X -> list X * list X Dado un
  conjunto [X], una funcion de tipo [X -> bool] y una [list X],
  [partition] debe retornar un par de listas.  El primer elemento del
  par es la sublista de la lista original conteniendo los elementos
  que satisfagan el test, y el segundo los que no.  El orden de los
  elementos en ambas listas debe respetar el orden que tenian en la
  lista original.  *)

Definition partition {X : Type} (test : X -> bool) (l : list X)
                     : list X * list X :=
(* FILL IN HERE *) admit.

Example test_partition1: partition oddb [1;2;3;4;5] = ([1;3;5], [2;4]).
(* FILL IN HERE *) Admitted.
Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
(* FILL IN HERE *) Admitted.
(** [] *)

(* ###################################################### *)
(** ** Map *)

(** Otra funcion de alto-orden util, [map]. *)

Fixpoint map {X Y:Type} (f:X->Y) (l:list X)
             : (list Y) :=
  match l with
  | []     => []
  | h :: t => (f h) :: (map f t)
  end.

(** Toma una funcion [f] y una lista [ l = [n1, n2, n3, ...] ] y
    retorna la lista [ [f n1, f n2, f n3,...] ], donde [f] ha sido
    aplicada a cada elemento de [l].  Por ejemplo: *)

Example test_map1: map (plus 3) [2;0;2] = [5;3;5].
Proof. reflexivity.  Qed.

(** Los tipos de los elementos de las listas de entrada y salida no
    tienen porque ser los mismos ([map] toma _dos_ argumentos de
    tipos, [X] e [Y]).  Esta version de [map] puede ser aplicada
    entonces a una lista de numeros y una funcion de numeros a
    booleanos y retornar una lista de booleanos: *)

Example test_map2: map oddb [2;1;2;5] = [false;true;false;true].
Proof. reflexivity.  Qed.

(** Incluso puede ser aplicada a una lista de numeros y una funcion de
    numeros a _listas_ de booleanos y retornar una lista de listas de
    booleanos: *)

Example test_map3:
    map (fun n => [evenb n;oddb n]) [2;1;2;5]
  = [[true;false];[false;true];[true;false];[false;true]].
Proof. reflexivity.  Qed.



(** **** Ejercicio: 3 stars (map_rev) *)
(** Muestre que [map] y [rev] conmuta.  Usted puede necesitar definir
    un lema auxiliar. *)


Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Ejercicio: 2 stars (flat_map) *)
(** La funcion [map] mapea una [list X] a una [list Y] usando una
    funcion de tipo [X -> Y].  Podemos definir una funcion similar,
    [flat_map], que mapea una [list X] a una [list Y] usando una
    funcion [f] de tipo [X -> list Y].  Su definicion debe funcionar
    'aplastando' ('flattening' en ingles) los resultados de [f], como
    en: [flat_map (fun n => [n;n+1;n+2]) [1;5;10] = [1; 2; 3; 5; 6; 7;
    10; 11; 12]].  *)

Fixpoint flat_map {X Y:Type} (f:X -> list Y) (l:list X)
                   : (list Y) :=
  (* FILL IN HERE *) admit.

Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
 (* FILL IN HERE *) Admitted.
(** [] *)

(** La funcion [map] no es exclisiva de la listas.  Aqui hay una
    definicion para el tipo [option]: *)

Definition option_map {X Y : Type} (f : X -> Y) (xo : option X)
                      : option Y :=
  match xo with
    | None => None
    | Some x => Some (f x)
  end.

(** **** Ejercicio: 2 stars, opcional (implicit_args) *)
(** Las definiciones y usos de [filter] y [map] usan argumentos
    implicitos en muchos lugares.  Reemplace las llaves ({}) alrededor
    de los argumentos implicitos por parentesis, y llene los
    parametros explicitamente donde sea necesario.  Verifique con Coq
    que lo haya hecho correctamente.  (Este ejercicio no se debe
    entregar; posiblemente sea mas facil trabajar sobre una _copia_ de
    este archivo que puede descartar una vez terminado el
    ejercicio). *)

(* ###################################################### *)
(** ** Fold *)

(** Una funcion de alto-orden incluso mas poderosa es llamada [fold].
    Esta funcion es la inspiracion de la operacion "[reduce]" que es
    parte central del framework de programacion distribuida de Google
    llamado map/reduce . *)

Fixpoint fold {X Y:Type} (f: X->Y->Y) (l:list X) (b:Y) : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.


(** Intuitivamente, el comportamiento de la operacion [fold] es
    insertar el operador binario [f] entre cada par de elementos de
    una lista dada.  Por ejemplo, [ fold plus [1;2;3;4] ] significa
    intuitivamente [1+2+3+4].  Para hacer esto mas preciso, tambien
    necesitamos un "elemento de inicio" que sirve como input inicial a
    [f].  De esta forma, por ejemplo, [ fold plus [1;2;3;4] 0 ]
    retorna [1 + (2 + (3 + (4 + 0)))].  Aqui hay mas ejemplos: *)

Check (fold andb).
(* ===> fold andb : list bool -> bool -> bool *)

Example fold_example1 : fold mult [1;2;3;4] 1 = 24.
Proof. reflexivity. Qed.

Example fold_example2 : fold andb [true;true;false;true] true = false.
Proof. reflexivity. Qed.

Example fold_example3 : fold app [[1];[];[2;3];[4]] [] = [1;2;3;4].
Proof. reflexivity. Qed.


(** **** Ejercicio: 1 star, avanzado (fold_types_different) *)
(** Observe que el tipo de [fold] esta parametrizado por _dos_
    variables de tipo, [X] e [Y], y que el parametro [f] es un
    operador binario que toma un [X] y un [Y] y retorna un [Y].  Puede
    pensar una situacion donde es util que [X] e [Y] sean diferentes?
    *)

(* ###################################################### *)
(** ** Funciones Para Construir Funciones *)

(** La mayoria de las funciones de alto-orden que hemos mencionado
    hasta ahora toman funciones como _argumentos_.  Ahora veamos
    algunos ejemplos de funciones _retornando_ funciones.

    Para empezar, aqui hay una funcion que toma un valor [x] (de algun
    tipo [X]) y retorna una funcion de [nat] a [X] que retorna [x]
    cuando es invocada, ignorando su argumento de tipo [nat].  *)

Definition constfun {X: Type} (x: X) : nat->X :=
  fun (k:nat) => x.

Definition ftrue := constfun true.

Example constfun_example1 : ftrue 0 = true.
Proof. reflexivity. Qed.

Example constfun_example2 : (constfun 5) 99 = 5.
Proof. reflexivity. Qed.

(** Similarmente, pero un poco mas interesantemente, aqui hay una
    funcion que toma una funcion [f] de numeros a algun tipo [X], un
    numero [k], y un valor [x], y construye una funcion que se
    comporta exactamente como [f] excepto que, cuando es llamada con
    el argumento [k], retorna [x].  *)

Definition override {X: Type} (f: nat->X) (k:nat) (x:X) : nat->X:=
  fun (k':nat) => if beq_nat k k' then x else f k'.

(** Por ejemplo, podemos aplicar [override] dos veces para obtener una
    funcion de numeros a booleanos que retorne [false] en [1] y [3]
    y retorne [true] en cualquier otro argumento. *)

Definition fmostlytrue := override (override ftrue 1 false) 3 false.

Example override_example1 : fmostlytrue 0 = true.
Proof. reflexivity. Qed.

Example override_example2 : fmostlytrue 1 = false.
Proof. reflexivity. Qed.

Example override_example3 : fmostlytrue 2 = true.
Proof. reflexivity. Qed.

Example override_example4 : fmostlytrue 3 = false.
Proof. reflexivity. Qed.

(** **** Ejercicio: 1 star (override_example) *)
(** Antes de empezar a trabajar en la demostracion a continuacion,
    asegurese que entiende exactamente lo que el teorema esta
    diciendo, y expliquecelo en sus propias palabras.  La prueba en si
    es sencilla. *)

Theorem override_example : forall (b:bool),
  (override (constfun b) 3 true) 2 = b.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** Usaremos la funcion [override] significativamente en el resto del
    curso, con lo que necesitaremos saber bastante acerca de sus
    propiedades.  Pero para poder probar estas propiedades, vamos a
    necesitar manejar varias tacticas de Coq.  Aprender estas tacticas
    va a ser el punto principal del capitulo siguiente.  Por ahora,
    vamos a introducir solo una tactica extremadamente util, que nos
    va a ayudar a probar algunas propiedades de las funciones que ya
    vimos en este capitulo. *)

(* ###################################################### *)
(** * La Tactica [unfold] *)

(** A veces, una demostracion puede quedarse trabada porque Coq no
    expande automaticamente una llamada a funcion en su definicion.
    (Esto es una caracteristica deseada de Coq, no un bug: si Coq
    expandiera automaticamente todo, los objetivos de prueba se
    volverian enormes rapidamente -- dificiles de leer y pesados de
    manipular para Coq!)  *)

Theorem unfold_example_bad : forall m n,
  3 + n = m ->
  plus3 n + 1 = m + 1.
Proof.
  intros m n H.
(* En este punto quisieramos hacer [rewrite -> H], puesto que 
     [plus3 n] es definicionalmente igual a [3 + n].  Sin embargo, 
     Coq no expande automaticamente [plus3 n] a su definicion. *)
  Abort.

(** La tactica [unfold] puede ser utilizada explicitamente para
    reemplazar un nombre definido por el lado derecho de su
    definicion.  *)

Theorem unfold_example : forall m n,
  3 + n = m ->
  plus3 n + 1 = m + 1.
Proof.
  intros m n H.
  unfold plus3.
  rewrite -> H.
  reflexivity.  Qed.

(** Ahora podemos probar la primer propiedad de [override]: Si
    sobreescribimos (override) una funcion en un valor [k] y luego
    miramos [k], obtenemos el valor sobreescrito. *)

Theorem override_eq : forall {X:Type} x k (f:nat->X),
  (override f k x) k = x.
Proof.
  intros X x k f.
  unfold override.
  rewrite <- beq_nat_refl.
  reflexivity.  Qed.

(** Esta prueba fue facil, pero note que requiere [unfold] para
    expandir la definicion de [override]. *)

(** **** Ejercicio: 2 stars (override_neq) *)
Theorem override_neq : forall (X:Type) x1 x2 k1 k2 (f : nat->X),
  f k1 = x1 ->
  beq_nat k2 k1 = false ->
  (override f k2 x2) k1 = x1.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** Como la inversa de [unfold], Coq provee tambien una tactica
    [fold], que puede ser utilizada para "desexpandir" una definicion.
    Es utilizada bastante menos frecuentemente.  *)

(* ##################################################### *)
(** * Ejercicios Adicionales *)

(** **** Ejercicio: 2 stars (fold_length) *)
(** Muchas funciones comunes sobre listas pueden ser implementadas en
   terminos de [fold].  Por ejemplo, aqui hay una definicion
   alternativa de [length]: *)

Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.

Example test_fold_length1 : fold_length [4;7;0] = 3.
Proof. reflexivity. Qed.

(** Demuestre la correctitud de [fold_length]. *)

Theorem fold_length_correct : forall X (l : list X),
  fold_length l = length l.
(* FILL IN HERE *) Admitted. 
(** [] *)

(** **** Ejercicio: 3 stars (fold_map) *)
(** Podemos definir tambien [map] en terminos de [fold].  Complete [fold_map]
    abajo. *)

Definition fold_map {X Y:Type} (f : X -> Y) (l : list X) : list Y :=
(* FILL IN HERE *) admit.

(** Escriba un teorema en Coq estableciendo que [fold_map] es correcto
    y demuestrelo. *)

(* FILL IN HERE *)
(** [] *)

(* $Date: 2013-07-17 16:19:11 -0400 (Wed, 17 Jul 2013) $ *)

