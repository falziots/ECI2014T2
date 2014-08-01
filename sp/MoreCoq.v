(** * MoreCoq: Mas Sobre Coq *)

Require Export Poly.

(** Este capitulo introduce varias tacticas que, en conjunto, nos
    ayudan a demostrar muchos teoremas sobre los programas funcionales
    que estuvimos escribiendo.  *)

(* ###################################################### *)
(** * La Tactica [apply] *)

(** Usualmente nos encontramos en situaciones en que el objetivo a ser
    demostrado es exactamente lo mismo que alguna hipotesis en el
    contexto o un lema previo. *)

Theorem silly1 : forall (n m o p : nat),
     n = m  ->
     [n;o] = [n;p] ->
     [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1.
  (* En este punto, podemos concluir con
     "[rewrite -> eq2. reflexivity.]" como hemos hecho varias veces
     anteriormente.  Pero podemos lograr lo mismo en un solo paso
     usando la tactica [apply]: *)
  apply eq2.  Qed.

(** La tactica [apply] tambien funciona con hipotesis _condicionales_
    y lemas: si el lema siendo aplicado es una implicacion, entonces
    las premisas de esta implicacion van a ser agregadas a nuestra
    lista de sub-objetivos a demostrar. *)

Theorem silly2 : forall (n m o p : nat),
     n = m  ->
     (forall (q r : nat), q = r -> [q;o] = [r;p]) ->
     [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2. 
  apply eq2. apply eq1.  Qed.

(** Puede encontrar instructivo experimentar con esta prueba y ver si
    existe forma de utilizar [rewrite] para resolverla, en vez de
    [apply]. *)

(** Tipicamente, cuando usamos [apply H], el lema (o hipotesis) [H] va
    a comenzar con un ligador [forall] ligando _variables
    universales_.  Cuando Coq "matchea" (unifica) el objetivo actual
    contra la conclusion de [H], va a intentar encontrar valores
    apropiados para estas variables.  Por ejemplo, cuando hacemos
    [apply eq2] en la siguente prueba, la variable universal [q] en
    [eq2] es instanciada con [n] y [r] es instanciada con [m]. *)

Theorem silly2a : forall (n m : nat),
     (n,n) = (m,m)  ->
     (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
     [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1.  Qed.

(** **** Ejercicio: 2 stars, opcional (silly_ex) *)
(** Complete la siguiente prueba sin utilizar [simpl]. *)

Theorem silly_ex : 
     (forall n, evenb n = true -> oddb (S n) = true) ->
     evenb 3 = true ->
     oddb 4 = true.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** Para usar la tactica [apply], la (conclusion del) lema siendo
    aplicado tiene que matchear el objetivo _exactamente_ -- por
    ejemplo, [apply] no va a funcionar si el lado izquierdo y el lado
    derecho de la igualdad estan intercambiados. *)

Theorem silly3_firsttry : forall (n : nat),
     true = beq_nat n 5  ->
     beq_nat (S (S n)) 7 = true.
Proof.
  intros n H.
  simpl.
  (* Aqui no podemos utilizar la tactica [apply] directamente *)
Abort.

(** En este caso podemos utilizar la tactica [symmetry], que
    intercambia los lados izquierdo y derecho de una igualdad en el
    objetivo.  *)

Theorem silly3 : forall (n : nat),
     true = beq_nat n 5  ->
     beq_nat (S (S n)) 7 = true.
Proof.
  intros n H.
  symmetry.
  simpl. (* De hecho, este [simpl] no es necesario, puesto 
            que [apply] hace un paso de [simpl] primero. *)  
  apply H.  Qed.         

(** **** Ejercicio: 3 stars (apply_exercise1) *)
(** Ayuda: usted puede usar [apply] con lemas definidos previamente,
    no solo hipotesis en el contexto.  Recuerde que [SearchAbout] es
    su amigo! *)

Theorem rev_exercise1 : forall (l l' : list nat),
     l = rev l' ->
     l' = rev l.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Ejercicio: 1 star, optional (apply_rewrite) *)
(** Explique brevemente la diferencia entre las tacticas [apply] y
    [rewrite].  Hay situaciones en las que ambas puedan ser
    exitosamente aplicadas?
  (* FILL IN HERE *)
*)
(** [] *)


(* ###################################################### *)
(** * La Tactica [apply ... with ...] *)

(** El siguiente ejemplo tonto utiliza dos rewrites seguidos para ir
    de [[a,b]] a [[e,f]]. *)

Example trans_eq_example : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2. 
  rewrite -> eq1. rewrite -> eq2. reflexivity.  Qed.

(** Como es comun tener este tipo de situaciones, podemos abstraer en
    un lema el hecho de que la igualdad es transitiva.  *)

Theorem trans_eq : forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. rewrite -> eq1. rewrite -> eq2. 
  reflexivity.  Qed.

(** Ahora, deberiamos poder utilizar [trans_eq] para provar el ejemplo
    de mas arriba.  Sin embargo, para hacer esto necesitamos una
    pequenia variacion de la tactica [apply].  *)

Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2. 
  (* Si le decimos a Coq simplemente [apply trans_eq] en este punto,
     puede deducir (mediante el matcheo del objetivo con la conclusion
     del lema) que debe instanciar [X] con [[nat]], [n] con [[a,b]], y
     [o] con [[e,f]].  Sin embargo, el proceso de matcheo no determina
     una instanciacion para [m]: tenemos que suplir uno explicitamnete
     agregando [with (m:=[c,d])] a la invocacion de [apply]. *)
     apply trans_eq with (m:=[c;d]). apply eq1. apply eq2.  Qed.

(** De hecho, usualmente no tenemos que incluir el nombre [m] en la
    clausula [with]; Coq es muchas veces inteligente y puede darse
    cuenta de que instanciacion estamos proveyendo.  Podemos escribir
    entonces: [apply trans_eq with [c,d]]. *)

(** **** Ejercicio: 3 stars, opcional (apply_with_exercise) *)
Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o). 
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)


(* ###################################################### *)
(** * La Tactica [inversion] *)

(** Recuerde la definicion de numeros naturales:
     Inductive nat : Type :=
       | O : nat
       | S : nat -> nat.

    Es claro de esta definicion que cada numero tiene una de dos
    formas: o es el constructor [O] o esta construido a partir de
    aplicar el constructor [S] a otro numero.  Pero hay mas aqui que
    lo que el ojo puede ver: implicito en esta definicion (y en
    nuestra forma de entender informalmente como las declaraciones de
    tipo funcionan en otros lenguajes de programacion) tambien hay
    otros dos hechos:

    - El constructor [S] es _inyectivo_.  Es decir, la unica forma de
      tener [S n = S m] es si [n = m].

    - Los constructores [O] y [S] son _disjuntos_.  Es decir, [O] no
      es igual a [S n] para ningun [n]. *)

(** Principios similares se aplican a todos los tipos definidos
    inductivamente: todos los constructores son inyectivos, y los
    valores construidos con distintos constructores son diferentes.
    Para listas, el constructor [cons] es inyectivo y [nil] es
    diferente de cualquier lista no vacia.  Para booleanos, [true] and
    [false] son diferentes.  (Como [true] y [false] no toman ningun
    argumento, su inyectividad es irrelevante). *)

(** Coq provee una tactica llamada [inversion] que nos permite
    explotar estos principios en una prueba.
 
    La tactica [inversion] es usada de la siguiente forma.  Suponga
    que [H] es una hipotesis en el context (o un lema ya establecido)
    de la forma
      c a1 a2 ... an = d b1 b2 ... bm
    para dos constructores [c] y [d] y argumentos [a1 ... an] y [b1
    ... bm].  Entonces [inversion H] instruye a Coq a "invertir" esta
    igualdad para extraer la informacion que contiene acerca de estos
    terminos:

    - Si [c] y [d] son el mismo constructor, entonces sabemos, por el
      principio de inyectividad de este constructor, que [a1 = b1],
      [a2 = b2], etc.; [inversion H] agrega estos conocimientos al
      contexto, e intenta utilizarlos para reescribir el objetivo.

    - Si [c] y [d] son constructores diferentes, entonces la hipotesis
      [H] es contradictoria.  Es decir, una premisa falsa ha aparecido
      en nuestro contexto, y esto significa que cualquier objetivo es
      demostrable!  En este caso, [inversion H] marca el objetivo
      actual como completo y lo saca del stack de objetivos por
      resolver. *)

(** Posiblemente la tactica [inversion] sea mas facil de entender
    viendola en accion que en descripciones generales como la de
    arriba.  Abajo va a encontrar ejemplos de teoremas que muestran el
    uso de [inversion] y ejercicios para probar su entendimiento.  *)

Theorem eq_add_S : forall (n m : nat),
     S n = S m ->
     n = m.
Proof.
  intros n m eq. inversion eq. reflexivity.  Qed.

Theorem silly4 : forall (n m : nat),
     [n] = [m] ->
     n = m.
Proof.
  intros n o eq. inversion eq. reflexivity.  Qed.

(** Como conveniencia, la tactica [inversion] tambien puede destruir
    igualdades entre valores complejos, ligando multiples variables a
    la vez. *)

Theorem silly5 : forall (n m o : nat),
     [n;m] = [o;o] ->
     [n] = [m].
Proof.
  intros n m o eq. inversion eq. reflexivity. Qed.

(** **** Ejercicio: 1 star (sillyex1) *) 
Example sillyex1 : forall (X : Type) (x y z : X) (l j : list X),
     x :: y :: l = z :: j ->
     y :: l = x :: j ->
     x = y.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

Theorem silly6 : forall (n : nat),
     S n = O ->
     2 + 2 = 5.
Proof.
  intros n contra. inversion contra. Qed.

Theorem silly7 : forall (n m : nat),
     false = true ->
     [n] = [m].
Proof.
  intros n m contra. inversion contra.  Qed.

(** **** Ejercicio: 1 star (sillyex2) *)
Example sillyex2 : forall (X : Type) (x y z : X) (l j : list X),
     x :: y :: l = [] ->
     y :: l = z :: j ->
     x = z.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** Mientras que la inyectividad de los constructores nos permite
    razonar acerca de [forall (n m : nat), S n = S m -> n = m], la
    direccion inversa de la implicacion es una instancia de un caso
    mas general acerca de constructores y funciones, que vamos a
    encontrar util: *)

Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A), 
    x = y -> f x = f y. 
Proof. intros A B f x y eq. rewrite eq.  reflexivity.  Qed. 

(** Aqui hay otro ejemplo de [inversion].  Este ejemplo es una
    modificacion de lo que probamos arriba.  Las igualdades extras nos
    forzan a hacer un poco de razonamiento ecuacional y ejercitar las
    tacticas que vimos recientemente. *)

Theorem length_snoc' : forall (X : Type) (v : X)
                              (l : list X) (n : nat),
     length l = n ->
     length (snoc l v) = S n. 
Proof.
  intros X v l. induction l as [| v' l'].
  Case "l = []". intros n eq. rewrite <- eq. reflexivity.
  Case "l = v' :: l'". intros n eq. simpl. destruct n as [| n'].
    SCase "n = 0". inversion eq.
    SCase "n = S n'".
      apply f_equal. apply IHl'. inversion eq. reflexivity. Qed.


(** **** Ejercicio: 2 stars, opcional (practice) *)
(** Un par de ejemplos no triviales pero tampoco tan complicados para
    ejercitar estos conceptos.  Pueden requerir lemas ya provados
    anteriormente.  *)
 

Theorem beq_nat_0_l : forall n,
   beq_nat 0 n = true -> n = 0.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem beq_nat_0_r : forall n,
   beq_nat n 0 = true -> n = 0.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)


(* ###################################################### *)
(** * Usando Tacticas en las Hipotesis *)

(** Por defecto, la mayoria de las tacticas funcionan en el objetivo y
    dejan el contexto sin cambiar.  Sin embargo, la mayoria de las
    tacticas tambien tienen una variante que realiza una operacion
    similar en una premisa del contexto. 

    Por ejemplo, la tactica [simpl in H] realiza una simplificaion en
    la hipotesis llamada [H] en el contexto. *)

Theorem S_inj : forall (n m : nat) (b : bool),
     beq_nat (S n) (S m) = b  ->
     beq_nat n m = b. 
Proof.
  intros n m b H. simpl in H. apply H.  Qed.

(** De forma similar, la tactica [apply L in H] matchea algun lema o
    hipotesis condicional [L] (de la forma [L1 -> L2], digamos) contra
    una hipotesis [H] en el contexto.  Sin embargo, a diferencia del
    [apply] ordinario (que reescribe el objetivo matcheando [L2] en el
    sub-objetivo [L1]), [apply L in H] matchea [H] contra [L1] y, si
    es exitoso, lo reemplaza con [L2].
 
    En otras palabras, [apply L in H] nos da una forma de
    "razonamiento hacia adelante" -- de [L1 -> L2] y una hipotesis
    matcheando [L1], nos da una hipotesis matcheando [L2].  En
    contraste, [apply L] es "razonamiento hacia atras" -- dice que si
    sabemos [L1->L2] y queremos probar [L2], es suficiente con probar
    [L1].

    Aqui hay una variante de una prueba de arriba, usando razonamiento
    hacia adelante en toda la prueba, en vez de hacia atras. *)

Theorem silly3' : forall (n : nat),
  (beq_nat n 5 = true -> beq_nat (S (S n)) 7 = true) ->
     true = beq_nat n 5  ->
     true = beq_nat (S (S n)) 7.
Proof.
  intros n eq H.
  symmetry in H. apply eq in H. symmetry in H. 
  apply H.  Qed.

(** El razonamiento hacia adelante empieza desde lo que esta _dado_
    (las premisas, teoremas provados anteriormente), e iterativamente
    obtiene conclusiones desde ellos hasta que el objetivo es
    encontrado.  El razonamiento hacia atras empieza desde el
    _objetivo_, e iterativamente razona acerca que puede implicar el
    objetivo, hasta llegar a las premisas o teoremas existentes.  Si
    usted ha visto pruebas informales antes (por ejemplo, en
    matematica o en una clase de ciencias de la computacion),
    probablemente hayan utilizado razonamiento hacia adelante.  En
    general, Coq tiende a favorecer razonamiento hacia atras, pero en
    algunas situaciones el estilo de razonamiento hacia adelante puede
    ser mas facil de usar o de pensar.  *)

(** **** Ejercicio: 3 stars (plus_n_n_injective) *)
(** Practique utilizando variantes de "in" en este ejercicio. *)

Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  intros n. induction n as [| n'].
    (* Ayuda: utilice el lema plus_n_Sm *)
    (* FILL IN HERE *) Admitted.
(** [] *)

(* ###################################################### *)
(** * Variando la Hipotesis Inductiva *)

(** A veces es importante controlar la forma exacta de la hipotesis
    inductiva.  En particular, necesitamos ser cuidadosos acerca de
    que premisas movemos del objetivo al contexto (usando [intros])
    antes de invocar la tactica [induction]. Por ejemplo, suponga que
    queremos mostrar que la funcion [double] es inyectiva -- es decir,
    que siempre mapea diferentes argumentos a diferentes resultados:

    Theorem double_injective: forall n m, double n = double m -> n = m.

    La forma que _empezamos_ esta demostracion es un poco delicada: si
    comenzamos con [intros n. induction n.] todo va bien.  Pero si
    comenzamos con [intros n m. induction n.] nos quedamos estancados
    en el medio del caso inductivo...  *)

Theorem double_injective_FAILED : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m. induction n as [| n'].
  Case "n = O". simpl. intros eq. destruct m as [| m'].
    SCase "m = O". reflexivity.
    SCase "m = S m'". inversion eq. 
  Case "n = S n'". intros eq. destruct m as [| m'].
    SCase "m = O". inversion eq.
    SCase "m = S m'".  apply f_equal. 
      (* Aqui estamos estancados.  La hipotesis inductiva, [IHn'], nos
         da [n' = m'] -- hay un extra [S] en el camino -- asi que este
         objetivo no es demostrable. *) 
Abort.

(** Que salio mal? *)

(** El problema es que, en el punto en que invocamos la hipotesis
    inductiva, ya hemos introducido [m] en el contexto --
    intuitivamente le dijimos a Coq "Consideremos unos [n] y [m]
    particulares..." y ahora vamos a demostrar que, si [double n =
    double m] para _este [n] y [m] en particular_, entonces [n = m].

    La siguiente tactica, [induction n], le dice a Coq: Ahora vamos a
    mostrar el objetivo por induccion en [n].  Es decir, vamos a
    provar que la proposicion

      - [P n]  =  "si [double n = double m], entonces [n = m]"

    vale para todo [n] mostrando

      - [P O]              

         (es decir, "si [double O = double m] entonces [O = m]")

      - [P n -> P (S n)]  

        (es decir, "si [double n = double m] entonces [n = m]" implica "si
        [double (S n) = double m] entonces [S n = m]").

    Si miramos en detalle al segundo objetivo, esta diciendo algo un
    poco extranio: dice que, para un [m] _en particular_, si sabemos

      - "si [double n = double m] entonces [n = m]"

    podemos probar

       - "si [double (S n) = double m] entonces [S n = m]".

    Para ver porque esto es extranio, pensemos en un [m] particular --
    digamos, [5].  Este objetivo dice que, si sabemos

      - [Q] = "si [double n = 10] entonces [n = 5]"

    entonces podemos probar

      - [R] = "si [double (S n) = 10] entonces [S n = 5]".

    Pero sabiendo [Q] no nos ayuda a probar [R]!  (Si intentaramos
    probar [R] a partir de [Q], deberiamos decir algo como "Suponga
    [double (S n) = 10]..." pero entonces nos quedamos estancados:
    sabiendo que [double (S n)] is [10] no nos dice nada acerca de que
    [double n] es [10], asi que [Q] es inutil.) *)

(** Para sumarizar: Intentar hacer esta prueba por induccion en [n]
    cuando [m] esta en el contexto no funciona porque estamos tratando
    de probar una relacion involucrando _todo_ [n] pero solo un
    _unico_ [m].  *)

(** La prueba adecuada de [double_injective] deja [m] en el objetivo
    antes de invocar [induction] en [n]: *)

Theorem double_injective : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n. induction n as [| n'].
  Case "n = O". simpl. intros m eq. destruct m as [| m'].
    SCase "m = O". reflexivity.
    SCase "m = S m'". inversion eq. 
  Case "n = S n'". 
    (* Note que ahora el objetivo y la hipotesis inductiva cambiaron:
       el objetivo pide demostrar algo mas general (es decir, probar
       la propiedad para _todo_ [m]), pero la hipotesis inductiva es
       correspondientemente mas flexible, permitiendonos elegir
       cualquier [m] que queramos cuando la apliquemos.   *)
    intros m eq.
    (* Ahora elegimos al [m] en particular e introducimos la premisa
       que [double n = double m].  Como estamos haciendo analisis por
       caso en [n], tenemos que hacer analisis por caso en [m] para
       mantener las dos "sincronizadas". *)

    destruct m as [| m'].
    SCase "m = O". 
      (* El caso 0 es trivial *)
      inversion eq.  
    SCase "m = S m'".  
      apply f_equal. 
      (* En este punto, como estamos en la segunda rama de [destruct
         m], la variable [m'] mencionada en el contexto en este punto
         es de hecho el predecesor de la que veniamos hablando.  Y
         como ademas estamos la rama [S] de la induccion, esto es
         perfecto: si instanciamos la [m] generica de la hipotesis
         inductiva con el [m'] que estamos mencionando ahora
         (instanciacion hecha automaticamente por [apply]), entonces
         [IHn'] nos da exactamente lo que necesitamos para terminar la
         prueba.  *)
      apply IHn'. inversion eq. reflexivity. Qed.

(** Lo que esto nos ensenia es que tenemos que ser cuidadosos cuando
    usamos induccion para evitar caer en un caso muy especifico: Si
    estamos provando una propiedad en [n] y [m] por induccion en [n],
    tal vez sea una buena idea idea dejar [m] generica.  *)

(** La demostracion de este teorema tiene que ser tratada similarmente: *)

(** **** Ejercicio: 2 stars (beq_nat_true) *)
Theorem beq_nat_true : forall n m,
    beq_nat n m = true -> n = m.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Ejercicio: 2 stars, avanzado (beq_nat_true_informal) *)
(** De una prueba informal de [beq_nat_true], siendo tan explicita
    como se pueda acerca de los cuantificadores. *)

(* FILL IN HERE *)
(** [] *)


(** La estrategia de hacer menos [intros] antes de una [induction] no
    funciona siempre; a veces se necesita hacer un pequenia
    _reorganizacion_ de las variabes cuantificadas.  Suponga, por
    ejemplo, que quisieramos demostrar [double_injective] por
    induccion en [m] en vez de [n]. *)

Theorem double_injective_take2_FAILED : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m. induction m as [| m'].
  Case "m = O". simpl. intros eq. destruct n as [| n'].
    SCase "n = O". reflexivity.
    SCase "n = S n'". inversion eq. 
  Case "m = S m'". intros eq. destruct n as [| n'].
    SCase "n = O". inversion eq.
    SCase "n = S n'".  apply f_equal.
        (* Estancados aca de nuevo, igual que antes. *)
Abort.

(** El problema es que, para acer induccion en [m], queremos pimero
    introducir [n].  (Si simplemente decimos [induction m] sin
    introducir nada antes, Coq va a introducir automaticamente [n] por
    nosotros!)  *)

(** Que podemos hacer con esto?  Una posibilidad es reescribir el lema
    de forma que [m] sea cuantificada antes que [n].  Esto funciona,
    pero no es elegante: No queremos adaptar los lemas para satisfacer
    las necesidades de la estrategia de la prueba -- queremos
    especificarlo en la forma mas natural y comprensible. *)

(** Lo que podemos hacer, en vez, es introducir todas las variables
    cuantificadas y luego _re-generalizar_ ona o mas variables,
    tomandolas del contexto y poniendolas de vuelta en el objetivo.
    La tactica [generalize dependent] hace esto. *)

Theorem double_injective_take2 : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m. 
  (* [n] y [m] estan las dos en el contexto *)
  generalize dependent n.
  (* Ahora [n] esta devuelta en el objetivo, y ahora podemos hacer
     induccion en [m] y obtener una HI suficientemente general. *)
  induction m as [| m'].
  Case "m = O". simpl. intros n eq. destruct n as [| n'].
    SCase "n = O". reflexivity.
    SCase "n = S n'". inversion eq.
  Case "m = S m'". intros n eq. destruct n as [| n'].
    SCase "n = O". inversion eq.
    SCase "n = S n'". apply f_equal.
      apply IHm'. inversion eq. reflexivity. Qed.

(** Miremos a una prueba informal de este teorema.  Note que la
    proposicion que provamos por induccion deja [n] cuantificado,
    correspondiendo al uso de [generalize dependent] en la prueba
    formal.

_Teorema_: Para todos naturales [n] y [m], si [double n = double m],
  entonces [n = m].

_Demostracion_: Sea [m] un [nat]. Provamos por induccion en [m] que,
  para cualquier [n], si [double n = double m] entonces [n = m].

  - Primero suponga [m = 0], y suponga que [n] es un numero
    tal que [double n = double m].  Debemos mostrar que [n = 0].

    Como [m = 0], por definicion de [double] tenemos [double n = 0].
    Tenemos que considerar dos casos para [n].  Si [n = 0] entonces ya
    esta, puesto que esto es lo que queriamos probar.  En otro caso,
    si [n = S n'] para algun [n'], derivamos una contradiccion: por la
    definicion de [double] obtenemos que [double n = S (S (double
    n'))], pero esto contradice la premisa de que [double n = 0].

  - En otro caso, suponga [m = S m'] y que [n] es, de vuelta, un
    number tal que [double n = double m].  Debemos mostrar que [n = S
    m'], con la hipotesis inductiva que para cualquier numero [s], si
    [double s = double m'] entonces [s = m'].
 
    Dado que [m = S m'] y la definicion de [double], tenemos que
    [double n = S (S (double m'))].  Hay dos casos que considerar para
    [n].

    Si [n = 0], entonces por definicion [double n = 0], una
    contradiccion.  Entonces, tenemos que asumir que [n = S n'] para
    algun [n'], y de vuelta por definicion de [double] tenemos [S (S
    (double n')) = S (S (double m'))], que por inversion implica
    [double n' = double m'].

    Instanciando la hipotesis inductiva con [n'] entonces nos permite
    concluir que [n' = m'], y en consecuencia, [S n' = S m'].  Como [S
    n' = n] y [S m' = m], esto es justo lo que queriamos probar. [] *)

(** **** Ejercicio: 3 stars (gen_dep_practice) *)

(** Demuestre por induccion en [l]. *)

Theorem index_after_last: forall (n : nat) (X : Type) (l : list X),
     length l = n ->
     index n l = None.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Ejercicio: 3 stars, avanzado, opcional (index_after_last_informal) *)
(** Escriba una prueba informal correspondiendo a su prueba de Coq de
    [index_after_last]:
 
     _Teorema_: Para todo conjunto [X], listas [l : list X], y numero
      [n], si [length l = n] entonces [index n l = None].
 
     _Demostracion_:
     (* FILL IN HERE *)
[]
*)

(** **** Ejercicio: 3 stars, opcional (gen_dep_practice_more) *)
(** Demuestre lo siguiente por induccion en [l]. *)

Theorem length_snoc''' : forall (n : nat) (X : Type) 
                              (v : X) (l : list X),
     length l = n ->
     length (snoc l v) = S n. 
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Ejercicio: 3 stars, opcional (app_length_cons) *)
(** Demuestre esto por induccion en [l1], sin utilizar [app_length]. *)

Theorem app_length_cons : forall (X : Type) (l1 l2 : list X) 
                                  (x : X) (n : nat),
     length (l1 ++ (x :: l2)) = n ->
     S (length (l1 ++ l2)) = n.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Ejercicio: 4 stars, opcional (app_length_twice) *)
(** Demuestre esto por induccion en [l], sin utilizar [app_length]. *)

Theorem app_length_twice : forall (X:Type) (n:nat) (l:list X),
     length l = n ->
     length (l ++ l) = n + n.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ###################################################### *)
(** * Usando [destruct] en Expresiones Compuestas *)

(** Vimos muchos ejemplos donde la tactica [destruct] es utilizada
    para realizar analisis por caso en el valor de una variable.  Pero
    a veces necesitamos razonar por casos en el resultado de alguna
    _expresion_.  Tambien podemos hacer esto con [destruct].

    Aqui hay unos ejemplos: *)

Definition sillyfun (n : nat) : bool :=
  if beq_nat n 3 then false
  else if beq_nat n 5 then false
  else false.

Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  intros n. unfold sillyfun. 
  destruct (beq_nat n 3).
    Case "beq_nat n 3 = true". reflexivity.
    Case "beq_nat n 3 = false". destruct (beq_nat n 5).
      SCase "beq_nat n 5 = true". reflexivity.
      SCase "beq_nat n 5 = false". reflexivity.  Qed.

(** Luego de expandir (unfold) [sillyfun] en la definicion de arriba,
    nos encontramos con que estamos varados en [if (beq_nat n 3) then
    ... else ...].  Bueno, o [n] es igual a [3] o no lo es, asi que
    [destruct (beq_nat n 3)] nos permite razonar acerca de los dos
    casos.

    En general, la tactica [destruct] puede ser utilizada para
    realizar analisis por caso en los resultados de computaciones
    arbitrarias.  Si [e] es una expresion cuyo tipo es algun tipo
    definido inductivamente [T], entonces, para cada constructor [c]
    de [T], [destruct e] genera un sub-objetivo en el cual todas las
    ocurrencias de [e] (en el objetivo y en el contexto) son
    reemplazadas por [c].

*)

(** **** Ejercicio: 1 star (override_shadow) *)
Theorem override_shadow : forall (X:Type) x1 x2 k1 k2 (f : nat->X),
  (override (override f k1 x2) k1 x1) k2 = (override f k1 x1) k2.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Ejercicio: 3 stars, opcional (combine_split) *)
(** Complete la demostracion de abajo *)

Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** A veces, haciendo un [destruct] en una expresion compuesta (una
    no-variable) puede borrar informacion que necesitamos para
    concluir la prueba. *)
(** Por ejemplo, suponga que definimos la funcion [sillyfun1] de la
    siguiente forma: *)

Definition sillyfun1 (n : nat) : bool :=
  if beq_nat n 3 then true
  else if beq_nat n 5 then true
  else false.

(** Y suponga que queremos convencer a Coq de la observacion bastante
     obvia que [sillyfun1 n] retorna [true] solo cuando [n] es impar.
     En analogia con las demostraciones que hicimos con [sillyfun] de
     arriba, es natural pensar la prueba de la siguiente manera: *)

Theorem sillyfun1_odd_FAILED : forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (beq_nat n 3).
  (* stuck... *)
Abort.

(** Nos quedamos estancados en este punto porque el contexto no
    contiene suficiente informacion para probar el objetivo!  El
    problema es que la sustitucion realizada por [destruct] es
    demasiado brutal -- tira todas las ocurrencias de [beq_nat n 3],
    pero a veces es necesario quedarnos con algun recuerdo de esta
    expresion y como ha sido destruida, porque debemos ser capaces de
    razonar que, en esta rama del analisis por caso, [beq_nat n 3 =
    true], y ergo debe ser que [n = 3], de lo cual concluimos que [n]
    es impar.

    Lo que realmente quisieramos es sustituir todas las ocurrencias de
    [beq_nat n 3], pero a la vez quedarnos con una ecuacion en el
    contexto que indique en que caso estamos.  el modificador [_eqn:]
    (o simplemente [eqn:] en Coq 8.4) nos permite obtener esta
    ecuacion (con el nombre que querramos ponerle). *)

Theorem sillyfun1_odd : forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (beq_nat n 3) as [] _eqn:Heqe3.
  (* Ahora estamos en el mismo punto en el que estabamos cuando nos
    quedamos estancados arriba, excepto que ahora tenemos lo que
    necesitamos para poder progresar en la demostracion.  *)
    Case "e3 = true". apply beq_nat_true in Heqe3.
      rewrite -> Heqe3. reflexivity.
    Case "e3 = false".
     (* Cuando llegamos al segundo test de igualdad, podemos utilizar
       [_eqn:] de vuelta para poder concluir la prueba. *)
      destruct (beq_nat n 5) as [] _eqn:Heqe5. 
        SCase "e5 = true".
          apply beq_nat_true in Heqe5.
          rewrite -> Heqe5. reflexivity.
        SCase "e5 = false". inversion eq.  Qed.


(** **** Ejercicio: 2 stars (destruct_eqn_practice) *)
Theorem bool_fn_applied_thrice : 
  forall (f : bool -> bool) (b : bool), 
  f (f (f b)) = f b.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Ejercicio: 2 stars (override_same) *)
Theorem override_same : forall (X:Type) x1 k1 k2 (f : nat->X),
  f k1 = x1 -> 
  (override f k1 x1) k2 = f k2.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################## *)
(** * Resumen *)

(** Ahora hemos visto una serie de tacticas fundamentales en Coq.
    Vamos a introducir algunas mas a medida que avanzemos en los
    capitulos, y mas adelante veremos algunas tacticas poderosas para
    _automatizar_ mucho del trabajo.  Pero basicamente tenemos todo lo
    necesario para poder trabajar.

    Aqui estan las que hemos vistos:

      - [intros]: 
        mueve las hipotesis/variables desde el objetivo al contexto. 

      - [reflexivity]:
        concluye la demostracion cuando el objetivo es de la forma [e = e].

      - [apply]:
        demuestra el objetivo utilizando una hipotesis, lema, o constructor.

      - [apply... in H]: 
        aplica una hipotesis, lema, o constructor a otra hipotesis en el
        contexto (razonamiento hacia adelante).

      - [apply... with...]:
        explicita los valores especificos para las variables que no pueden
        ser determinadas por simple matcheo.

      - [simpl]:
        simplifica (reduce cuidadosamente) las computaciones en el objetivo...

      - [simpl in H]:
        ... on en una hipotesis.

      - [rewrite]:
        utiliza una premisa (o lema) de igualdad para reescribir el objetivo...

      - [rewrite ... in H]:
        ... o una hipotesis.

      - [symmetry]:
        cambia un objetivo de la forma [t=u] en [u=t].

      - [symmetry in H]:
        cambia una hipotesis de la forma [t=u] en [u=t]

      - [unfold]:
        reemplaza la definicion de una constante en el objetivo...

      - [unfold... in H]:
        ... o en una hipotesis  

      - [destruct... as...]:
        analiza por casos los valores de tipos definidos inductivamente.

      - [destruct... _eqn:...]:
        especifica el nombre de la ecuacion a ser agregada en el contexto,
        guardando el resultado del analisis por caso.

      - [induction... as...]:
        induccion en variables de un tipo inductivo. 

      - [inversion]:
        razonamiento por inyectividad y distincion de constructores.

      - [assert (e) as H]:
        introduce un "lema local" [e] y lo llama [H].

      - [generalize dependent x]:
        mueve la variable [x] (y todo lo que dependa de ella)
        desde el contexto hacia el objetivo.
*)

(* ###################################################### *)
(** * Ejercicios Adicionales *)

(** **** Ejercicio: 3 stars (beq_nat_sym) *)
Theorem beq_nat_sym : forall (n m : nat),
  beq_nat n m = beq_nat m n.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Ejercicio: 3 stars, avanzado, opcional (beq_nat_sym_informal) *)
(** De una prueba informal a este lema que corresponda con la
    demostracion formal suya de arriba:

   Teorema: Para todos [nat]s [n] [m], [beq_nat n m = beq_nat m n].

   Demostracion:
   (* FILL IN HERE *)
[]
 *)

(** **** Ejercicio: 3 stars, opcional (beq_nat_trans) *)
Theorem beq_nat_trans : forall n m p,
  beq_nat n m = true ->
  beq_nat m p = true ->
  beq_nat n p = true.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Ejercicio: 3 stars, avanzado (split_combine) *)
(** Hemos demostrado que para todas las listas de pares, [combine] es
    el inverso de [split].  Como formalizaria el hecho de que
    [split] es el inverso de [combine]?

    Complete la definicion de [split_combine_statement] de abajo con
     una propiedad que estalece que [split] es el inverso de
     [combine]. Luego, pruebe que esta propiedad vale.  (Asegurese de
     dejar su hipotesis inductiva general evitando introducir mas
     cosas que las necesarias.  Ayuda: que propiedad necesita de
     [l1] y [l2] para [split] que haga cierto [combine l1 l2 = (l1,l2)]?)
     *)

Definition split_combine_statement : Prop :=
(* FILL IN HERE *) admit.

Theorem split_combine : split_combine_statement.
Proof.
(* FILL IN HERE *) Admitted.


(** [] *)

(** **** Ejercicio: 3 stars (override_permute) *)
Theorem override_permute : forall (X:Type) x1 x2 k1 k2 k3 (f : nat->X),
  beq_nat k2 k1 = false ->
  (override (override f k2 x2) k1 x1) k3 = (override (override f k1 x1) k2 x2) k3.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Ejercicio: 3 stars, avanzado (filter_exercise) *)
(** Este es un poco dificil.  Preste atencion a la forma de su HI. *)

Theorem filter_exercise : forall (X : Type) (test : X -> bool)
                             (x : X) (l lf : list X),
     filter test l = x :: lf ->
     test x = true.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Ejercicio: 4 stars, avanzado (forall_exists_challenge) *)
(** Defina dos [Fixpoints], [forallb] y [existsb].  El primero
    verifica que todo elemento de una lista dada satisfaga una
    predicado dado:
      forallb oddb [1;3;5;7;9] = true

      forallb negb [false;false] = true
  
      forallb evenb [0;2;4;5] = false
  
      forallb (beq_nat 5) [] = true

    El segundo verifica que existe al menos un elmento de la lista que
    satisfaga el predicado dado:

      existsb (beq_nat 5) [0;2;3;6] = false
 
      existsb (andb true) [true;true;false] = true
 
      existsb oddb [1;0;0;0;0;3] = true
 
      existsb evenb [] = false

    A continuacion, defina una version _no recursiva_ de [existsb] --
    llamela [existsb'] -- usando [forallb] y [negb].
 
    Demuestre que [existsb'] y [existsb] tienen el mismo
    comportamiento.  *)

(* FILL IN HERE *)
(** [] *)

(* $Date: 2013-07-17 16:19:11 -0400 (Wed, 17 Jul 2013) $ *)



