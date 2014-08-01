(** * Induction: Demostracion por Induccion *)
 

(** La siguiente linea importa todas nuestras definiciones del
    capitulo anterior. *)

Require Export Basics.

(** Para que funcione, necesita usar [coqc] para compilar [Basics.v]
    en [Basics.vo] (Esto es como hacer un archivo .class de un archivo
    .java, o un archivo .o de un .c).
  
    Aqui presentamos dos formas de compilar el codigo:
  
     - CoqIDE:
   
         Abrir [Basics.v].
         En el menu "Compile", click en "Compile Buffer".
   
     - Linea de comandos:
   
         Ejecute [coqc Basics.v]

    *)

(* ###################################################################### *)
(** * Nombrando Casos *)

(** El hecho de que no hay un comando explicito para moverse de una
    rama de un analisis por caso al siguiente puede hacer los scripts
    de prueba dificiles de leer.  En pruebas grandes, con casos
    anidados, uno se puede desorientar facilmente cuando se esta
    frente a Coq llendo paso a paso en una prueba.  (Imaginese
    tratando de acordarse que los primeros cinco sub-casos pertenecen
    a la primer rama del analisis por caso principal, y los siete
    siguientes pertenencen al segundo...)  Un uso disciplinado de
    identacion y comentarios puede ayudar, pero una forma mejor es
    usar la tactica [Case]. *)

(* [Case] no viene por default in Coq: tenemos que definirla nosotros
    mismos.  No hay necesidad de entender como funciona -- puede
    simplemente saltear la definicion e ir derecho al ejemplo que
    sigue.  Usa ciertas herramientas de Coq que todavia no hemos
    discutido -- la libreria de strings y el comando [Ltac], que nos
    permite declarar tacticas propias.  Kudos a Aaron Bohannon por
    este lindo hack! *)

Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.

(** Aqui hay un ejemplo de como [Case] se usa.  Vaya paso a paso en la
   prueba y observe como el contexto cambia. *)

Theorem andb_true_elim1 : forall b c : bool,
  andb b c = true -> b = true.
Proof.
  intros b c H.
  destruct b.
  Case "b = true".  (* <----- aqui *)
    reflexivity.
  Case "b = false".  (* <---- y aqui *)
    rewrite <- H. 
    reflexivity.  
Qed.

(** [Case] hace algo muy simple: Simplemente agrega el string que le
    pasemos ("tageado" con el identificador "Case") al contexto del
    objetivo actual.  Cuando se generan sub-objetivos, este string es
    copiado en sus contextos.  Cuando el ultimo de los sub-objetivos
    es finalmente demostrado y el siguiente ojetivo de nivel superior
    se activa, este string no va a aparecer mas en el contexto, y
    podremos determinar que hemos terminado con el caso.  Tambien,
    como "sanity check" (checkeo de sanidad?), si intentamos ejecutar
    un nuevo [Case] mientras estamos resolviendo uno, vamos a obtener
    un mensaje claro de error.

    Para casos anidados (e.g., para cuando utilizamos [destruct] en el
    caso creado por otro [destruct]), hay una tactica [SCase] (por
    "sub-caso"). *)

(** **** Ejercicio: 2 stars (andb_true_elim2) *)
(** Demuestre [andb_true_elim2], marcando casos (y sub-casos) cuando
    utilice [destruct]. *)

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** No hay reglas estrictas y definidas de como una demostracion puede
    ser estructurada en Coq -- en particular, donde se deben quebrar
    las lineas y como las distintas secciones de una demostracion
    deben ser identadas.  Sin embargo, si se marca explicitamente con
    [Case] los lugares donde los sub-casos son generados, entonces la
    demostracion puede ser legible independientemente de otros aspectos en
    el formateo de la misma.

    Este es un buen lugar para mencionar otro "tip" (posiblemente
    obvio) acerca del ancho de las lineas.  En general, los usuarios
    principiantes de Coq tienden a ser extremistas, escribiendo o una
    tactica por linea, o pruebas enteras en una linea.  El buen
    estilo se encuentra un poco en el medio.  En particular, una
    convencion razonable es limitarse a los 80 caracteres por linea.
    Lineas mas largas que esto pueden ser dificiles de leer y pueden
    ser dificiles de imprimir.  Muchos editores tienen facilidades
    para enforzar este limite. *)

(* ###################################################################### *)
(** * Pruebas por Induccion *)

(** Hemos provado en el capitulo anterior que [0] es un elemento
    neutral para [+] a la izquierda usando un argumento simple.  El
    hecho de que tambien es neutral a la _derecha_... *)

Theorem plus_0_r_firsttry : forall n:nat,
  n + 0 = n.

(** ... no puede ser provado en la misma forma.  Aplicando simplemente
  [reflexivity] no funciona: el [n] en [n + 0] es un numero
  desconocido arbitrario, con lo que el [match] en la definicion de
  [+] no puede ser simplificado.  *)

Proof.
  intros n.
  simpl. (* No hace nada! *)
Abort.

(** Razonando por casos usando [destruct n] no nos lleva muy lejos: el
   caso [n = 0] funciona, pero en el caso [n = S n'] para algun [n']
   nos quedamos bloqueados de la misma forma.  Podemos usar [destruct
   n'] para ir un paso mas alla, pero [n] puede ser arbitrariamente
   grande, con lo que si seguimos de esta forma nunca vamos a
   terminar. *)

Theorem plus_0_r_secondtry : forall n:nat,
  n + 0 = n.
Proof.
  intros n. destruct n as [| n'].
  Case "n = 0".
    reflexivity. (* todo bien hasta aca... *)
  Case "n = S n'".
    simpl.       (* ...pero aca estamos bloqueados como antes. *)
Abort.

(** Para demostrar este tipo de teoremas -- de hecho, para demostrar
    casi cualquier teorema sobre numeros, listas, y cualquier otro
    tipo de datos definido inductivamente -- necesitamos un
    razonamiento mas elaborado: _induccion_.

    Recuerden el principio de induccion sobre numeros naturales: Si
    [P(n)] es una proposicion involucrando un numero natural [n] y
    queremos ver que P es cierto para _todo_ numero [n], podemos
    razonar de la siguiente forma: 
    - mostrar que [P(O)] vale; 
    - mostrar que, para cualquier [n'], si [P(n')] vale, entonces vale
    [P(S n')]; 
    - concluir que [P(n)] vale para todo [n].

    En Coq, estos pasos son iguales, pero el orden es inverso:
    comenzamos con el obejtivo que queremos probar [P(n)] para todo
    [n] y lo dividimos (aplicando la tactica [induction]) en dos
    sub-objetivos: primero [P(O)] luego [P(n') -> P(S n')].  Asi es
    como funciona en el problema que estuvimos trabajando hasta ahora:
    *)

Theorem plus_0_r : forall n:nat, n + 0 = n.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0".     reflexivity.
  Case "n = S n'".  simpl. rewrite -> IHn'. reflexivity.  Qed.

(** Como [destruct], la tactica [induction] toma una clausula [as...]
    que especifica los nombres de las variables a ser introducidas en
    los sub-objetivos.  En la primer rama, [n] es reemplazado por [0]
    el objetivo es [0 + 0 = 0], que es cierto por simplificacion.  En el
    segundo, [n] es reemplazado por [S n'] y la hipotesis [n' + 0 =
    n'] es agregada al contexto (con el nombre [IHn'], es decir, la
    Hipotesis Inductiva para [n']).  El objetivo en este caso es [(S
    n') + 0 = S n'], que se puede simplificar a [S (n' + 0) = S n'],
    que a su cez se puede resolver usando la hipotesis inductiva. *)

Theorem minus_diag : forall n,
  minus n n = 0.
Proof.
  (* WORKED IN CLASS *)
  intros n. induction n as [| n'].
  Case "n = 0".
    simpl. reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. reflexivity.  Qed.

(** **** Ejercicio: 2 stars (basic_induction) *)

(** Pruebe los siguientes teoremas usando induccion.  Tal ver requiera
    utilizar algun resultado previo. *)

Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem plus_n_Sm : forall n m : nat, 
  S (n + m) = n + (S m).
Proof. 
  (* FILL IN HERE *) Admitted.


Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  (* FILL IN HERE *) Admitted.


Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Ejercicio: 2 stars (double_plus) *)

(** Considere la siguiente funcion, que duplica el argumento: *)

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

(** Use induccion para probar este simple lema sobre [double]: *)

Lemma double_plus : forall n, double n = n + n .
Proof.  
  (* FILL IN HERE *) Admitted.
(** [] *)


(** **** Ejercicio: 1 star (destruct_induction) *)
(** Explique brevemente la diferencia entre las tacticas
    [destruct] e [induction].  

(* FILL IN HERE *)

*)
(** [] *)


(* ###################################################################### *)
(** * Pruebas dentro de Pruebas *)


(** En Coq, al igual que en los razonamientos matematicos informales,
    las demostraciones largas son usualmente divididas en una
    secuencia de teoremas, con las demostraciones del final utilizando
    los teoremas demostrados anteriormente.  Ocasionalmente, sin
    embargo, una demostracion puede necesitar algun hecho (fact) que
    es trivial y de poco interes general para molestarse en darle un
    nombre propio.  En tales casos, es conveniente poder establecer y
    demostrar localmente un "sub-teorema" en el punto en que debe ser
    utilizado.  La tactica [assert] nos permite hacer esto.  Por
    ejemplo, en nuestra demostracion del teorema [mult_0_plus] nos
    referimos a otro teorema [plus_O_n].  Podemos utilizar [assert]
    para establecer [plus_O_n] "in-line": *)

Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n). 
    Case "Proof of assertion". reflexivity.
  rewrite -> H.
  reflexivity.  Qed.

(** La tactica [assert] introduce dos sub-objetivos.  El primero es la
    asercion en si misma; al prefijarla con [H:], le hemos dado como
    nombre [H].  (Note que tambien podemos utilizar [as] como hicimos
    con [destruct] e [induction], i.e., [assert (0 + n = n) as H].
    Tambien note que hemos marcado la prueba de esta asercion con un
    [Case], para mejorar la legibilidad de la prueba y para, mientras
    usamos Coq interactivamente, saber que hemos concluido la prueba
    de la asercion observando que el string ["Proof of assertion"]
    desaparece del contexto.)  El segundo objetivo es el mismo que el
    que teniamos antes de invocar [assert], excepto que ahora tiene
    una hipotesis llamada [H] que establece [0 + n = n].  Es decir,
    [assert] genera un sub-objetivo para demostrar la asercion, y un
    segundo sub-objetivo donde la asercion esta a nuestra mano para
    utilizar y hacer progreso en la prueba principal. *)

(** Actualmente, [assert] nos va a ser util en muchos tipos de
    situaciones.  Por ejemplo, suponga que queremos probar que [(n +
    m) + (p + q) = (m + n) + (p + q)].  La unica diferencia entre los
    dos lados del igual es que los argumentos [m] y [n] en el primer
    [+] estan intercambiados, con lo que pareceria que podemos
    utilizar la comutatividad de la suma ([plus_comm]) para reescribir
    uno en otro.  Sin embargo, la tactica [rewrite] es un poco
    estupida respecto de _donde_ aplicar la reescritura.  Hay tres usos
    de [+] aqui, y resulta que si hacemos [rewrite -> plus_comm] vamos
    a afectar el de mas _afuera_. *)

Theorem plus_rearrange_firsttry : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  (* Necesitamos intercambiar (n + m) por (m + n)...
     pareceria que plus_comm debiera funcionar! *)
  rewrite -> plus_comm.
  (* No funciona... Coq reescribio la suma incorrecta! *)
Abort.

(** Para poder aplicar [plus_comm] en el lugar que queremos, podemos
    introducir un lema local estableciendo [n + m = m + n] (para los
    [m] y [n] particulares que utilizamos en la demostracion), demostrar
    este lema utilizando [plus_comm], y usar luego este lema para reescribir
    el lugar correcto. *)

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
    Case "Proof of assertion".
    rewrite -> plus_comm. reflexivity.
  rewrite -> H. reflexivity.  Qed.

(** **** Ejercicio: 4 stars (mult_comm) *)
(** Utilice [assert] para ayudar probar este teorema.  No deberia
    necesitar [induction]. *)

Theorem plus_swap : forall n m p : nat, 
  n + (m + p) = m + (n + p).
Proof.
  (* FILL IN HERE *) Admitted.


(** Ahora demuestre la conmutatividad de la multiplicacion.  (Va a
    necesitar posiblemente demostrar un teorema subsidiario para
    usarlo en este.)  Puede encontrar util [plus_swap]. *)

Theorem mult_comm : forall m n : nat,
 m * n = n * m.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Ejercicio: 2 stars, opcional (evenb_n__oddb_Sn) *)

(** Pruebe el siguiente teorema sencillo: *)

Theorem evenb_n__oddb_Sn : forall n : nat,
  evenb n = negb (evenb (S n)).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ###################################################################### *)
(** * Mas ejercicios *)

(** **** Ejercicio: 3 stars, opcional (more_exercises) *)
(** Tome un pedazo de papel.  Por cada uno de los siguientes teoremas,
    primero _piense_ acerca de si (a) puede ser demostrado utilizando
    simplemente [rewrite], [simpl] y [reflexivity], o (b) tambien
    requiere analisis por caso ([destruct]), o (c) tambien requiere
    induccion.  Escriba su prediccion.  Entonces complete las
    demostraciones.  (No hay necesidad de entregar el papel, este
    ejercicio es para estimular el pensamiento antes de hackear!) *)

Theorem ble_nat_refl : forall n:nat,
  true = ble_nat n n.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem zero_nbeq_S : forall n:nat,
  beq_nat 0 (S n) = false.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem plus_ble_compat_l : forall n m p : nat, 
  ble_nat n m = true -> ble_nat (p + n) (p + m) = true.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem S_nbeq_0 : forall n:nat,
  beq_nat (S n) 0 = false.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem all3_spec : forall b c : bool,
    orb
      (andb b c)
      (orb (negb b)
               (negb c))
  = true.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  (* FILL IN HERE *) Admitted.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Ejercicio: 2 stars, opcional (beq_nat_refl) *)
(** Pruebe el siguiente teorema.  Poner [true] en el lado izquierdo de
    la igualdad puede verse raro, pero es asi como el teorema esta
    escrito en la libreria estandard de Coq, y nosotros copiamos en
    consecuencia.  Como se puede reescribir igualmente en cualquier
    direccion, no vamos a tener problemas usando el teorema, sin
    importar en que forma lo escribamos. *)

Theorem beq_nat_refl : forall n : nat, 
  true = beq_nat n n.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, optional (plus_swap') *)
(** La tactica [replace] permite especificar un subtermino particular
   a reescribir, y a que se debe reescribir.  Mas precisamente,
   [replace (t) with (u)] reemplaza (todas las copias de) la expresion
   [t] en el objetivo por la expresion [u], y genera [t = u] como
   sub-objetivo adicional. Esto es util cuando [rewrite] reescribe una
   parte incorrecta del objetivo.

   Utilice la tactica [replace] para demostrar [plus_swap'], similar a
   [plus_swap] pero sin necesitar [assert (n + m = m + n)].  *)

Theorem plus_swap' : forall n m p : nat, 
  n + (m + p) = m + (n + p).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)


(** **** Ejercicio: 3 stars (binary_commute) *)
(** Recuerde las funciones [increment] y [binary-to-unary] que
    escribio para el ejercicio [binary] en el capitulo [Basics].
    Pruebe que estas funciones conmutan -- es decir, que incrementar
    un numero binario y convertirlo a unitario es igual a convertirlo
    en unario primero y luego incrementarlo.

    (Antes de empezar a trabajar en este ejercicio, por favor copie
    sus definiciones del ejercicio [binary] aqui, para que este
    archivo pueda ser evaluado independientemente.  Si necesita
    modificar las definiciones para hacer la prueba mas facil,
    sientase libre de hacerlo). *)

(* FILL IN HERE *)
(** [] *)


(** **** Ejercicio: 5 stars, advanced (binary_inverse) *)
(** Este ejercicio es una continuacion del ejercicio anterior acerca
    numeros binarios.  Usted debe completar las definiciones y
    teoremas del ejercicio previo antes de hacer este ejercicio.

    (a) Primero, escriba una funcion para convertir numeros naturales a
        numeros binarios.  Luego, pruebe que convertir un numero
        natural a binario, y luego convertir a natural el resultado,
        resulta en el mismo numero.

    (b) Tal vez usted considere que tambien podemos probar lo
        contrario, es decir, que convertir un numero binario en natural
        y viceversa resulta en el mismo numero natural.  Sin embargo,
        no es asi!  Explique por que.

    (c) Defina una funcion [normalize] de numeros binarios a numeros
        binarios tal que para cada numero binario b, convertir b a
        numero natural y viceversa resulta en [(normalize b)].  Demuestrelo.

    Como antes, sientase en la libertad de cambiar las definiciones si
    asi lo desea.  *)

(* FILL IN HERE *)
(** [] *)

(* ###################################################################### *)
(** * Material Avanzado *)

(** ** Prueba Formal vs. Informal *)

(** "Pruebas informales son algoritmos; pruebas formales son codigo." *)

(** La pregunta de que exactamente constituye una "prueba" de un
    teorema matematico a intrigado a filosofos por milenios.  Una
    definicion burda y rapida puede ser: una prueba de una proposicion
    matematica [P] es un texto escrito (o dicho) que infunde en el
    lector (o receptor) la certeza de que [P] es verdad.  Es decir,
    una prueba es un acto de comunicacion.

    Ahora, la comunicacion en general puede incluir tipos diferentes
    de lectores.  En una mano, el "lector" puede ser un programa como
    Coq, en cuyo caso la "creencia" que es inculcada es un checkeo
    mecanico de que [P] puede ser derivado de un conjunto de reglas
    logicas, y la prueba es una receta que guia al programa para
    realizar este checkeo.  Estas recetas son pruebas _formales_.

    Alternativamente, el lector puede ser un ser humano, en cuyo caso
    la prueba puede ser escrita en espaniol o cualquier otro lenguaje
    natural, necesariamente _informal_.  Aqui, el criterio para el
    exito esta especificado de forma mas difusa.  Una "buena" prueba
    es una que convence al lector de que [P] vale.  Pero la misma
    prueba puede ser leida por muchos lectores diferentes, en los que
    algunos pueden convencerse de cierto argumento, mientras que otros
    pueden ponerlo en duda.  Un lector puede ser particularmente
    pedante, inexperto, o simplemente lento; la unica forma de
    convencerlo va a ser haciendo el argumento extremadamente
    puntillosamente.  Pero otro lector, conocedor del area, puede
    encontrar estos detalles tan apabullantes, que le hacen perder el
    argumento principal.  Lo unico que necesita es que le digan las
    ideas principales, porque es mas facil llenar los detalles por si
    mismo.  De ultima, no hay un estandard universal, porque no hay una
    sola forma de escribir una prueba informal de forma tal que
    convenza a todos los lectores.  En practica, sin embargo, los
    matematicos han desarrollado una serie de convenciones y modismos
    para escribir acerca de objetos matematicos complejos que, para
    cierta comunidad, hace la comunicacion decentemente fiable.  Las
    convenciones utilizadas en esta forma estilizadad de comunicacion
    da paso a estandardes claros para juzgar una prueba buena o mala.

    Como estamos usando Coq en este curso, vamos a trabajar
    fuertemente con pruebas formales.  Pero eso no significa que
    podemos ignorar las pruebas informales!  Las pruebas formales son
    utiles en muchos sentidos, pero no son muy eficientes como
    mechanismo para comunicar ideas entre humanos. *)

(** Por ejemplo, aqui hay un ejemplo de que la suma de los naturales
    es asociativa: *)

Theorem plus_assoc' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof. intros n m p. induction n as [| n']. reflexivity. 
  simpl. rewrite -> IHn'. reflexivity.  Qed.

(** Coq esta perfectamente feliz con esta prueba.  Para un humano, sin
    embargo, es dificil entender que esta pasando.  Si el lector esta
    acostumbrado a Coq, puede ir paso por paso en su cabeza,
    imaginando cual es el estado del contexto y el objetivo en cada
    paso, pero si la prueba fuera ligeramente mas complicada, esto
    seria completamente imposible.  En cambio, un matematico
    escribiria algo asi: *)

(** - _Teorema_: Para cada [n], [m] y [p],
      n + (m + p) = (n + m) + p.
    _Prueba_: Por induccion en [n].

    - Primero, suponga [n = 0].  Debemos mostrar 
        0 + (m + p) = (0 + m) + p.  
      Esto se desprende de la definicion de [+].

    - Siguiente, suponga [n = S n'], donde
        n' + (m + p) = (n' + m) + p.
      Debemos mostrar
        (S n') + (m + p) = ((S n') + m) + p.
      Por definicion de [+], esto es equivalente a
        S (n' + (m + p)) = S ((n' + m) + p),
      que es inmediato por la hipotesis inductiva. [] *)

(** El aspecto general de la prueba es basicamente similar.  Y esto no
    es pura casualidad: Coq ha sido diseniado de forma que la tactica
    [induction] genera los mismos sub-objetivos, en el mismo orden,
    que las vinietas que un matematico/a podria escribir.  Pero las
    pruebas difieren en los detalles: la prueba formal es mucho mas
    explicita en algunos aspectos (ej., el uso de [reflexivity]) pero
    mucho menos explicita en otros (en particular, el "estado de la
    prueba" en cada paso en la prueba en Coq es implicita, mientras
    que en la prueba informal se le recuerda al lector varias veces
    sobre el punto en el que se esta). *)

(** Aca hay una prueba formal con una estructura mas clara: *)

Theorem plus_assoc'' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n']. 
  Case "n = 0".
    reflexivity. 
  Case "n = S n'".
    simpl. rewrite -> IHn'. reflexivity.   Qed.

(** **** Ejercicio: 2 stars, advanced (plus_comm_informal) *)
(** Traduzca su prueba de [plus_comm] en una prueba informal. *)

(** Teorema: La adicion es conmutativa.
 
    Prueba: (* FILL IN HERE *)
[]
*)

(** **** Ejercicio: 2 stars, opcional (beq_nat_refl_informal) *)
(** Escriba una prueba informal del siguiente teorema, usando la
    prueba informal de [plus_assoc] como modelo.  No se restringa a
    parafrasear las tacticas de Coq en espaniol!
 
    Teorema: [true = beq_nat n n] para cada [n].
    
    Prueba: (* FILL IN HERE *)
[]
 *)

(* $Date: 2013-07-17 16:19:11 -0400 (Wed, 17 Jul 2013) $ *)
