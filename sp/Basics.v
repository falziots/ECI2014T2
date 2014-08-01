(** * Basics: Programacion Funcional en Coq *)
 
(* This library definition is included here temporarily 
   for backward compatibility with Coq 8.3.  
   Please ignore. *)
Definition admit {T: Type} : T.  Admitted.

(* ###################################################################### *)
(** * Introduccion *)

(** El estilo de programacion funcional acerca la progamacion a las
    matematicas: Si un procedimiento o metodo no tiene efectos
    colaterales, entonces casi todo lo que se necesita entender acerca
    del procedimiento es como relaciona entradas con salidas -- es
    decir, uno puede pensar su comportamiento como computar una
    funcion matematica.  Esta es una razon para la palabra "funcional"
    en "programacion funcional".  Esta conexion directa entre
    programas y objetos matematicos permite razonar informalmente,
    tanto como formalmente, acerca del comportamiento de los
    programas.

    El otro sentido en que la programacion funcional es "funcional" es
    que pone enfasis en el uso de funciones (o metodos) como valores
    _de primera clase_ -- es decir, valores que pueden ser pasados
    como argumentos de otras funciones, retornados como resultados,
    almacenados en estructuras de datos, etc.  El reconocimiento de
    que funciones pueden ser tratadas como datos en esta forma
    habilita una cantidad de expresiones utiles, como vamos a ver.

    Otras caracteristicas comunes a los lenguajes funcionales incluye
    _tipos de datos algebraicos_ y _"pattern matching"_, que facilita
    la construccion y manipulacion de estructuras de datos expresivas,
    junto con sofisticados _sistemas de tipos polimorficos_ que
    permiten abstraccion y reutilizacion de codigo.  Coq incluye todas
    estas caracteristicas.  *)


(* ###################################################################### *)
(** * Tipos Enumerados *)

(** Un aspecto poco usual de Coq es que esta conformado por un
    conjunto _extremadamente_ pequenio de elementos.  Por ejemplo, en
    vez de proveer la usual paleta de tipos de datos atomicos
    (booleanos, enteros, strings, etc.), Coq ofrece un mechanismo
    poderoso para definir nuevos tipos de datos desde cero -- tan
    poderoso que todos estos tipos familiares son reproducidos dentro
    de Coq mismo.

    Naturalmente, la distribucion oficial de Coq viene con una
    libreria estandard extensiva, que ya provee definiciones para los
    tipos de datos mencionados y muchos otros, como listas, tablas de
    hash, etc.  Pero no hay nada magico o primitivo acerca de estas
    definiciones de libreria: son codigo ordinario que cualquier
    usuario de Coq puede escribir.

    Para ver como funciona este mechanismo, empecemos por un ejemplo
    muy sencillo. *)

(* ###################################################################### *)
(** ** Dias de la Semana *)

(** La siguiente declaracion le dice a Coq que estamos definiendo un nuevo
    conjunto de valores -- un _tipo_ de datos. *)

Inductive day : Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.

(** El tipo es llamado [day] (dia), y sus miembros son [monday]
    (lunes), [tuesday] (martes), etc.  Desde la segunda hasta la
    octava linea de la definicion se pueden leer como "[monday] es un
    [day], [tuesday] es un [day], etc."

    Habiendo definido [day], podemos escribir funciones que operan
    sobre dias. *)

Definition next_weekday (d:day) : day :=
  match d with
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => monday
  | saturday  => monday
  | sunday    => monday
  end.

(** Noten que el tipo del argumento y de retorno estan declarados
    explicitamente.  Como muchos lenguajes de programacion funcionales,
    Coq ofrece la posibilidad de descubrir estos tipos si no son
    declarados explicitamente -- es decir, realiza _inferencia de tipos_
    -- pero vamos a escribirlos explicitamente de cualquier forma para
    facilitar la lectura. *)

(** Habiendo definido una funcion, vamos a verificar que funciona en
    algunos ejemplos.  Hay tres formas distintas de hacer esto en Coq.
    Primero, podemos usar el comando [Eval compute] para evaluar una
    expresion incluyendo [next_weekday].  *)

Eval compute in (next_weekday friday).
   (* ==> monday : day *)
Eval compute in (next_weekday (next_weekday saturday)).
   (* ==> tuesday : day *)

(** Si tienes una computadora a mano, este es un momento excelente
    para utilizar tu IDE favorito -- ya sea CoqIde o Proof General --
    y probarlo por ti mismo.  Carga este archivo ([Basics.v]) desde el
    codigo Coq acompaniando a este libro, busca el ejemplo anterior,
    ejecutalo en Coq, y observa el resultado. *)

(** La palabra clave [compute] le dice a Coq precisamente como evaluar
    la expresion que le dimos.  Por el momento, [compute] es lo unico
    que vamos a necesitar; mas tarde veremos otras alternativas que
    son a veces utiles. *)

(** Segundo, vamos a registrar que _esperamos_ que el resultado sea en
    la forma de un ejemplo de Coq: *)

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.

(** Esta declaracion hace dos cosas: crea una asercion (que el
    segundo dia de la semana luego de [saturday] es [tuesday]), y
    provee un nombre a tal afirmacion para que nos podamos referir a
    ella mas tarde. *)
(** Habiendo hecho esta asercion, podemos pedirle a Coq que la
    verifique de la siguiente manera: *)

Proof. simpl. reflexivity.  Qed.


(** Los detalles no son importantes de momento (volveremos a ellos en
    un segundo), pero esencialmente esto se puede leer como "La
    asercion que hicimos puede ser probada observando que ambos
    lados de la igualdad son iguales, luego de simplificar (en este
    caso, evaluar) la expresion". *)

(** Podemos pedirle a Coq que "extraiga" un programa, desde una
    [Definition], a un lenguaje de programacion mas convencional
    (OCaml, Scheme, o Haskell) con un compilador de alta performance.
    Esta facilidad es muy interesante, puesto que nos permite una
    forma de construir programas _totalmente certificados_ en
    lenguajes conocidos.  De hecho, este es uno de los usos
    principales por los cuales Coq fue desarrollado.  Volveremos a
    este tema en capitulos posteriores.  Para mas informacion,
    referimos al lector al libro "Coq'Art" de Bertot y Casteran, asi
    como tambien al manual de referencia de Coq. *)

(* ###################################################################### *)
(** ** Booleanos *)

(** De forma similar, podemos definir el tipo [bool] de valores booleanos,
    con miembros [true] y [false]. *)

Inductive bool : Type :=
  | true : bool
  | false : bool.

(** Aunque estamos escribiendo nuestros propios booleanos para
    ilustrar que se puede construir todo desde cero, Coq incluye, por
    supuesto, una implementacion "default" de los booleanos en su
    libreria estandard, junto a una multitud de funciones utiles y
    lemmas.  (Mirar a [Coq.Init.Datatypes] en la documentacion de la
    libreria estandard de Coq para mas datos.)  Cuando sea posible,
    vamos a nombrar las definiciones y teoremas con los mismos nombres
    que los utilizados en las librerias de Coq. *)

(** Podemos definir funciones sobre booleanos de la misma forma como
    hicimos antes: *)

(** Negacion: *)
Definition negb (b:bool) : bool := 
  match b with
  | true => false
  | false => true
  end.

(** Conjuncion: *)
Definition andb (b1:bool) (b2:bool) : bool := 
  match b1 with 
  | true => b2 
  | false => false
  end.

(** Disyuncion: *)
Definition orb (b1:bool) (b2:bool) : bool := 
  match b1 with 
  | true => true
  | false => b2
  end.

(** Los ultimos dos ilustran la sintaxis utilizada para definiciones
    de funciones con varios argumentos. *)

(** Los siguientes "unit tests" (tests de un unidad) constituyen una
    especificacion completa -- una tabla de verdad -- para la funcion
    [orb]: *)

Example test_orb1:  (orb true  false) = true. 
Proof. reflexivity.  Qed.
Example test_orb2:  (orb false false) = false.
Proof. reflexivity.  Qed.
Example test_orb3:  (orb false true)  = true.
Proof. reflexivity.  Qed.
Example test_orb4:  (orb true  true)  = true.
Proof. reflexivity.  Qed.

(** (Notar que omitimos el [simpl] en las pruebas.  No es necesario
    porque [reflexivity] de hecho realiza la simplificacion
    automaticamente.) *)

(** _Una nota sobre la notacion_: Usamos corchetes para delimitar
    fragmentos de codigo Coq en los comentarios de los archivos .v;
    esta convecion, que es tambien utilizada por la herramienta de
    documentacion [coqdoc], separa el codigo visualemente del texto
    alrededor del codigo.  En la version html, estos pedazos de texto
    aparecen con [fuente diferente]. *)

(** Los valores [Admitted] y [admit] puede ser utilizados para llenar
    un agujero en una definicion o prueba incompleta.  Los usamos aqui
    en los siguientes ejercicios.  En general, tu trabajo en los
    ejercicios es reemplazar [admit] o [Admitted] con una definicion o
    prueba concreta. *)

(** **** Ejercicio: 1 star (nandb) *)
(** Complete la definicion de la siguiente funcion.  Luego asegurese
    de que los ejemplos a continuacion pueden ser verificados
    correctamente por Coq.  *)

(** Esta funcion debe retornar [true] si ambos o uno de los inputs es
    [false]. *)

Definition nandb (b1:bool) (b2:bool) : bool :=
  (* FILL IN HERE *) admit.

(** Remover "[Admitted.]" y llenar cada prueba con
    "[Proof. reflexivity. Qed.]" *)

Example test_nandb1:               (nandb true false) = true.
(* FILL IN HERE *) Admitted.
Example test_nandb2:               (nandb false false) = true.
(* FILL IN HERE *) Admitted.
Example test_nandb3:               (nandb false true) = true.
(* FILL IN HERE *) Admitted.
Example test_nandb4:               (nandb true true) = false.
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Ejercicio: 1 star (andb3) *)
(** Repita la misma idea para la funcion [andb3] de abajo.  Esta
    funcion retorna [true] cuando todos sus input son [true], y
    [false] en cualquier otro caso. *)

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  (* FILL IN HERE *) admit.

Example test_andb31:                 (andb3 true true true) = true.
(* FILL IN HERE *) Admitted.
Example test_andb32:                 (andb3 false true true) = false.
(* FILL IN HERE *) Admitted.
Example test_andb33:                 (andb3 true false true) = false.
(* FILL IN HERE *) Admitted.
Example test_andb34:                 (andb3 true true false) = false.
(* FILL IN HERE *) Admitted.
(** [] *)

(* ###################################################################### *)
(** ** Tipos de Funcion *)

(** El comando [Check] hace que Coq imprima el tipo de una expresion.
    Por ejemplo, el tipo de [negb true] es [bool]. *)

Check true.
(* ===> true : bool *)
Check (negb true).
(* ===> negb true : bool *)

(** Funciones como [negb] son tambien valores, como [true] y [false].
    Sus tipos son llamados _tipos de funcion_, y se escriben con
    flechas. *)

Check negb.
(* ===> negb : bool -> bool *)

(** El tipo de [negb], escrito [bool -> bool] y pronunciado "[bool]
    flecha [bool]," puede leerse como, "Dado una entrada (argumento)
    de tipo [bool], esta funcion produce una salida de tipo [bool]."
    Similarmente, el tipo de [andb], escrito [bool -> bool -> bool],
    puede leerse como, "Dado dos argumentos, ambos de tipo [bool],
    esta funcion produce un resultado de tipo [bool]." *)

(* ###################################################################### *)
(** ** Numeros *)

(** _Digresion tecnica_: Coq provee un _sistema de modulos_ bastante
    sofisticado, para ayudar a organizar grandes desarrollos.  En este
    curso no vamos a utilizar muchas de sus caracteristicas, pero hay
    una que es partiuclarmente util: Si encerramos una coleccion de
    declaraciones entre [Module X] y [End X], entonces, en el resto
    del archivo luego del [End] estas definiciones van a ser referidas
    con [X.foo] en vez de [foo].  Aqui, utilizamos esta caracteristica
    para introducir definiciones de tipo [nat] en un modulo interno,
    de forma que no sobreescriba la que viene por default en la
    libreria estandard. *)

Module Playground1.

(** Los tipos que definimos hasta ahora son ejemplos de "tipos
    enumerados": Su definicion explicitamente enumera un a serie de
    elementos.  Una forma mas interesante de definir un tipo es
    proveyendo una serie de "reglas inductivas" describiendo sus
    elementos.  Por ejemplo, podemos definir a los numeros naturales como: *)

Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

(** Las clausulas de esta definicion se pueden leer como: 
      - [O] es un numero natural (Notar que es la letra "[O]," no el numeral 
        "[0]").
      - [S] es el "constructor" que toma un numero natural y retorna otro 
        -- eso es, si [n] es un numero natural, entonces [S n] lo es tambien.

    Veamoslo con mayor detalle.

    Cada conjunto definido inductivamente ([day], [nat], [bool], etc.)
    es en realidad un conjunto de _expresiones_.  La definicion de
    [nat] dice como estas expresiones en el conjunto [nat] pueden ser
    construidas:

    - la expresion [O] pertence al conjunto [nat]; 
    - si [n] es una expresion perteneciente al conjunto [nat], entonces [S n]
      tambien es una expresion perteneciente al conjunto [nat]; y
    - expresiones formadas de estas dos formas son las unicas pertenecientes 
      al conjunto [nat].

    Las mismas reglas se aplican a las definiciones de [day] y
    [bool]. Las anotaciones que usamos para sus constructores son
    analogos a las el constructor [O], e indican que cada uno de estos
    constructores no toma ningun argumento. *)

(** Estas tres condiciones son la fortaleza de la declaracion
    [Inductive].  Implican que la expresion [O], la expresion [S O],
    la expresion [S (S O)], la expresion [S (S (S O))], etc, todas
    pertenecen al conjunto [nat], mientras que otras como [true],
    [andb true false], y [S (S false)] no.

    Podemos escribir funciones que "pattern matchean" numeros
    naturales como hicimos antes -- por ejemplo, la funcion
    predecesor: *)

Definition pred (n : nat) : nat :=
  match n with
    | O => O
    | S n' => n'
  end.

(** La segunda clausula puede leerse como: "si [n] tiene la forma [S n']
    para algun [n'], entonces retornar [n']."  *)

End Playground1.

Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.

(** Como los numeros naturales son tan importantes, Coq provee
    funcionalidad para imprimirlos y "parsearlos": se puede utilizar un
    numeral arabico ordinario como alternativa a la representacion
    "unaria" definida con los constructores [S] y [O].  Coq imprime el
    numero en forma arabica tambien como default: *)

Check (S (S (S (S O)))).
Eval simpl in (minustwo 4).

(** El constructor [S] tiene tipo [nat -> nat], igual que las
    funciones [minustwo] y [pred]: *)

Check S.
Check pred.
Check minustwo.

(** Estas son todas cosas que pueden ser aplicadas a un numero para
    retornar otro numero.  Sin embargo, hay una diferencia
    fundamental: las funciones como [pred] y [minustwo] vienen con
    _reglas computacionales_ -- es decir, la definicion de [pred] dice
    que [pred 2] puede simplificarse a [1] -- mientras que la
    definicion de [S] no tiene ningun comportamiento.  Aunque es como
    una funcion en el sentido de que puede ser aplicada a un
    argumento, _no hace_ nada en absoluto!  *)

(** Para casi todas las funciones sobre numeros, pattern matching no
    es suficiente: necesitamos tambien recursion.  Por ejemplo, para
    ver que un numero [n] es par (even en ingles), debemos
    recusivamente ver que [n-2] es par.  Para escribir tal funcion
    necesitamos la palabra clave [Fixpoint] (punto fijo). *)

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => evenb n'
  end.

(** Podemos definir [oddb] (impar) de forma similar, con la
    declaracion [Fixpoint], pero hay una forma mejor: *)

Definition oddb (n:nat) : bool   :=   negb (evenb n).

Example test_oddb1:    (oddb (S O)) = true.
Proof. reflexivity.  Qed.
Example test_oddb2:    (oddb (S (S (S (S O))))) = false.
Proof. reflexivity.  Qed.

(** Naturalmente, podemos tambien definir funciones recursivas con
    multiples argumentos.  (De nuevo, usamos un modulo para evitar
    conflictos de nomenclatura.) *)

Module Playground2.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

(** Sumar 3 a 2 nos da 5, como esperamos. *)

Eval simpl in (plus (S (S (S O))) (S (S O))).

(** La simplificacion que Coq realiza para llegar a esta conclusion
    puede verse como sigue: *)

(*  [plus (S (S (S O))) (S (S O))]    
==> [S (plus (S (S O)) (S (S O)))] por la segunda clausula de [match]
==> [S (S (plus (S O) (S (S O))))] por la segunda clausula de [match]
==> [S (S (S (plus O (S (S O)))))] por la segunda clausula de [match]
==> [S (S (S (S (S O))))]          por la primer clausula de [match]
*)

(** Los argumentos se pueden agrupar si tienen el mismo tipo para
    facilitar la lectura.  En la siguiente definicion [(n m : nat)]
    significa lo mismo que si hubieramos escrito [(n : nat) (m : nat)]. *)

Fixpoint mult (n m : nat) : nat :=
  match n with
    | O => O
    | S n' => plus m (mult n' m)
  end.

Example test_mult1: (mult 3 3) = 9.
Proof. reflexivity.  Qed.

(** Se pueden matchear dos expresiones a la vez poniendo una coma entre ellas: *)

Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O   , _    => O
  | S _ , O    => n
  | S n', S m' => minus n' m'
  end.

(** El _ en la primer linea es un _patron comodin_.  Escribir _ en un
    patron es lo mismo que escribir una variable que luego no es
    utilizada en el lado derecho de la clausula.  Esto evita tener que
    inventar nombres innecesarios. *)

End Playground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
    | O => S O
    | S p => mult base (exp base p)
  end.

(** **** Ejercicio: 1 star (factorial) *)
(** Recuerde la funcion factorial (notada normalmente n!):
<<
    factorial(0)  =  1 
    factorial(n)  =  n * factorial(n-1)     (si n>0)
>>
    Traducir esto a Coq. *)

Fixpoint factorial (n:nat) : nat := 
(* FILL IN HERE *) admit.

Example test_factorial1:          (factorial 3) = 6.
(* FILL IN HERE *) Admitted.
Example test_factorial2:          (factorial 5) = (mult 10 12).
(* FILL IN HERE *) Admitted.
(** [] *)

(** Podemos hacer las expresiones numericas mas faciles de leer
    introduciendo notaciones para la adicion, multiplicacion, y
    resta. *)

Notation "x + y" := (plus x y)  
                       (at level 50, left associativity) 
                       : nat_scope.
Notation "x - y" := (minus x y)  
                       (at level 50, left associativity) 
                       : nat_scope.
Notation "x * y" := (mult x y)  
                       (at level 40, left associativity) 
                       : nat_scope.

Check ((0 + 1) + 1).

(** (Las anotaciones [level], [associativity], y [nat_scope] controlan
   como estas notaciones deben ser tratadas por el parser de Coq.  Los
   detalles no son importantes, pero el interesado puede ir a la
   subseccion "Mas sobre Notacion" en la seccion "Material Opcional"
   al final de este capitulo). *)

(** Notar que estas notaciones no cambian las definiciones que
    hicimos: son simplemente instrucciones al parser de Coq para
    aceptar [x + y] ademas de [plus x y] y, de forma inversa, para
    indicar al "pretty-printer" (la funcion de impresion en pantalla)
    que imprima [plus x y] como [x + y]. *)

(** Cuando decimos que Coq no viene con nada "built-in", lo decimos en
    serio: hasta la igualdad de numeros naturales es una operacion
    definida!  *)

(** La funcion [beq_nat] verifica si dos numeros [nat]urales son
   [eq]uivalentes, retornando un [b]ooleano.  Notar el uso de
   [match]es sucesivos (tambien podriamos haber hecho un match
   simultaneo, como hicimos con [minus]). *)

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.

(** De forma analoga, la funcion [ble_nat] verifica si dos numeros
    [nat]urales son "[l]ess-or-[e]qual" (menor o igual), retornando un
    [b]ooleano. *)

Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => ble_nat n' m'
      end
  end.

Example test_ble_nat1:             (ble_nat 2 2) = true.
Proof. reflexivity.  Qed.
Example test_ble_nat2:             (ble_nat 2 4) = true.
Proof. reflexivity.  Qed.
Example test_ble_nat3:             (ble_nat 4 2) = false.
Proof. reflexivity.  Qed.

(** **** Ejercicio: 2 stars (blt_nat) *)
(** La funcion [blt_nat] verifica si dos numeros [nat]urales son
    "[l]ess-[t]han" (menor), retornando un [b]ooleano.  En vez de
    hacer un nuevo [Fixpoint] para esta funcion, definala en terminos
    de definiciones previas.
    
    Nota: Si tiene problemas con la tactica [simpl], intente usar
    [compute], que es como [simpl] con esteroides.  Sin embargo, hay
    una solucion simple y elegante para la cual [simpl] es
    suficiente. *)

Definition blt_nat (n m : nat) : bool :=
  (* FILL IN HERE *) admit.

Example test_blt_nat1:             (blt_nat 2 2) = false.
(* FILL IN HERE *) Admitted.
Example test_blt_nat2:             (blt_nat 2 4) = true.
(* FILL IN HERE *) Admitted.
Example test_blt_nat3:             (blt_nat 4 2) = false.
(* FILL IN HERE *) Admitted.
(** [] *)

(* ###################################################################### *)
(** * Demostracion por Simplificacion *)

(** Ahora que definimos un par de tipos de datos y funciones, pasemos
    a la pregunta de como establecer y demostrar propiedades sobre su
    comportamiento.  De hecho, en cierto sentido, ya empezamos a hacer
    esto: cada [Example] en las secciones previas conjetura de forma
    precisa cual debe ser el comportamiento de alguna funcion con un
    input particular.  Las pruebas de estas conjeturas fueron siempre
    igual: usar [reflexivity] para verificar que ambos lados de la [=]
    simplifican (es decir, pueden ser reducidos) a valores identicos.
 
    (Dicho sea de paso, va a ser util mas tarde saber que
    [reflexivity] de hecho hace algo mas que [simpl] -- por ejemplo,
    intenta hacer "unfolding" sobre terminos definidos, reemplazando
    el nombre de una definicion con su cuerpo.  La razon para esta
    diferencia es que, cuando [reflexivity] termina, el objetivo esta
    alcanzado y no queremos mirar a ver como es que expandiendo las
    expresiones [reflexivity] encontro la solucion.  En contraste,
    [simpl] se utiliza en situaciones donde queremos leer y entender
    el nuevo objetivo, con lo que no queremos que expanda definiciones
    de forma ciega.)

    El mismo tipo de "demostracion por simplificacion" puede ser
    utilizado para probar propiedades mas interesantes tambien.  Por
    ejemplo, el hecho de que [0] es un "elemento neutral" para [+] a
    la izquierda puede ser provado simplemente observando que [0 + n]
    reduce a [n], sin importar el [n], un hecho que se puede observar
    de la definicion de [plus].*)

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n. reflexivity.  Qed.


(** (_Nota_: Puede notar que el teorema de arriba se ve diferente en
    la version html que en la version original.  En los archivos Coq
    escribimos el cuantificado universal con la palabra reservada
    "_forall_".  Esto se imprime en el html como la "A" invertida, la
    notacion tipica en logica.)  *)

(** La forma de este teorema y la prueba son casi iguales a los
    ejemplos anteriores; hay apenas unas diferencias.

    Primero, usamos el comando [Theorem] en vez de [Example].  De
    hecho, esta diferencia es puramente un tema de estilo; los
    comandos [Example] y [Theorem] (y otros como [Lemma], [Fact], y
    [Remark]) tienen el mismo significado en Coq.

    Segundo, hemos agregado el cuantificador [forall n:nat], de forma
    que nuestro teorema hable de _todo_ numero natural [n].  Para
    poder probar teoremas de esta forma, necesitamos poder razonar
    _asumiendo_ la existencia de un numero arbitrario [n].  Este
    razonamiento se ve reflejado en la prueba con el comando [intros
    n], que, en cierto sentido, mueve el cuantificador desde el
    objetivo hacia el "contexto" de asunciones actuales.  En efecto,
    empezamos la prueba diciendo "OK, supongamos [n] es un numero
    natural arbitrario".

    Las palaras claves [intros], [simpl], y [reflexivity] son ejemplos
    de _tacticas_.  Una tactica es un comando que es utilizado entre
    [Proof] y [Qed] para decirle a Coq como debe verificar la
    correccion de una conjetura que estamos haciendo.  Vamos a ver
    varias tacticas mas en el resto de este capitulo, y muchas mas en
    capitulos futuros. *)


(** Vaya paso por paso en las siguientes pruebas, y note como el
    objetivo y el contexto cambian. *)

Theorem plus_1_l : forall n:nat, 1 + n = S n. 
Proof.
  intros n. reflexivity.  Qed.

Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof.
  intros n. reflexivity.  Qed.

(** El sufijo [_l] en los nombres de estos teoremas se pronuncia "a la
    izquierda" (por [l]eft, en ingles). *)


(* ###################################################################### *)
(** * Demostracion por Reescritura *)

(** Aqui hay un teorema ligeramente mas interesante: *)

Theorem plus_id_example : forall n m:nat,
  n = m -> 
  n + n = m + m.

(** En vez de hacer una conjetura universal sobre todo los numeros [n]
    y [m], este teorema es sobre una propiedad mas especifica que solo
    vale cuando [n = m].  El simbolo flecha [->] se pronuncia
    "implica".

    Como antes, necesitamos poder razonar asumiendo la existencia de
    numeros naturales [n] y [m].  Tambien necesitamos asumir la
    hipotesis [n = m].  La tactica [intros] sirve para mover las tres
    hipotesis desde el objetivo al contexto actual.

    Como [n] y [m] son arbitrarios, no podemos simplemente simplificar
    para provar este teorema.  En vez, lo probamos observando que, si
    estamos asumiendo que [n = m], entonces podemos reemplazar a [n]
    por [m] en el objetivo y obtener una igualdad con la misma
    expresion de ambos lados.  La tactica que le dice a Coq como
    realizar este reemplazo se llama [rewrite] (reescribir). *)

Proof.
  intros n m.   (* mover ambos cuantificadores al contexto *)
  intros H.     (* movee la hipotesis al contexto *)
  rewrite -> H. (* Reescribir el objetivo usando la hipotesis *)
  reflexivity.  Qed.

(** La primera linea de la prueba, como dijumos, mueve las variables
    cuantificadas universalmente [n] y [m] en el contexto.  La segunda
    mueve la hipotesis [n = m] en el contexto, y le asigna el nombre
    (arbitrario) [H].  La tercera le dice a Coq que reescriba el
    objetivo actual ([n + n = m + m]) reemplazando el lado izquierda
    de la hipotesis de igualdad [H] con el lado derecho, obteniendo [m + m = m + m].

    (La flecha en el [rewrite] no tiene nada que ver con la
    implicacion: le dice a Coq en que direccion realizar la
    reescritura, en este caso de izquierda a derecha.  Para reescribir
    en la direccion contraria, es decir de derecha a izquierda ([m]
    por [n] en vez de [n] por [m]), se puede utilizar [rewrite <-].
    Pruebe haciendo este cambio en la preuba anterior y vea la
    diferencia). *)

(** **** Ejercicio: 1 star (plus_id_exercise) *)
(** Remover "[Admitted.]" y llenar la prueba. *)

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** Como hemos visto en ejemplos anteriores, el comando [Admitted] le
    dice a Coq que queremos saltearnos la prueba del teorema y que la
    acepte como dada.  Esto es util cuando estamos realizando una
    prueba larga, porque podemos establecer lemas intermedios que
    creemos que pueden sernos util para resolver una prueba mas
    grande, admitirlas (con [Admitted]) por el momento, y continuar
    pensando en la preuba principal hasta que estamos seguros que
    tiene sentido.  Luego podemos volver y llenar las pruebas que nos
    salteamos.  Pero debe ser cuidadoso: cada vez que dice [Admitted]
    (o [admit]), usted esta dejando una puerta abierta a un argumento
    falso en el limpio, riguroso, y formalmente verificado mundo de
    Coq!  *)

(** No solo podemos utilizar hiptosis del contexto con la tactica
    [rewrite].  Tambien podemos utilizarla con un teorema demostrado
    anteriormente. *)

Theorem mult_0_plus : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_O_n.
  reflexivity.  Qed.

(** **** Ejercicio: 2 stars (mult_S_1) *)
Theorem mult_S_1 : forall n m : nat,
  m = S n -> 
  m * (1 + n) = m * m.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)



(* ###################################################################### *)
(** * Prueba por Analisis por Caso *) 

(** Por supuesto, no todo puede ser probado por una simple
    simplificacion: En general, valores hipoteticos (numeros,
    booleanos, listas, etc. arbitrarios) pueden bloquear la reduccion.
    Por ejemplo, si intentamos probar el siguiente teorema usando la
    tactica [simpl] como hicimos antes, nos quedamos bloqueados. *)

Theorem plus_1_neq_0_firsttry : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n. 
  simpl.  (* does nothing! *)
Abort.

(** La razon para esto es que las definiciones de ambos [beq_nat] y
    [+] comienzan haciendo un [match] en su primer argumento.  Pero
    aqui, el primer argumento de [+] es el numero desconocido [n], y
    el argumento de [beq_nat] es la expresion compuesta [n + 1];
    ninguno puede ser simplificado. 

    Lo que necesitamos es tener la capacidad de razonar las posibles
    formas de [n] por separado.  Si [n] es [O], entonces calculamos el
    resultado final de [beq_nat (n + 1) 0] y verificamos que es, en
    efecto, [false].  Y si [n = S n'], para algun numero [n'],
    entonces, aunque no sabemos exactamente que numero [n + 1] va a
    retornar, igual podemos calcular que, al menos, va a empezar con
    un [S].  Y eso es suficiente para calcular que, de nuevo, [beq_nat
    (n + 1) 0] va a retornar [false].

    La tactica que le dice a Coq que considere por separado los casos
    donde [n = O] y donde [n = S n'] se llama [destruct]. *)

Theorem plus_1_neq_0 : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n. destruct n as [| n'].
    reflexivity.
    reflexivity.  Qed.

(** La tactica [destruct] genera _dos_ sub-objetivos, que debemos
    demostrar por separado para que Coq acepte el teorema como
    demostrado.  (No se necesita ningun comando especial para pasar
    del primer sub-objetivo al siguiente.  Cuado el primero ha sido
    demostrado, simplemente desaparece y nos deja con el otro "en foco").
    En esta prueba, ambos sub-objetivos son facilmente demostrados por
    el uso de [reflexivity]. 

    La notacion "[as [| n']]" se denomina _patron intro_.  Le dice a
    Coq que nombres de variables introducir en cada sub-objetivo.  En
    general, lo que sigue entre los corchetes es una _lista_ de lista
    de nombres, separada por [|].  Aqui, el primer componente es la
    lista vacia, porque el constructor [O] es nulario (no contiene
    niguna informacion).  El segundo componente provee un solo nombre
    [n'], puesto que [S] es un constructor unario.

    La tactica [destruct] puede ser utilizada con cualquier tipo de
    datos definido inductivamente.  Por ejemplo, la usamos aqui para
    demostrar que la negacion booleana es involutiva -- es decir, que
    negacion es su propio inverso. *)

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b.
    reflexivity.
    reflexivity.  Qed.

(** Notar que el uso de [destruct] aqui no tiene ninguna clausula
    [as], porque ninguno de los sub-casos de [destruct] necesita ligar
    alguna variable, con lo que no necesitamos nombres.  (Tambien
    podriamos haber escrito [as [|]], o [as []]).  De hecho, podemos
    omitir la clausula [as] de _cualquier_ [destruct] y Coq va a
    llenar el contexto con nombres generados automaticamente.  Aunque
    puede parecer util, se puede argumentar que es un mal estilo de
    programacion, porque Coq elige los nombres de forma abitraria, y a
    veces inconsistentes.  *)

(** **** Ejercicio: 1 star (zero_nbeq_plus_1) *)
Theorem zero_nbeq_plus_1 : forall n : nat,
  beq_nat 0 (n + 1) = false.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ###################################################################### *)
(** * Mas Ejercicios *)

(** **** Ejercicio: 2 stars (funciones booleanas) *)
(** Use las tacticas que ha aprendido hasta ahora para demostrar el
    siguiente teorema acerca de funciones booleanas. *)

Theorem identity_fn_applied_twice : 
  forall (f : bool -> bool), 
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  (* FILL IN HERE *) Admitted.

(** Ahora indique y demuestre un teorema [negation_fn_applied_twice]
    similar a la previa definicion pero en que la segunda hipotesis
    dice que la funcion [f] tiene la propiedad [f x = negb x].*)

(* FILL IN HERE *)

(** **** Ejercicio: 2 stars (andb_eq_orb) *)
(** Demuestre el siguiente teorema.  (Tal vez quiera provar primero
    algun lema auxiliar o dos).  *)

Theorem andb_eq_orb : 
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  (* FILL IN HERE *) Admitted.

(** **** Ejercicio: 3 stars (binary) *)
(** Considere una representacion diferente, y mas eficiente, de
    numeros naturales, usando un sistema binario en vez de unario.  Es
    decir, en vez de decir que cada numero es o cero o el sucesor de
    un numero natural, podemos decir que cada numero binario es o

      - cero,
      - dos veces un numero binario, o
      - uno mas que dos veces un numero binario.

    (a) Primero, escriba una definicion inductiva del tipo [bin]
        correspondiente a esta descripcion de numeros binarios.

    Ayuda: Recuerde que la definicion de [nat],

    Inductive nat : Type :=
      | O : nat
      | S : nat -> nat.

    no dice nada acerca de lo que [O] y [S] "significan".  Solo dicen
    "[O] esta en el conjunto llamado [nat], y si [n] esta en el
    conjunto, entonces tambien [S n] esta".  La interpretacion de que
    [O] es el numero cero y [S] el sucesor/mas uno viene por la froma
    en que _usamos_ los valores de [nat], cuando escribimos funciones
    que los utilizan, cuando probamos cosas acerca de ellos, etc.  Su
    definicion de [bin] debe ser, en consecuencia, simple; son las
    funciones que va a escribir a continuacion las que le de
    significado matematico.

    (b) A continuacion, escriba una funcion que incremente un numero
        binario en uno, y otra que convierta de un numero binario a un
        numero unario.

    (c) Escriba algunos tests de unidad para ambas funciones.  Note
        que incrementar un numero binario y convertirlo a un numero
        unario debe retornar el mismo resultado que primero
        convertirlo y luego incrementarlo como unario.  *)

(* FILL IN HERE *)
(** [] *)

(* ###################################################################### *)
(** * Material Opcional *)

(** ** Mas sobre Notacion *)

Notation "x + y" := (plus x y)  
                       (at level 50, left associativity) 
                       : nat_scope.
Notation "x * y" := (mult x y)  
                       (at level 40, left associativity) 
                       : nat_scope.

(** Por cada simbolo de notacion en Coq podemos especificar su _nivel
    de precedencia_ y su _asociatividad_.  El nivel de presedencia [n]
    puede ser especificado con las palabras claves [at level n] y es
    util para disambiguar expresiones conteniendo distintos simbolos.
    La asociatividad es util para disambiguar expresiones conteniendo
    mas de una ocurrencia del mismo simbolo.  Por ejemplo, los
    parametros especificados arriba para [+] y [*] dicen que la
    expresion [1+2*3*4] es la forma corta para la expresion
    [(1+((2*3)*4))]. Coq usa niveles de precedencia de 0 a 100, y
    asociatividad _left_ (izquierda), _right_ (derecha), o _no_
    asociatividad.

    Cada simbolo de notacion en Coq es activo en un _contexto de
    notacion_.  Coq intenta adivinar el contexto, de forma que cuando
    escribimos [S(O*O)] adivina que debe ser [nat_scope], pero cuando
    escribimos el tipo del producto cartesiano (tupla) [bool*bool]
    adivina [type_scope].  Ocasionalmente debemos ayudarlo escribiendo
    el contexto prefijado con un simbolo de porcentaje, como
    [(x*y)%nat], y a veces Coq va a indicar en el output que esta
    usando un cierto "scope" para determinada expresion.

    Los contextos de notacion tambien aplican a la notacion numeral
    (3,4,5, etc.), con lo que a veces es comun ver [0%nat] para decir
    [O], o [0%Z] para indicar el cero de los enteros (Integer).  *)

(** ** [Fixpoint]s y Recursion Estructural  *)

Fixpoint plus' (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus' n' m)
  end.

(** Cuando Coq verifica esta definicion, nota que [plus'] esta
    "decreciendo en su primer argumento".  Lo que esto significa es
    que estamos realizando _recursion estructural_ sobre el argumento
    [n] -- es decir, que vamos a hacer llamadas recursivas unicamente a un
    valor estrictamente menor al argumento [n].  Esto implica que
    todas las llamadas a [plus'] van a terminar eventualmente.  Coq
    exige que _algun_ argumento de _cada_ definicion de punto fijo sea
    "decresciente".

    Este requerimiento es un feature fundamental en el disenio de Coq:
    En particular garantiza que cada funcion que se pueda definir va a
    terminar en todo input.  Sin embargo, el analisis que realiza
    Coq para determinar que una funcion es decresciente no es muy
    sofisticado, y a veces es necesario escribir funciones de forma un
    tanto poco natural para convencerlo.  *)

(** **** Ejercicio: 2 stars, opcional (decreasing) *)
(** Para concretizar lo dicho, busque una forma de escribir un punto
    fijo perfectamente valido, es decir, que _termine_ en todo input,
    pero que Coq _no_ acepte por esta restriccion.  *)

(* FILL IN HERE *)
(** [] *)

(* $Date: 2013-07-17 16:19:11 -0400 (Wed, 17 Jul 2013) $ *)

