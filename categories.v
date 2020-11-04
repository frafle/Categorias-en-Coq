(*modulo de listas*)
(*######################################################*)
Inductive list {X:Type} : Type :=
  | nil
  | cons (x : X) (l : @list X).


Fixpoint app {X : Type} (l1 l2 : @list X)
             : (@list X) :=
  match l1 with
  | nil  => l2
  | cons h t => cons h (app t l2)
  end.

Fixpoint rev {X:Type} (l: @list X) : @list X :=
  match l with
  | nil => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Fixpoint length {X : Type} (l : @list X) : nat :=
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.



Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

Fixpoint map {X Y: Type} (f:X -> Y) (l:@list X) : (@list Y) :=
  match l with
  | nil => nil
  | h :: t => (f h) :: (map f t)
  end.
(*######################################################*)


(*modulo de conjuntos finitos*)
(*######################################################*)
Definition finEmptySet {X: Type} := @nil X.

Definition finSet {X: Type} := @list X.

Fixpoint finSetEq {X: Type} (a: @finSet X) (b: @finSet X) (pred: X -> X -> bool) : bool :=
  match a, b with
  | nil, nil => true
  | h :: t, nil => false
  | nil, h :: t => false
  | h1 :: t1, h2 :: t2 => if pred (h1) (h2) then finSetEq (t1) (t2) (pred) else false
  end.
(*######################################################*)


(*Esta es la estructura basica de una categoria. La estructura comun para los objetos y flechas esta
capturado en la forma de una representacion que puede ser expresada con funciones para construir
representaciones. Se necesitan cuatro funciones para representar efectivamente una categoria:
	1, 2) las funciones de origen y objetivo (source and target) que retornan un objeto por cada flecha
	3) la funcion de identidad que retorna una flecha por cada uno de los objetos
	4) la funcion de composicion que por cada dos flechas que pueden ser compuestas retorna la flecha compuesta 
     resultante *)

Inductive category {O A: Type}: Type :=
  |cat (source: A -> O) (target: A -> O) (id: O -> A) (comp: A -> A -> A).

(*esta notacion se utilizara a la hora de hacer los match y simbolizara el valor construido*)

Notation "( x , y , z , w )" := (cat x y z w).

(*-----------------------------------------------------------------------*)

(*las flechas en la categoria de conjuntos finitos son tripletas que consisten de dos conjuntos y una funcion entre 
ellos*)

Inductive finSetArrow {X: Type}: Type :=
  |setArr (set1: @finSet X) (f: X -> X) (set2: @finSet X).

(*esta funcion retorna el conjunto de salida de setArrow*)

Definition finSetSource {X: Type} (s: @finSetArrow X): @finSet X:=
  match s with
  | setArr (a) (f) (c) => a
  end.

(*esta funcion retorna el conjunto de llegada de setArrow*)

Definition finSetTarget {X: Type} (s: @finSetArrow X): @finSet X:=
  match s with
  | setArr (a) (f) (c) => c
  end.

(*esta funcion retorna la funcion identidad de un conjunto en forma de finSetArrow*)

Definition finSetIdentity {X: Type} (a: @finSet X): @finSetArrow X := setArr (a) (fun x => x) (a).

(*opcion para el manejo de errores*)
Inductive option {X: Type} : Type := 
  |Some (x: X)
  |None.


(*esta funcion retorna la composicion de dos flechas con notacion g(f(x)) *)

Definition finSetComposition {X: Type} (a1: @finSetArrow X) (a2: @finSetArrow X) (pred: X -> X -> bool): 
  @option (@finSetArrow X) :=
  match a1, a2 with
  |setArr (c) (g) (d), setArr (a) (f) (b) => if finSetEq (b) (c) (pred) then
                                                  Some (setArr (a) (fun x => g (f (x))) (d) ) else None
  end.

Check finSetComposition.
(*esta funcion maneja el error de la composicion de funciones, en el caso de que los dos conjuntos no sean 
iguales. Si no lo son, se retorna una flecha finSetArrow donde el conjunto de llegada y salida son vacios
y la funcion que los une es una funcion que retorna el valor que se le da como parametro*)

Definition getOptionComp {X: Type} (op: @option (@finSetArrow X)) : @finSetArrow X :=
  match op with
  |Some x => x
  |None => setArr (@finEmptySet X) (fun x => x) (@finEmptySet X)
  end.


(*dado que la definicion de categoria espera un finSetArrow X -> finSetArrow X -> finSetArrow X se creo esta
funcion la cual asume que las funciones pueden ser compuestas,es decir, que los conjuntos b y c sean iguales*)

Definition finSetComposition' {X: Type} (a1: @finSetArrow X) (a2: @finSetArrow X): 
  @finSetArrow X :=
  match a1, a2 with
  |setArr (c) (g) (d), setArr (a) (f) (b) => setArr (a) (fun x => g (f (x))) (d)
  end.

(*se puede verificar que las funciones pueden ser compuestas con esta funcion*)

Definition composable {X: Type} (a1: @finSetArrow X) (a2: @finSetArrow X) (pred: X -> X -> bool): bool :=
  match a1, a2 with
  |setArr (c) (g) (d), setArr (a) (f) (b) => if finSetEq (b) (c) (pred) then true else false
  end.

(*teniendo esto, ahora podemos revisar el tipo de la categoria FinSet*)

Check @cat (finSet) (finSetArrow).

(*construccion de la categoria FinSet *)

Definition FinSetCat {X: Type} := (@finSetSource X, @finSetTarget X, @finSetIdentity X, @finSetComposition' X).

(*-----------------------------------------------------------------------*)

(*Definicion de una categoria finita:*)

(*objetos*)
Inductive objects: Type := 
  |a
  |b
  |c
  |none. (*para manejo de errores*)

(*verifica si dos objetos son iguales*)
Definition eqObj (o1 o2: objects): bool :=
  match o1, o2 with
  |a, a => true
  |b, b => true
  |c, c => true
  |_, _ => false
  end.

(*En genneral el manejo de errores no se puede hacer, ya que requiere el uso
de otro tipo de dato option, lo que rompe con el esquema general de las 
categorias como se plantearon*)

Module finiteCat.
(*flechas*)
Inductive arrows: Type := 
  |f
  |g
  |h
  |k
  |id (obj: objects)
  |noComp. (*para manejo de errores*)


(*objetos de salida*)
Definition s (arrow: arrows): objects := 
  match arrow with
  |f => b
  |g => a
  |h => a
  |k => b
  |id x => x
  |noComp => none 
  end.

(*objetos de llegada*)
Definition t (arrow: arrows): objects := 
  match arrow with
  |f => a
  |g => c
  |h => c
  |k => c
  |id x => x
  |noComp => none 
  end.

Definition ident := fun x => id (x). 

Definition comp (a1 a2: arrows): arrows :=
  match a1, a2 with
  | id x, u => if eqObj (x) (t u) then u else noComp (*t(u) debe ser igual a x*)
  | u, id x => if eqObj (x) (s u) then u else noComp (*s(u) debe ser igual a x*)
  | g, f => k
  | h, f => k
  | _, _ => noComp 
  end.

Definition FinCat := (s,t,ident,comp).

End finiteCat.

(*-----------------------------------------------------------------------*)

(*Functores*)
(*los functores consisten de dos funciones, una sobre los objetos y
otra sobre las flechas*)

Inductive functor {oA aA oB aB: Type}: Type :=
|func (catA: @category oA aA) (oFun: oA -> oB) (aFun: aA -> aB) (catB: @category oB aB).


(*functor identidad*)

Definition functId {X Y: Type} (cat: @category X Y): functor :=
      @func (X) (Y) (X) (Y) (cat) (fun x => x) (fun x => x) (cat).

(*functor entre un conjunto y su producto cartesiano*)

(*Definicion de pareja*)
Inductive prod {X Y: Type} : Type :=
|pair (p1: X) (p2: Y).

Inductive triple {X Y Z: Type} : Type :=
|trip (p1: X) (p2: Y) (p2: Z).  

Notation "( x , y )" := (pair x y).
Notation "( x , y , z )" := (trip x y z).


(*definicion de producto cartesiano en conjuntos finitos*)
Fixpoint aux {X Y: Type} (l1: @list X) (l2: @list Y):=
  match l1, l2 with
  |h1::t1, h2::t2 => (h1 , h2)::(aux (l1) (t2))
  |h1::t1, nil => nil
  |nil, _ => nil
  end.

Fixpoint cartesianProduct {X Y: Type} (l1: @finSet X) (l2: @finSet Y) :=
  match l1, l2 with
  |h1::t1, h2::t2 => app (aux l1 l2) (cartesianProduct t1 l2) 
  |nil, _ => nil
  |_, nil => nil
  end.

(*funcion que mapea parejas del producto cartesiano de dos dominios y
las envia a parejas del producto cartesiano de los codominios*)
Definition pairArrow {X Y: Type} (f: X -> X) (g: Y -> Y) (pareja: @prod X Y): @prod X Y :=
  match pareja with
  |(x , y) => ( (f x) , (g y) )
  end.
 
(*flechas entre productos cartesianos de FinSet, a partir de dos flechas
de FinSet (producto de flechas) *)
Definition prodArrow {X Y: Type} (s1: @finSetArrow X) (s2: @finSetArrow Y) : finSetArrow :=
  match s1, s2 with
  |setArr A f B, setArr C g D => setArr (cartesianProduct A C) 
                      (pairArrow f g) 
                      (cartesianProduct B D)
  end.

(*definicion del functor que va de un A: FinSet a A X A: FinSet X FinSet*)

Definition functAtoAXA {X: Type} := func (@FinSetCat X) 
                                  (fun A => cartesianProduct A A)
                                  (fun f => prodArrow f f)
                                  (@FinSetCat (@prod X X)).

(*Definicion de objeto inicial en una categoria*)

Inductive initialObj {X Y: Type} :=
  |ini (object: X) (function: X -> Y).

(*funcion vacia f:empty -> a*)

Definition emptyFunction {X: Type} (x: @option X) := @None X.

Check emptyFunction.

(*objeto inicial en FinSet *)

Definition finSetInitial {X: Type} := ini (finEmptySet) 
         (fun a => setArr (finEmptySet) (@emptyFunction X) (a)).

Check finSetInitial. 

(*Definicion de coproductos*)
Definition coproductCoCone {X Y: Type}: Type := (X * Y * Y) * 
                                                (X * Y * Y -> Y).

Definition coproduct {X Y: Type}: Type :=  (X * X) -> 
                                            @coproductCoCone X Y.

(*Definicion de coproducto en FinSet donde a+b es una union disjunta*)

(*Definicion de etiquetas para un conjunto u otro*)

Inductive Tag {X: Type} : Type :=
  |just (x: X)
  |setA (x: @Tag X)
  |setB (x: @Tag X).

Check setA.

(*definicion de union disjunta*)

Definition disjointU {X: Type} (a b: @finSet (@Tag X)) := 
                                  app (map setA a) (map setB b).

Compute disjointU [just 1; just 2; just 3] [just 1; just 2; just 3].

(*funcion [f,g] de la forma [f,g]: a+b -> c *)  

Definition fg {X: Type} (f g: @Tag X -> @Tag X) (tag: @Tag X): @Tag X  :=
  match tag with
  |setA x => f (x)
  |setB x => g (x)
  |just x => tag
  end.

(*flecha entre a+b y c*)

Definition univ {X: Type} (a b c: @finSet (@Tag X)) (s1 s2: @finSetArrow (@Tag X)) :=
  match s1, s2 with
  |setArr _ f _ , setArr _ g _ => setArr (disjointU a b) (fg f g) (c)
  end.

Check univ.      

(*coproducto final en finSet*)

Definition finSetCoProduct {X: Type} (a b: @finSet (@Tag X)) := 
pair ( trip (disjointU a b) (setArr a setA (disjointU a b)) (setArr b setB (disjointU a b)) )
     (univ a b).

Check finSetCoProduct.  








 







