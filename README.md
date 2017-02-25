# recur v1.0 ： provide recursion scheme combinators for Scala
<b>recur</b> is a library provide recursion scheme combinators (catamorphism, paramorphism, anamorphism, etc.) for Scala. It's based on [Category:Recursion Schemes](https://en.wikipedia.org/wiki/Category:Recursion_schemes)

# Using recur
## Catamorphism
Catamorphisms provided via generic function : `F_Algebra.cata`, `Mendler_Style.mcata`, `F_W_Algebra.g_cata` or use the `constructor type-functors` (will be introduced later)
### Initial Fixed-Point
Use the `F_Algebra.cata` (standard fold)
```scala
  import algebra.Functor, algebra.F_Algebra.{Fix, mu, cata}

  //type List[A] = μ(ListFFunctor[A])
  trait ListF[+A, +B]
  case object Nil extends ListF[Nothing, Nothing]
  case class Cons[A, B](a: A, b: B) extends ListF[A, B]

  //an endofunctor F
  implicit def ListFFunctor[T] = new Functor[ListF[T, ?]] {
    def map[A, B](fa: ListF[T, A])(f: A => B): ListF[T, B] = fa match {
      case Nil => Nil
      case Cons(a, b) => Cons(a, f(b))
    }
  }

  type ListFInt[A] = ListF[Int, A]
  def nil = mu[ListFInt[Nothing], ListFInt](Nil)
  def cons[B](a: Int, b: B) = mu[ListFInt[B], ListFInt](Cons(a, b))

  //algSum :: ListF Int Int -> Int
  val algSum: ListFInt[Int] => Int = {
    case Nil => 0
    case Cons(e, acc) => e + acc
  }

  //lst :: Fix (ListF Int)
  val lst: Fix[ListFInt] = cons(2, cons(3, cons(4, nil)))

  val foldr = cata[ListFInt, Int](algSum)

  println(foldr(lst)) //9
```

### Mendler Style
catamorphism as a recursion scheme a la Mendler, which removes the dependency on the Functor typeclass, because `Algebra (CoYoneda f) a = MendlerAlgebra f a`

```scala
  import algebra.~>>
  import algebra.Mendler_Style.{mcata, MendlerAlgebra}

  //rank-2 function
  object ms_algSum extends MendlerAlgebra[ListFInt, Int] {
    override def apply(v1: algebra.Id ~>> Int): ListFInt ~>> Int = {
      val sum = new (ListFInt ~>> Int) {
        override def apply[A](a: ListFInt[A]): Int = a match {
          case Nil => 0
          case Cons(e, acc) => e + v1(acc)
        }
      }
      sum
    }
  }
  val foldr2 = mcata[ListFInt, Int](ms_algSum)
  println(foldr2(lst)) //9
```

### Generalized Catamorphisms
>Most more advanced recursion schemes for folding structures, such as paramorphisms and zygomorphisms can be seen in a common framework as "generalized" catamorphisms

<b>recur</b> also have the `g_cata`, you can use it via `F_W_Algebra.g_cata`, but you need write `distributive law` (it is rank-2 type signatures) and define a `Comonad`

//TODO give a sample of use it

### T-homomorphisms : for all i . ([ g1,..., gn ]) . ti = gi . Fi ([ g1,..., gn ])
Use the `constructor type-functors`, and set the recursive type (e.g. List[A]) as the Initial Algebra, so you don't need use `mu` & write a base functor (e.g. ListF[T, ?])，just use the type-functors(determine the constructors) : F1,...,Fn <br/>
(use the right part of the equation : `type List[A] = μ(ListFFunctor[A])`)

```scala
  import algebra.PFunctor, algebra.PFunctor._

  //recursive type as initial algebra
  sealed trait List[+T]
  case class Cons[T](hd: T, tl: List[T]) extends List[T]
  sealed trait Nil extends List[Nothing]
  case object Nil extends Nil

  val pf = PFunctor[List[Int]] //get base functor of the initial algebra

  //for all i . ([ g1,..., gn ]) . ti = gi . Fi ([ g1,..., gn ])
  def fold[B](g1: Unit => B, g2: (Int, B) => B)(l: List[Int]): B = l match {
    case Nil => (g1 compose ((u: Unit) => pf.term(termName[Nil.type]).map(u)(fold(g1, g2)))) ()
    case Cons(h, t) =>
      val fmap_cata = (p: Pair[Int, List[Int]]) => pf.term(termName[Cons[Int]]).map(p)(fold(g1, g2)).asInstanceOf[Pair[Int, B]]
      ((p: Pair[Int, List[Int]]) => g2(fmap_cata(p).outl, fmap_cata(p).outr)) (Pair(h, t))
  }
  val l = Cons(2, Cons(3, Cons(4, Nil)))
  val res = fold[Int](_ => 0, _ + _)(l)
  println(res) //9
```

The `fold` function body just come from the equations:
```
let h = fold(c, f) :
h nil = (g1 . F1 h) ()
h cons(a , xs) = (g2 . F2 h) (a, xs)
```
`Nil` is abstracted as `()`, and `Cons(h, t)` is abstracted as `Pair(h, t)` (which is `(h, t)`) </br>

In current version, as you can see, there are lots of boilerplate code need write

# Building recur
<b>recur</b> is built with SBT 0.13.11 or later, and its master branch is built with Scala 2.12.1 (and jdk 1.8).

# TODO List
- Add `paramorphisms` & `zygomorphisms` for F_W_Algebra
- Support Mutual Type Recursion (via initial fixed-point of product category functor)
- Add Adjoint Fixed-Point Equations (Adjoint-Folds) to unify the recursion schemes
- Use macro to reduce the boilerplate code of T-homomorphisms, so you don't need write the `fold` function, the `fold` function will come with the data type definition (in <b>recur</b> v2.0)
- Add `unfold` function just like `fold` in v2.0
- Add `hylomorphisms` (just combination of cata- & ana-)
- Add `metamorphisms` for Abstract Data Types

# References
[Algebra of programming](http://dl.acm.org/citation.cfm?id=248932)
http://citeseerx.ist.psu.edu/viewdoc/download;jsessionid=A48F549C76E5742B07A1BCCAC04DFDB9?
http://usi-pl.github.io/lc/sp-2015/doc/Bird_Wadler.%20Introduction%20to%20Functional%20Programming.1ed.pdf
http://citeseerx.ist.psu.edu/viewdoc/download;jsessionid=A48F549C76E5742B07A1BCCAC04DFDB9?doi=10.1.1.221.4281&rep=rep1&type=pdf
http://web.engr.oregonstate.edu/~erwig/papers/CategoricalADT_AMAST98.pdf
http://pdfs.semanticscholar.org/fec6/b29569eac1a340990bb07e90355efd2434ec.pdf
http://www.cs.indiana.edu/cmcs/categories.pdf
[Recursion schemes from comonads](http://dl.acm.org/citation.cfm?id=766517.766523)
https://en.wikipedia.org/wiki/Category:Recursion_schemes
https://en.wikipedia.org/wiki/Inductive_type
[Generic Programming with Adjunctions](http://www.cs.ox.ac.uk/ralf.hinze/LN.pdf)