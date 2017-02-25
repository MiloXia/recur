
object Test {
  def main(args: Array[String]) {
    Macros.hello
  }
}

object PolyFunctor extends App {
  import algebra.PFunctor, algebra.PFunctor._

  //test type-functor
  val r = idFunctor.map(1)(a => a + 1)
  println(r)

  val r2 = constFunctor(1).map(1)((a : Int) => a + 1)
  println(r2)

  val r22 = constFunctor(1).map(constFunctor(1).pure(2))((a : Int) => a + 1)
  println(r22)

  implicit val idF = idFunctor
  implicit val constIntF = constFunctor(1)
  val Id_x_Int_<< = mulFunctor[Id, ({type λ[α] = Const[Int, α]})#λ]
  val r3 = Id_x_Int_<<.map(PFunctor.Pair(1, 1))(a => a + 1)
  println(r3)

  val Id_sum_Int_<< = sumFunctor[Id, ({type λ[α] = Const[Int, α]})#λ]
  val r4 = Id_sum_Int_<<.map(Inl(1))(a => a + 1)
  val r5 = Id_sum_Int_<<.map(Inr[Int, Int](1))(a => a + 1)
  println(r4, r5)

  //ADT
  case class AX()
  case class AXX(a: Int)
  case class AXXX(a: Int, b: Char)

  sealed trait Bool
  case class True() extends Bool
  case class False() extends Bool

  val pf1 = PFunctor[AX]
  println(pf1.functor.map(().asInstanceOf[pf1.F[Unit]])(a => a))
  println(pf1.functor.map(pf1.functor.pure(1))(a => a + 1))
  val pf2 = PFunctor[AXX]
  println(pf2.functor.map(1.asInstanceOf[pf2.F[Int]])(a => a + 1))
  println(pf2.functor.map(pf2.functor.pure("1"))(a => a + 1))

  val pf3 = PFunctor[AXXX]
  println(pf1.isPrimitive_?, pf2.isPrimitive_?, pf3.isPrimitive_?)

  val pf4 = PFunctor[Bool]

  println(pf1.functor, pf2.functor, pf3.functor, pf4.functor)
  println(pf1.typeFunctors, pf2.typeFunctors, pf3.typeFunctors, pf4.typeFunctors)

  //test Nat
  sealed trait Nat
  case class Zero() extends Nat
  case class Succ(n: Nat) extends Nat

  val pf5 = PFunctor[Nat]
  println(pf5.isPrimitive_?, pf5.functor, pf5.typeFunctors)
  println(pf5.functor.map(pf5.functor.pure(1))(a => a + 1))

  //test list
  sealed trait List[+T]
  case class Cons[T](hd: T, tl: List[T]) extends List[T]
  sealed trait Nil extends List[Nothing]
  case object Nil extends Nil

  val pf6 = PFunctor[List[Int]]
  println(pf6.isPrimitive_?, pf6.functor, pf6.typeFunctors, pf6.typeFunctorList, pf6.term)
  //test Expr
  sealed trait Expr
  case class AConst(i: Int) extends Expr
  case class Add(expr1: Expr, expr2: Expr) extends Expr
  case class Mul(expr1: Expr, expr2: Expr) extends Expr

  val pf7 = PFunctor[Expr]
  println(pf7.isPrimitive_?, pf7.functor, pf7.typeFunctors, pf7.typeFunctorList, pf7.term)
  val rx = pf7.typeFunctors
//  println(pf7.typeFunctors.head)

  println(termName[Mul], termName[Nil.type])

  //for all i . ([ g1,..., gn ]) . ti = gi . Fi ([ g1,..., gn ])

  def fold[B](g1: Unit => B, g2: (Int, B) => B)(l: List[Int]): B = l match {
    case Nil => (g1 compose ((u: Unit) => pf6.term(termName[Nil.type]).map(u)(fold(g1, g2)))) ()
    case Cons(h, t) =>
      val fmap_cata = (p: Pair[Int, List[Int]]) => pf6.term(termName[Cons[Int]]).map(p)(fold(g1, g2)).asInstanceOf[Pair[Int, B]]
      ((p: Pair[Int, List[Int]]) => g2(fmap_cata(p).outl, fmap_cata(p).outr)) (Pair(h, t))
  }
  val l = Cons(1, Cons(2, Cons(3, Nil)))
  val rr = fold[Int](_ => 0, _ + _)(l)
  println(rr)
}

object Test_Initial_Fixed_Point extends App {
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

  //test Mendler_Style
  import algebra.~>>
  import algebra.Mendler_Style.{mcata, MendlerAlgebra}

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
}

object Test_T_homomorphisms extends App {
  import algebra.PFunctor, algebra.PFunctor._

  sealed trait List[+T]
  case class Cons[T](hd: T, tl: List[T]) extends List[T]
  sealed trait Nil extends List[Nothing]
  case object Nil extends Nil

  val pf = PFunctor[List[Int]]

  def fold[B](g1: Unit => B, g2: (Int, B) => B)(l: List[Int]): B = l match {
    case Nil => (g1 compose ((u: Unit) => pf.term(termName[Nil.type]).map(u)(fold(g1, g2)))) ()
    case Cons(h, t) =>
      val fmap_cata = (p: Pair[Int, List[Int]]) => pf.term(termName[Cons[Int]]).map(p)(fold(g1, g2)).asInstanceOf[Pair[Int, B]]
      ((p: Pair[Int, List[Int]]) => g2(fmap_cata(p).outl, fmap_cata(p).outr)) (Pair(h, t))
  }
  val l = Cons(2, Cons(3, Cons(4, Nil)))
  val res = fold[Int](_ => 0, _ + _)(l)
  println(res) //9
}