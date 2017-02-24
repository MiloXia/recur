package algebra

import scala.language.higherKinds

object F_Algebra {
  //### F-Algebra
  //Fixed point of type constructor
  case class Fix[F[_]](f: F[Fix[F]]) //Mu or Nu
  //TODO reduce type lambda

  def mu[T, F1[_]: Functor](f: T): Fix[F1] = Fix[Lambda[a => T]](f).asInstanceOf[Fix[F1]]


  type Algebra[F[_], A] = Function[F[A], A] //a morphism from F(A) to A

  //unFix :: Fix f -> f (Fix f)
  def unFix[F[_]](fa: Fix[F]): F[Fix[F]] = fa match {
    case Fix(a) => a
  }

  //cata :: Functor f => (f a -> a) -> Fix f -> a
  //cata f = f . fmap (cata f) . outF
  def cata[F[_]: Functor, A](alg: F[A] => A): Fix[F] => A = {
    val _unFix: Fix[F] => F[Fix[F]] = unFix[F] _
    val fmap = Functor[F].map[Fix[F], A] _
    val fmap_cata_alg: F[Fix[F]] => F[A] = fff => fmap(fff)(cata(alg))
    alg compose fmap_cata_alg compose _unFix
  }

  //F-coalgebra

  //ana :: Functor f => (a -> f a) -> a -> Fix f
  def ana[F[_]: Functor, A](grow: A => F[A])(seed: A): Fix[F] = {
    val fix: F[Fix[F]] => Fix[F] = Fix.apply[F] _
    val fmap: F[A] => ((A) => Fix[F]) => F[Fix[F]] = Functor[F].map[A, Fix[F]] _
    val fmap_ana_grow: F[A] => F[Fix[F]] = f => fmap(f)(ana(grow))
    (fix compose fmap_ana_grow compose grow)(seed)
  }

  ////////////////////////////////test///////////////////////////
  def main(args: Array[String]) {
    //foldr
    trait ListF[+A, +B]
    case object Nil extends ListF[Nothing, Nothing]
    case class Cons[A, B](a: A, b: B) extends ListF[A, B]

    //an endofunctor F
    implicit def ListFFunctor[T] = new Functor[({type λ[α] = ListF[T, α]})#λ] {
      def map[A, B](fa: ListF[T, A])(f: A => B): ListF[T, B] = fa match {
        case Nil => Nil
        case Cons(a, b) => Cons(a, f(b))
      }
    }

    type ListFInt[A] = ListF[Int, A]
//    def nil = Fix[({type λ[α] = ListF[Nothing, Nothing]})#λ](Nil).asInstanceOf[Fix[ListFInt]]
//    def cons[B](a: Int, b: B) = Fix[({type λ[α] = ListF[Int, B]})#λ](Cons(a, b)).asInstanceOf[Fix[ListFInt]]
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

    //unfold
    val growListF: Int => ListFInt[Int] = {
      case 0 => Nil
      case x => Cons(x, x - 1)
    }
    val unfold = ana[ListFInt, Int](growListF) _
    println(unfold(5)) //Fix(Cons(5,Fix(Cons(4,Fix(Cons(3,Fix(Cons(2,Fix(Cons(1,Fix(Nil)))))))))))

    //Expr
    trait ExprF[+A]
    case class Const[A](i: Int) extends ExprF[A]
    case class Add[A](left: A, right: A) extends ExprF[A]
    case class Mul[A](left: A, right: A) extends ExprF[A]

    implicit val ExprFFunctor = new Functor[ExprF] { //an endofunctor F
    def map[A, B](fa: ExprF[A])(f: A => B): ExprF[B] = fa match {
        case Const(i) => Const(i)
        case Add(l, r) => Add(f(l), f(r))
        case Mul(l, r) => Mul(f(l), f(r))
      }
    }

    type Expr = Fix[ExprF]
//    def const(i: Int) = Fix[({type λ[α] = ExprF[Nothing]})#λ](Const(i)).asInstanceOf[Fix[ExprF]]
//    def mul[A](a: A, b: A) = Fix[({type λ[α] = ExprF[A]})#λ](Mul(a, b)).asInstanceOf[Fix[ExprF]]
//    def add[A](a: A, b: A) = Fix[({type λ[α] = ExprF[A]})#λ](Add(a, b)).asInstanceOf[Fix[ExprF]]

    def const(i: Int) = mu[ExprF[Nothing], ExprF](Const(i))
    def mul[A](a: A, b: A) = mu[ExprF[A], ExprF](Mul(a, b))
    def add[A](a: A, b: A) = mu[ExprF[A], ExprF](Add(a, b))

    val testExpr1 = add(const(2), mul(const(3), const(4)))

    val alg: Algebra[ExprF, Int] = {
      case Const(i) => i
      case Add(l, r) => l + r
      case Mul(l, r) => l * r
    }

    def alg2: Algebra[ExprF, String] = {
      case Const(i) => ('a'.toInt + i).toChar.toString
      case Add(l, r) => l + r
      case Mul(l, r) => (l zip r).map(t => s"${t._1}${t._2}").mkString
    }

    val eval = cata(alg)
    println(eval(testExpr1)) //14

    val eval2 = cata(alg2)
    println(eval2(testExpr1)) //cde

  }
}
