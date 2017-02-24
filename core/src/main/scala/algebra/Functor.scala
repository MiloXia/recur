package algebra

import shapeless.labelled.FieldType

import scala.language.higherKinds

import shapeless._
import shapeless.ops.coproduct.IsCCons
import shapeless.ops.hlist.IsHCons
import shapeless.syntax.singleton._
import shapeless.record._

trait Functor[F[_]] {
  def map[A, B](fa: F[A])(f: A => B): F[B]
}
object Functor {
  def apply[F[_]: Functor] = implicitly[Functor[F]]
}

trait TypeFunctor[F[_]] extends Functor[F] {
  def pure[A](a: A): F[A] //for debug & test
  override def toString: String = "type-functor"
}


//polynomial functor
trait PFunctor[T] {
  type F[_]
  def isPrimitive_? = false
  def functor: TypeFunctor[F] //F is a functor

  //constructor type-functors
  type Components <: HList
  def typeFunctors: Components
  //TODO get type of Components to manipulate HList
  def typeFunctorList: List[TypeFunctor[Any]] = Nil
  def term: Map[String, TypeFunctor[Any]] = Map.empty
}

/**
  * see: https://zhuanlan.zhihu.com/p/24992042
  */

object PFunctor {
  type Aux[T, H[_]] = PFunctor[T] {type F[A] = H[A]}
  def apply[A](implicit pf: PFunctor[A]): PFunctor[A] = pf

  //identify functor
  type Id[A] = A
  val idFunctor: TypeFunctor[Id] = new TypeFunctor[Id] {
    def pure[A](a: A): Id[A] = a
    def map[A, B](fa: Id[A])(f: (A) => B): Id[B] = f(fa)
    override def toString = "I"
  }
  //constant functor
  type Const[A, B] = A
  def const[A, B](a: A, b: B): Const[A, B] = a

  def constFunctor[T](default: T, tg: String = "[None]") =
    new TypeFunctor[({type λ[α] = Const[T, α]})#λ] {
      def pure[A](a: A): Const[T, A] = default
      def map[A, B](fa: Const[T, A])(f: (A) => B): Const[T, B] = fa
      override def toString = s"($tg <<)"
    }

  //product
  case class Pair[A, B](a: A, b: B) {
    def outl = a
    def outr = b
    def curry = (x: A) => b
  }

  def mulFunctor[F[_]: TypeFunctor, G[_]: TypeFunctor] =
    new TypeFunctor[({type λ[α] = Pair[F[α], G[α]]})#λ] {
      val (f1, f2) = (implicitly[TypeFunctor[F]], implicitly[TypeFunctor[G]])
      def pure[A](a: A): Pair[F[A], G[A]] = Pair(f1.pure(a), f2.pure(a))

      def map[A, B](pa: Pair[F[A], G[A]])(f: (A) => B): Pair[F[B], G[B]] = {
        // f x g = <f . outl, g . outr>
        // Ff x Gf = <Ff . outl, Gf . outr> = <(map f) . outl, (map f) . outr>
        Pair(f1.map(pa.outl)(f), f2.map(pa.outr)(f))
      }
      override def toString = s"$f1 x $f2"
    }

  //coproduct
  sealed trait DSum[A, B]
  case class Inl[A, B](a: A) extends DSum[A, B]
  case class Inr[A, B](b: B) extends DSum[A, B]

  def sumFunctor[F[_]: TypeFunctor, G[_]: TypeFunctor] =
    new TypeFunctor[({type λ[α] = DSum[F[α], G[α]]})#λ] {
      val (f1, f2) = (implicitly[TypeFunctor[F]], implicitly[TypeFunctor[G]])

      def pure[A](a: A): DSum[F[A], G[A]] = Inr[F[A], G[A]](f2.pure(a)) // ???

      def map[A, B](fa: DSum[F[A], G[A]])(f: (A) => B): DSum[F[B], G[B]] = {
        // f + g = [inl . f, inr . g]
        // [f, g](inl a) = f a & [f, g](inr b) = g b
        fa match {
          case Inl(a) => Inl(f1.map(a)(f))
          case Inr(b) => Inr(f2.map(b)(f))
        }
      }
      override def toString = s"$f1 + $f2"
    }

  //to repr

  //or use (implicit tg: scala.reflect.runtime.universe.TypeTag[T])
  def pFunctorOfConst[T](default: T, tg: String = "[None]"): PFunctor[T] = new PFunctor[T] {
    type F[A] = Const[T, A]
    override def functor = constFunctor[T](default, tg)
    override def isPrimitive_? = true

    type Components = HNil
    def typeFunctors = HNil
  }

  implicit val intFunctor = pFunctorOfConst(0, "Int")
  implicit val charFunctor = pFunctorOfConst(' ', "Char")
  implicit val floatFunctor = pFunctorOfConst(0f, "Float")
  implicit val unitFunctor = pFunctorOfConst((), "1")

  //HList - product
  implicit val hnilFunctor: PFunctor[HNil] = new PFunctor[HNil] {
    type F[A] = Const[Unit, A]
    override def functor = constFunctor[Unit]((), "1") //HNil iso ()
    override def isPrimitive_? = true

    type Components = TypeFunctor[F] :: HNil
    def typeFunctors = functor :: HNil

    override def typeFunctorList = functor.asInstanceOf[TypeFunctor[Any]] :: Nil
  }
  //for H :: HNil
  implicit def hlistFunctor[H](
    implicit
    hPFunctor: Lazy[PFunctor[H]],
    tPFunctor: PFunctor[HNil]
  ): PFunctor[H :: HNil] =
    if(!hPFunctor.value.isPrimitive_?) {
      new PFunctor[H :: HNil] {
        type F[A] = Id[A]
        override def isPrimitive_? = true
        override def functor = idFunctor

        type Components = TypeFunctor[F] :: HNil
        def typeFunctors = functor :: HNil
      }
    } else {
      new PFunctor[H :: HNil] {
        type F[A] = hPFunctor.value.F[A]
        override def isPrimitive_? = true
        override def functor = hPFunctor.value.functor

        type Components = TypeFunctor[F] :: HNil
        def typeFunctors = functor :: HNil

        override def typeFunctorList = functor.asInstanceOf[TypeFunctor[Any]] :: Nil
      }
    }
  //for H :: T ^ T = Head :: Tail
  implicit def hlistFunctor2[H, T <: HList, Head, Tail <: HList](
    implicit
    hPFunctor: Lazy[PFunctor[H]],
    tPFunctor: PFunctor[T],
    isHCons: IsHCons.Aux[T, Head, Tail]
  ): PFunctor[H :: T] =
    if(!hPFunctor.value.isPrimitive_?) {
      new PFunctor[H :: T] {
        type P[A] = Id[A]
        type G[A] = tPFunctor.F[A]
        type F[A] = Pair[P[A], G[A]]

        override def isPrimitive_? = false

        override def functor: TypeFunctor[({type λ[α] = Pair[P[α], G[α]]})#λ] =
          mulFunctor[P, G](idFunctor, tPFunctor.functor)

        type Components = TypeFunctor[F] :: HNil
        def typeFunctors = functor :: HNil

        override def typeFunctorList = functor.asInstanceOf[TypeFunctor[Any]] :: Nil
      }
    } else {
      new PFunctor[H :: T] {
        type P[A] = hPFunctor.value.F[A]
        type G[A] = tPFunctor.F[A]
        type F[A] = Pair[P[A], G[A]]

        override def isPrimitive_? = false

        override def functor: TypeFunctor[({type λ[α] = Pair[P[α], G[α]]})#λ] =
          mulFunctor[P, G](hPFunctor.value.functor, tPFunctor.functor)

        type Components = TypeFunctor[F] :: HNil
        def typeFunctors = functor :: HNil

        override def typeFunctorList = functor.asInstanceOf[TypeFunctor[Any]] :: Nil
      }
    }

  //bridge
  implicit def genericPFunctor[A, R](
    implicit
    gen: Generic.Aux[A, R],
    pf: Lazy[PFunctor[R]] //e.g for all Int :: String :: HNil => (Int <<) x (String <<)
  ): PFunctor[A] =
    new PFunctor[A] {
      type F[X] = pf.value.F[X]
      override def isPrimitive_? = pf.value.isPrimitive_?
      override def functor = pf.value.functor

      type Components = pf.value.Components
      def typeFunctors = pf.value.typeFunctors

      override def typeFunctorList = pf.value.typeFunctorList
      override def term = pf.value.term
    }

  //coproduct
  implicit val cnilPFunctor = new PFunctor[CNil] {
    override def functor = throw new Exception("error")

    type Components = HNil
    def typeFunctors = HNil
  }

  implicit def coproductPFunctor[H, T <: Coproduct](
    implicit
    hPFunctor: Lazy[PFunctor[H]],
    tPFunctor: PFunctor[T],
    tg: scala.reflect.runtime.universe.TypeTag[H]
  ): PFunctor[H :+: CNil] =
    new PFunctor[H :+: CNil] {
      type F[A] = hPFunctor.value.F[A]
      def functor = hPFunctor.value.functor
      override def isPrimitive_? = true

      type Components = TypeFunctor[F] :: HNil
      def typeFunctors = hPFunctor.value.functor :: HNil

      override def typeFunctorList = hPFunctor.value.functor.asInstanceOf[TypeFunctor[Any]] :: Nil
      override def term = Map(tg.tpe.toString -> typeFunctorList.head)
    }

  implicit def coproductPFunctor2[H, T <: Coproduct, Head, Tail <: Coproduct](
    implicit
    hPFunctor: Lazy[PFunctor[H]],
    tPFunctor: PFunctor[T],
    isCCons: IsCCons.Aux[T, Head, Tail],
    tg: scala.reflect.runtime.universe.TypeTag[H]
  ): PFunctor[H :+: T] =
    new PFunctor[H :+: T] {
      type P[A] = hPFunctor.value.F[A]
      type G[A] = tPFunctor.F[A]
      type F[A] = DSum[P[A], G[A]]
      def functor = sumFunctor[P, G](hPFunctor.value.functor, tPFunctor.functor)
      override def isPrimitive_? = false

      type Components = TypeFunctor[P] :: tPFunctor.Components
      def typeFunctors = hPFunctor.value.functor :: tPFunctor.typeFunctors

      override def typeFunctorList = hPFunctor.value.functor.asInstanceOf[TypeFunctor[Any]] :: tPFunctor.typeFunctorList
      override def term = Map(tg.tpe.toString -> typeFunctorList.head) ++ tPFunctor.term
    }

  def termName[T](implicit tg: scala.reflect.runtime.universe.TypeTag[T]) = tg.tpe.toString
}