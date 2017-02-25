package algebra

trait Adjunction[F[_],G[_]] {
  def left[A,B](f: F[A] => B): A => G[B]
  def right[A,B](f: A => G[B]): F[A] => B
}
