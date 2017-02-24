package algebra

trait Comonad[N[_]] extends Functor[N] {
  def extract[A](n: N[A]): A
  def duplicate[A](n: N[A]): N[N[A]]

  def counit[A](n: N[A]) = extract(n)
}

object Comonad {
  def apply[N[_]: Comonad] = implicitly[Comonad[N]]
}

trait DistComonad[F[_], N[_]] {
  def dist[A](fna: F[N[A]])(implicit f: Functor[F], n: Comonad[N]): N[F[A]]
}