package algebra

/*
* MendlerAlgebra is ues rank-2 polymorphism, you can use it with shapeless poly functions
* Scala rank-2 is so sad (＞﹏＜)
*/

object Mendler_Style {
  /*
  * removes the dependency on the functor F
  * Algebra (CoYoneda f) a = MendlerAlgebra f a
  * CoYoneda f = free functor
  */
  import F_Algebra.{Fix => Mu}

  //type MendlerAlgebra f c = forall a. (a -> c) -> f a -> c
  type MendlerAlgebra[F[_], C] = Id ~>> C => F ~>> C


  // mcata :: MendlerAlgebra f c -> Mu f -> c
  // mcata phi = phi (mcata phi) . outF

  def mcata[F[_], C](phi: MendlerAlgebra[F, C]): Mu[F] => C = {
    val outF: Mu[F] => F[Mu[F]] = F_Algebra.unFix[F] _
    //rank-2 outF
    val outF_rank2 = new (Lambda[a => Mu[F]] ~> Lambda[a => F[Mu[F]]]) {
      override def apply[A](a: Lambda[a => Mu[F]][A]): Lambda[a => F[Mu[F]]][A] = outF(a)
    }

    val id2c = new (Id ~>> C) {
      override def apply[A](a: A): C = {
        val mf2c: Mu[F] => C = (mf: Mu[F]) => mcata(phi)(mf)
        mf2c(a.asInstanceOf[Mu[F]]) //TODO rm cast , isn't safe
      }
    }

    val mcata_rank2 = new (Lambda[a => Mu[F]] ~>> C) {
      override def apply[A](a: Lambda[a => Mu[F]][A]): C = {
        val r: F ~>> C = phi(id2c)
        r(outF_rank2(a) : F[Mu[F]])
      }
    }
    //rank-2 to function
    val f: Mu[F] => C = (muF: Mu[F]) => mcata_rank2(muF)
    f
  }

  // cata :: Functor f => Algebra f c -> Mu f -> c
  // cata phi = mcata (\f -> phi . fmap f)

}
