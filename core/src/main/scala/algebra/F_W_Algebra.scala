package algebra

/**
  * Generalized Catamorphisms
  * A generalized catamorphism is defined in terms of an F-W-algebra and a distributive law
  * for the comonad W over the functor F which preserves the structure of the comonad W.
  */
object F_W_Algebra {
  import F_Algebra.{Fix => Mu}

  //F-W-algebra
  type FWAlgebra[F[_], N[_], A] = F[N[A]] => A

  //distributive law
  //type Dist f w = forall a. f (w a) -> w (f a)
  type Dist[F[_], N[_]] = Lambda[a => F[N[a]]] ~> Lambda[a => N[F[a]]]

  // g_cata :: (Functor f, Comonad w) => Dist f w -> FWAlgebra f w a -> Mu f -> a
  // g_cata k g = extract . c
  // where c = liftW g . k . fmap (duplicate . c) . outF

  // or ([ phi ])F-N = epsilon . ([ phi++ ])F (definition 35)
  // g_cata dist phi = extract . cata (fmap phi . dist . fmap duplicate)

  def g_cata[F[_]: Functor, N[_]: Comonad, A](dist: Dist[F, N], phi: FWAlgebra[F, N, A]): Mu[F] => A = {
    def fmap[A1, B] = Functor[F].map[A1, B] _
    def fmap2[A1, B] = Comonad[N].map[A1, B] _
    val extract = Comonad[N].extract[A] _
    val duplicate = Comonad[N].duplicate[A] _
    val fmap_dupl: F[N[A]] => F[N[N[A]]] = (fna: F[N[A]]) => fmap[N[A], N[N[A]]](fna)(duplicate)
    val fmap_phi: N[F[N[A]]] => N[A] = (nfna: N[F[N[A]]]) => fmap2[F[N[A]], A](nfna)(phi)
    //dist is rank-2 function can't use pointfree style
    val fmap_phi_dot_dist_dot_fmap_dupl: F[N[A]] => N[A] = (fna: F[N[A]]) => fmap_phi(dist(fmap_dupl(fna)))

    extract compose F_Algebra.cata(fmap_phi_dot_dist_dot_fmap_dupl)
  }

  def g_cata[F[_]: Functor, N[_]: Comonad, A](phi: FWAlgebra[F, N, A])(implicit DC: DistComonad[F, N]): Mu[F] => A = {
    def _dist[A1](fna: F[N[A1]]) = DC.dist[A1](fna)(Functor[F], Comonad[N])
    def fmap[A1, B] = Functor[F].map[A1, B] _
    def fmap2[A1, B] = Comonad[N].map[A1, B] _
    val outF: Mu[F] => F[Mu[F]] = F_Algebra.unFix[F] _
    val In: F[Mu[F]] => Mu[F] = fmf => Mu(fmf).asInstanceOf[Mu[F]]
    val fmap_In: N[F[Mu[F]]] => N[Mu[F]] = (nfmn: N[F[Mu[F]]]) => fmap2[F[Mu[F]], Mu[F]](nfmn)(In)
    val fmap_In_dot_dist: F[N[Mu[F]]] => N[Mu[F]] = fmap_In compose _dist
    val iota: Mu[F] => N[Mu[F]] = F_Algebra.cata(fmap_In_dot_dist)
    val fmap_gcata_phi: N[Mu[F]] => N[A] = nmf => fmap2[Mu[F], A](nmf)(g_cata(phi))
    val fmap_fgp: F[Mu[F]] => F[N[A]] = fmf => fmap[Mu[F], N[A]](fmf)(fmap_gcata_phi compose iota)
    phi compose fmap_fgp compose outF
  }

  //Prod Comonad
  type Prod[E, C] = Pair[C, E]
  def outl[E, C]: Prod[E, C] => C = prod => prod.outl
  def outr[E, C]: Prod[E, C] => E = prod => prod.outr

  def fork[A, C, E](g1: A => C)(g2: A => E)(z: A): Prod[E, C] = Pair(g1(z), g2(z))

  implicit def prodComonad[E]: Comonad[Prod[E, ?]] = new Comonad[Prod[E, ?]] {
    def map[A, B](fa: Prod[E, A])(f: (A) => B): Prod[E, B] = fork[Prod[E, A], B, E](f compose outl)(outr)(fa)

    def extract[A](n: Prod[E, A]): A = outl(n)
    def duplicate[A](n: Prod[E, A]): Prod[E, Prod[E, A]] = fork[Prod[E, A], Prod[E, A], E](identity)(outr)(n)
  }

  //TODO zygo & para

  // zygo :: Functor f => (f e -> e) -> (f (Prod e c) -> c) -> Mu f -> c
  // zygo chi = gcata (fork (fmap outl) (chi . fmap outr))

  // para :: Functor f => (f (Prod (Mu f) c) -> c) -> Mu f -> c
  // para = zygo In

  //test para
  // fact :: Nat -> Nat
  // fact = para phi
  //   where phi zero = succ zero
  //         phi (succ(Pair f n)) = mult f (succ n)

}

