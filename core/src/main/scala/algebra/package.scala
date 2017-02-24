
package object algebra {
  trait ~>[F[_], G[_]] { //nt
    def apply[A](a: F[A]): G[A]
  }

  trait Forall[F[_], G[_]] extends ~>[F, G]

  //rank-2
  type Id[A] = A

  type Const[C] = {
    type λ[T] = C
  }

  type ~>>[F[_], R] = ~>[F, Const[R]#λ]
}
