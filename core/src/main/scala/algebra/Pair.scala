package algebra

case class Pair[A, B](a: A, b: B) {
  def outl = a
  def outr = b
}
