import scala.reflect.macros.blackbox.Context

import scala.language.experimental.macros

object Macros {
  def hello: Unit = macro impl

  def impl(c: Context) = {
    import c.universe._

    c.Expr[Unit](q"""println("Hello World")""")
  }

}