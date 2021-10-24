package fos

import scala.util.parsing.input.Positional

/** Abstract Syntax Trees for terms. */
sealed abstract class Term extends Positional
case class Var(name: String) extends Term
case class Abs(v: String, t: Term) extends Term
case class App(t1: Term, t2: Term) extends Term
